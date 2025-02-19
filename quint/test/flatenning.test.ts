import { assert } from 'chai'
import { describe, it } from 'mocha'
import { collectDefinitions } from '../src/definitionsCollector'
import { scanConflicts } from '../src/definitionsScanner'
import { flatten } from '../src/flattening'
import { newIdGenerator } from '../src/idGenerator'
import { resolveImports } from '../src/importResolver'
import { definitionToString } from '../src/IRprinting'
import { resolveNames } from '../src/nameResolver'
import { quintErrorToString } from '../src/quintError'
import { treeFromModule } from '../src/scoping'
import { collectIds } from './util'
import JSONbig from 'json-bigint'
import { parsePhase1fromText } from '../src/quintParserFrontend'
import { toScheme } from '../src/types/base'

describe('flatten', () => {
  function assertFlatennedDefs(baseDefs: string[], defs: string[], expectedDefs: string[]): void {
    const idGenerator = newIdGenerator()

    const quintModules: string = `module A { ${baseDefs.join('\n')} } module wrapper { ${defs.join('\n')} }`

    const result = parsePhase1fromText(idGenerator, quintModules, 'mocked_path')
    if (result.isLeft()) {
      assert.fail(`Couldn't parse mocked expression. Result - ${JSONbig.stringify(result)}`)
    }

    // Module A is a module called A containing `baseDefs`. The main module can import or instance it.
    const moduleA = result.value.modules[0]
    const tableA = collectDefinitions(moduleA)
    const lookupTableA = resolveNames(moduleA, tableA, treeFromModule(moduleA)).unwrap()

    // This is the main module containing `defs`. It can import or instance module A.
    const module = result.value.modules[1]
    const table = collectDefinitions(module)
    const [errors, tableWithImports] = resolveImports(module, new Map([
      ['A', tableA],
      ['wrapper', table],
    ]))

    assert.isEmpty(errors, `Should find no errors, found: ${[...errors.values()].map(quintErrorToString)}`)

    const lookupTable = new Map([
      ...lookupTableA.entries(),
      ...resolveNames(module, tableWithImports, treeFromModule(module)).unwrap().entries(),
    ])

    const originalIds = [...result.value.sourceMap.keys()]
    const typesMap = new Map(originalIds.map(i => [i, toScheme({ kind: 'int' })]))

    const flattenedModule = flatten(module, lookupTable, new Map([
      ['A', moduleA],
      ['wrapper', module],
    ]), idGenerator, result.value.sourceMap, typesMap)

    it('flattens instances', () => {
      assert.sameDeepMembers(flattenedModule.defs.map(def => definitionToString(def)), expectedDefs)
    })

    it('does not repeat ids', () => {
      const ids = collectIds(flattenedModule)
      assert.notDeepInclude(collectIds(moduleA), ids)
      assert.sameDeepMembers(ids, [...new Set(ids)])
    })

    it('does not have conflicting definitions', () => {
      assert.isTrue(scanConflicts(table, treeFromModule(module)).isRight())
    })

    it('adds new entries to the source map', () => {
      const sourceMap = result.value.sourceMap
      assert.includeDeepMembers([...sourceMap.keys()], flattenedModule.defs.map(def => def.id))
    })

    it('adds new entries to the types map', () => {
      assert.includeDeepMembers([...typesMap.keys()], flattenedModule.defs.map(def => def.id))
    })
  }

  describe('multiple instances', () => {
    const baseDefs = [
      'const N: int',
      'val x = N + 1',
    ]

    const defs = [
      'import A(N = 1) as A1',
      'import A(N = 2) as A2',
    ]

    const expectedDefs = [
      'pure val A1::N: int = 1',
      'val A1::x = iadd(A1::N, 1)',
      'pure val A2::N: int = 2',
      'val A2::x = iadd(A2::N, 1)',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })

  describe('single instance with several definitions', () => {
    const baseDefs = [
      'const N: int',
      'var x: int',
      'pure def f(a) = a + 1',
      `action V = x' = f(x)`,
      'assume T = N > 0',
      'def lam = val b = 1 { a => b + a }',
      'def lam2 = val b = 1 { a => b + a }',

    ]

    const defs = [
      'import A(N = 1) as A1',
    ]

    const expectedDefs = [
      'pure val A1::N: int = 1',
      'var A1::x: int',
      'pure def A1::f = (A1::a => iadd(A1::a, 1))',
      `action A1::V = assign(A1::x, A1::f(A1::x))`,
      'assume A1::T = igt(A1::N, 0)',
      'def A1::lam = val A1::b = 1 { (A1::a => iadd(A1::b, A1::a)) }',
      'def A1::lam2 = val A1::b = 1 { (A1::a => iadd(A1::b, A1::a)) }',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })

  describe('imports', () => {
    const baseDefs = [
      'val f(x) = x + 1',
    ]

    const defs = [
      'import A.*',
    ]

    const expectedDefs = [
      'val f = (x => iadd(x, 1))',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })

  describe('export with previous import', () => {
    const baseDefs = [
      'val f(x) = x + 1',
    ]

    const defs = [
      'import A.*',
      'export A.*',
    ]

    const expectedDefs = [
      'val f = (x => iadd(x, 1))',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })

  describe('export without previous import', () => {
    const baseDefs = [
      'val f(x) = x + 1',
    ]

    const defs = [
      'export A.*',
    ]

    const expectedDefs = [
      'val f = (x => iadd(x, 1))',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })

  describe('export instance', () => {
    const baseDefs = [
      'const N: int',
      'val x = N + 1',
    ]

    const defs = [
      'import A(N = 1) as A1',
      'export A1.*',
    ]

    const expectedDefs = [
      // Namespaced defs, from the instance statement
      'pure val A1::N: int = 1',
      'val A1::x = iadd(A1::N, 1)',
      // Exported defs, without namespace
      'pure val N: int = 1',
      'val x = iadd(N, 1)',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })

  describe('export instance with qualifier', () => {
    const baseDefs = [
      'const N: int',
      'val x = N + 1',
    ]

    const defs = [
      'val myN = 1',
      'import A(N = myN) as A1',
      'export A1 as B',
    ]

    const expectedDefs = [
      'val myN = 1',
      // Namespaced defs, from the instance statement
      'pure val A1::N: int = myN',
      'val A1::x = iadd(A1::N, 1)',
      // Exported defs, with namespace B
      'pure val B::N: int = myN',
      'val B::x = iadd(B::N, 1)',
    ]

    assertFlatennedDefs(baseDefs, defs, expectedDefs)
  })
})
