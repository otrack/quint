/* ----------------------------------------------------------------------------------
 * Copyright (c) Informal Systems 2023. All rights reserved.
 * Licensed under the Apache 2.0.
 * See License.txt in the project root for license information.
 * --------------------------------------------------------------------------------- */

/**
 * Assembling of documentation strings collected from the Quint IR,
 * previously parsed from documentation comments starting with ///
 *
 * @author Gabriela Moreira
 *
 * @module
 */

import { compact } from 'lodash'
import { definitionToString } from './IRprinting'
import { QuintModule } from './quintIr'

/**
 * A documentation entry for a definition, compatible with LSP responses for signature help
 */
export interface DocumentationEntry {
  /* The mode and type signature of the definition */
  label: string;
  /* The documentation string in markdown for the definition, if present */
  documentation?: string;
}

/**
 * Produces a documentation map for the modules' definitions
 *
 * @param quintModule the module for which documentation should be produced
 * @returns a map of definition names to their documentation
 */
export function produceDocs(quintModule: QuintModule): Map<string, DocumentationEntry> {
  const entries = quintModule.defs.map((def) => {
    if (def.kind === 'instance' || def.kind === 'import' || def.kind === 'export') {
      return undefined
    }

    const entry: [string, DocumentationEntry] = [def.name, {
      label: definitionToString(def, false),
      documentation: def.doc,
    }]

    return entry
  })

  return new Map<string, DocumentationEntry>(compact(entries))
}

/**
 * Produces a documentation map for the modules' definitions
 *
 * @param quintModule the module for which documentation should be produced
 * @returns a map of definition ids to their documentation
 */
export function produceDocsById(quintModule: QuintModule): Map<bigint, DocumentationEntry> {
  const entries = quintModule.defs.map((def) => {
    if (def.kind === 'instance' || def.kind === 'import' || def.kind === 'export') {
      return undefined
    }

    const entry: [bigint, DocumentationEntry] = [def.id, {
      label: definitionToString(def, false),
      documentation: def.doc,
    }]

    return entry
  })

  return new Map(compact(entries))
}

/**
 * Formats a documentation entry to Markdown
 *
 * @param entry the documentation entry to be formatted
 * @returns a string with the entry's label as header and documentation as body
 */
export function toMarkdown(entry: DocumentationEntry): string {
  return `## \`${entry.label}\`\n\n${entry.documentation || ''}`
}
