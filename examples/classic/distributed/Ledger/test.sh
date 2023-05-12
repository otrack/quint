#!/bin/sh

echo "
submitTwiceError
commitNonSubmittedError
commitSubmittedSuccess
" | quint -r Ledger.qnt::LedgerTests

quint run --main LedgerTests --invariant invariant Ledger.qnt 


