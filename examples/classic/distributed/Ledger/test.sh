#!/bin/sh

# echo "
# proposeTwiceError
# decideNonProposedError
# decideProposedSuccess
# " | quint -r Ledger.qnt::ConsensusTests

echo "
submitTwiceError
commitNonProposedError
decideProposedSuccess
" | quint -r Ledger.qnt::LedgerTests


# quint run --verbosity 5 --main Consensus --step stepConsensus --init initConsensus Ledger.qnt


