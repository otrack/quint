#!/bin/sh

# echo "
# proposeTwiceError
# decideNonProposedError
# decideProposedSuccess
# " | quint -r Consensus.qnt::ConsensusTests

# quint run --main ConsensusTests --invariant invariant Consensus.qnt 

# echo "
# submitTwiceError
# commitNonSubmittedError
# commitSubmittedSuccess
# " | quint -r Ledger.qnt::LedgerTests

quint run --main LedgerTests --invariant invariant Ledger.qnt 


