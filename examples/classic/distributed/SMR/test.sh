#!/bin/sh

echo "\
proposeTwiceError
proposeDecideNonProposedError" | quint -r SMR.qnt::Consensus

quint run --verbosity 5 --main Consensus --step stepConsensus --init initConsensus SMR.qnt


