#!/bin/sh

echo "\
proposeTwiceError
proposeDecideNonProposedError" | quint -r All.qnt::Consensus

quint run --verbosity 5 --main Consensus --step stepConsensus --init initConsensus All.qnt


