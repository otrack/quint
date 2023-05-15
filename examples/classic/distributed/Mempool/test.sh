#!/bin/sh

echo "moveHeightOnce" | quint -r Mempool.qnt::MempoolTests

quint run --verbosity 3 --main MempoolTests --invariant allInv Mempool.qnt 


