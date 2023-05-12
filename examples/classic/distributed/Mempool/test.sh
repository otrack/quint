#!/bin/sh

# echo "
# moveHeightOnce
# " | quint -r Mempool.qnt::MempoolTests

quint run --main MempoolTests --invariant validInv Mempool.qnt 


