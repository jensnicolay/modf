#!/bin/bash

rsync --verbose --recursive --times --perms --delete \
  --exclude "*.sh" --exclude ".project" --exclude ".svn" \
  ./* $1.vub.ac.be:modf