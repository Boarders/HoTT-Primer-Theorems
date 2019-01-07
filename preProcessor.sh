#!/bin/bash

  file=$2
  output=$3
  sed -e 's/¬/Not/g' "${file}" > $3
