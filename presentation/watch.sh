#!/bin/bash
inotifywait -q -m -e close_write ../proofs/*.agda |
  while read -r filename event; do
    python3 latex.py $filename
  done &
inotifywait -q -m -e close_write *.lagda |
  while read -r filename event; do
    ~/.cabal/bin/agda --latex $filename --latex-dir .
  done &
xdg-open presentation.pdf
latexmk -pvc -pdf -shell-escape presentation.tex
pkill inotify