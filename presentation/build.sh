for file in ../proofs/*.agda; do
  python3 latex.py $file
done
for file in *.lagda; do
  /home/mari/.cabal/bin/agda --latex $file --latex-dir .
done
latexmk -pdf -halt-on-error -shell-escape presentation.tex