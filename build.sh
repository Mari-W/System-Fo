#!/bin/bash

marp slides.md --html --pdf
latexmk -pdf -halt-on-error thesis.tex