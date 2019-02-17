#!/bin/sh

OPTIONS="-d -r -revkeys -nodoc -nofooter -nokeywords -noabstract -linebreak -nf url pdf"

bibtex2html $OPTIONS -o ../publications publications.bib
bibtex2html $OPTIONS -o ../reports reports.bib
