#!/bin/sh

# in all lines that start with "code", unescape all underscores
# (zotero's better bibtex escapes them because the "code" field is not an url field)
UNESCAPE_IN_CODE_FIELD='/^ *code/s/\\_/_/g'

sed -i -e "$UNESCAPE_IN_CODE_FIELD" publications.bib
sed -i -e "$UNESCAPE_IN_CODE_FIELD" reports.bib

OPTIONS="-d -r -revkeys -nodoc -nofooter -nokeywords -noabstract -nobiblinks -nobibsource -linebreak -nf code code -nf url PDF"

bibtex2html $OPTIONS -o ../publications publications.bib
bibtex2html $OPTIONS -o ../reports reports.bib
