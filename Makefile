default_target: all

.PHONY: clean

VS := $(shell find . -type f -name '*.v')
VOS := $(patsubst %.v,%.vo,$(VS))
VHTMLS := $(patsubst %.v,%.v.html,$(VS))

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $*.v

%.v.html: %.vo %.v
	$(COQDOC) --parse-comments --body-only --short --no-index --no-externals --output $*.v.html  $*.v
	rm "`dirname $*`/coqdoc.css"

all: $(VOS) $(VHTMLS)

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' -o -name '*.v.html' \) -delete
