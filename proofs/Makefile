.PHONY: build mdgen html pdf clean all

PANDOC_FLAGS = --standalone --toc --mathjax \
    --css=style.css \
    --metadata title="Formal Verification of CQL.jl" \
    --metadata author="Simon Frost" \
    --highlight-style=tango

# Order matches CqlProofs.lean imports (dependency order)
MD_FILES = \
    SchemaCategory.md TransformCategory.md \
    DeltaSigmaAdjunction.md QueryFunctor.md \
    SchemaColimit.md Chase.md EquationalReasoning.md \
    CoEval.md InitialAlgebra.md InstanceCoproduct.md

all: build mdgen html

# Build the Lean 4 project (verifies all proofs)
build:
	lake build

# Generate markdown from Lean source via mdgen
mdgen:
	rm -rf .mdgen_tmp
	mkdir -p .mdgen_tmp
	lake exe mdgen CqlProofs .mdgen_tmp
	cat $(addprefix .mdgen_tmp/, $(MD_FILES)) > CqlProofs.md
	rm -rf .mdgen_tmp
	@echo "Generated CqlProofs.md"

# Generate HTML from markdown
html: CqlProofs.md
	pandoc CqlProofs.md -o CqlProofs.html $(PANDOC_FLAGS)
	@echo "Generated CqlProofs.html"

# Generate PDF from markdown
pdf: CqlProofs.md
	pandoc CqlProofs.md -o CqlProofs.pdf \
	    --pdf-engine=lualatex \
	    --toc \
	    --metadata title="Formal Verification of CQL.jl" \
	    --metadata author="Simon Frost" \
	    --highlight-style=tango \
	    -H header.tex
	@echo "Generated CqlProofs.pdf"

clean:
	rm -f CqlProofs.html CqlProofs.pdf CqlProofs.md
	rm -rf .mdgen_tmp
