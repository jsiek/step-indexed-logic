SRCDIR = ../../src
SRCTEX = $(SRCDIR)/latex

PAPERTEX = latex/July2023

#  latex/July2023/SILReference.tex
paper.pdf: paper.tex $(SRCTEX)/StepIndexedLogic2.tex $(PAPERTEX)/STLC2.tex $(PAPERTEX)/LogRel2.tex $(PAPERTEX)/STLCDeterministic2.tex $(PAPERTEX)/STLCBind2.tex $(PAPERTEX)/STLCSafe2.tex $(PAPERTEX)/STLCTypeSafe.tex  $(PAPERTEX)/SILIntro.tex
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper

texclean:
	rm -f paper.out paper.aux paper.bbl paper.blg

clean:
	rm -f paper.out paper.aux paper.bbl paper.blg $(PAPERTEX)/* $(SRCTEX)/*


$(SRCTEX)/StepIndexedLogic2.tex: $(SRCDIR)/StepIndexedLogic2.lagda
	cd $(SRCDIR) ; agda --latex StepIndexedLogic2.lagda

$(PAPERTEX)/SILIntro.tex: SILIntro.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex SILIntro.lagda

$(PAPERTEX)/SILReference.tex: SILReference.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex SILReference.lagda

$(PAPERTEX)/STLC2.tex: STLC2.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex STLC2.lagda

$(PAPERTEX)/LogRel2.tex: LogRel2.lagda STLC2.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex LogRel2.lagda

$(PAPERTEX)/STLCDeterministic2.tex: STLCDeterministic2.lagda STLC.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex STLCDeterministic2.lagda

$(PAPERTEX)/STLCBind2.tex: STLCBind2.lagda STLCDeterministic2.lagda STLC2.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex STLCBind2.lagda

$(PAPERTEX)/STLCSafe2.tex: STLCSafe2.lagda  STLCBind2.lagda STLC2.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex STLCSafe2.lagda

$(PAPERTEX)/STLCTypeSafe.tex: STLCTypeSafe.lagda STLCSafe2.lagda  STLCBind2.lagda STLC2.lagda $(SRCDIR)/StepIndexedLogic2.lagda
	agda --latex STLCTypeSafe.lagda
