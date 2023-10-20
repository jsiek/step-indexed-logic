SRCDIR = ../../src
SRCTEX = $(SRCDIR)/latex

PAPERTEX = latex/July2023

#  latex/July2023/SILReference.tex
paper.pdf: paper.tex $(SRCTEX)/RawSetO.tex $(SRCTEX)/Approx.tex $(SRCTEX)/Iteration.tex $(SRCTEX)/EquivalenceRelation.tex $(SRCTEX)/Variables.tex $(SRCTEX)/Env.tex $(SRCTEX)/SetO.tex $(SRCTEX)/Fixpoint.tex $(SRCTEX)/Membership.tex $(SRCTEX)/Later.tex $(SRCTEX)/RecPred.tex  $(SRCTEX)/StepIndexedLogic2.tex $(PAPERTEX)/STLC2.tex $(PAPERTEX)/LogRel2.tex $(PAPERTEX)/STLCDeterministic2.tex $(PAPERTEX)/STLCBind2.tex $(PAPERTEX)/STLCSafe2.tex $(PAPERTEX)/STLCTypeSafe.tex  $(PAPERTEX)/SILIntro.tex
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


$(SRCTEX)/EquivalenceRelation.tex: $(SRCDIR)/EquivalenceRelation.lagda
	cd $(SRCDIR) ; agda --latex EquivalenceRelation.lagda

$(SRCTEX)/RawSetO.tex: $(SRCDIR)/RawSetO.lagda
	cd $(SRCDIR) ; agda --latex RawSetO.lagda

$(SRCTEX)/Approx.tex: $(SRCDIR)/Approx.lagda
	cd $(SRCDIR) ; agda --latex Approx.lagda

$(SRCTEX)/Iteration.tex: $(SRCDIR)/Iteration.lagda
	cd $(SRCDIR) ; agda --latex Iteration.lagda

$(SRCTEX)/Variables.tex: $(SRCDIR)/Variables.lagda
	cd $(SRCDIR) ; agda --latex Variables.lagda

$(SRCTEX)/Env.tex: $(SRCDIR)/Env.lagda
	cd $(SRCDIR) ; agda --latex Env.lagda

$(SRCTEX)/SetO.tex: $(SRCDIR)/SetO.lagda
	cd $(SRCDIR) ; agda --latex SetO.lagda

$(SRCTEX)/Fixpoint.tex: $(SRCDIR)/Fixpoint.lagda
	cd $(SRCDIR) ; agda --latex Fixpoint.lagda

$(SRCTEX)/Membership.tex: $(SRCDIR)/Membership.lagda
	cd $(SRCDIR) ; agda --latex Membership.lagda

$(SRCTEX)/Later.tex: $(SRCDIR)/Later.lagda
	cd $(SRCDIR) ; agda --latex Later.lagda

$(SRCTEX)/RecPred.tex: $(SRCDIR)/RecPred.lagda
	cd $(SRCDIR) ; agda --latex RecPred.lagda

$(SRCTEX)/StepIndexedLogic2.tex: $(SRCDIR)/RawSetO.lagda $(SRCDIR)/Approx.lagda $(SRCDIR)/Iteration.lagda $(SRCDIR)/Variables.lagda $(SRCDIR)/Env.lagda $(SRCDIR)/SetO.lagda $(SRCDIR)/Membership.lagda $(SRCDIR)/Later.lagda $(SRCDIR)/RecPred.lagda $(SRCDIR)/StepIndexedLogic2.lagda
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
