
all: unbound-NJPLS-20110408.pdf

# images/%.pdf : images/%.svg
# 	make -C images $(@F)

# static-images/%.pdf : static-images/%.svg
# 	make -C static-images $(@F)

%.pdf: %.tex
	rubber -d $<

%.tex: %.lhs
	lhs2TeX --poly $< > $@

clean:
	rm -f *.{aux,dvi,log,nav,out,pdf,ptb,snm,tex,toc,vrb}
	rm -f *~
