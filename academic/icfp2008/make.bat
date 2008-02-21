lhs2tex firstify.tex -o final.tex
bibtex final
texify final.tex
del catch.dvi
copy final.dvi firstify.dvi
