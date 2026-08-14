# The Weil Conjectures on the Pro-etale Site through Perverse Sheaves

This directory contains the LaTeX source for the lecture notes and the
compiled PDF.

## Build

Run from this directory:

```powershell
latexmk -pdf -interaction=nonstopmode -halt-on-error weil_conjectures_proetale_perverse_notes.tex
```

The build uses BibTeX through `latexmk` and produces an A4 PDF.

## Organization

- `weil_conjectures_proetale_perverse_notes.tex` is the master file.
- `chapters/` contains the mathematical chapters and appendices.
- `bibliography.bib` contains the cited primary and expository sources.

The proof spine uses Route B. It starts with the presentable category of
solid pro-etale complexes, constructs the coherent ambient six operations,
and then proves their restriction to constructible complexes. The naive
category of all pro-etale complexes is not used as a six-functor ambient:
proper base change fails there. Derived completion, solidification,
constructibility, and rational scalar extension are kept as separate
operations.

The classical adic-system construction remains a comparison model, and its
finite-coefficient geometric theorems remain proof inputs. The
perverse-sheaf chapters isolate intermediate
extension, affine Artin vanishing, Fourier-Deligne exactness, the curve
estimate, direct-image weights, proper purity, intersection complexes, and
the decomposition theorem in a noncircular order.

These notes are self-contained relative to the precisely stated
foundational theorems in Appendix A. They do not claim to reprove the full
SGA-scale construction of those theorems from the definitions of schemes
and topoi.
