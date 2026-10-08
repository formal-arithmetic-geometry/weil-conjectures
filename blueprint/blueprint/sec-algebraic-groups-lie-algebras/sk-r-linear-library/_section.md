+++
id = "sk-r-linear-library"
kind = "section"
title = "The linear-algebra library"
order = 2538
uses = ["sk-d-linear"]
+++
*Remark (sketch).*

Three standard facts about finite-dimensional representations over a field
$k$ are used below and in §[sec-purity-real-sheaves] without further comment;
they are quoted, not proved here.

2pt
1. **(L1)** *Jordan–Hölder.* A finite-dimensional
$k$-representation has a composition series, and the
multiset of its simple subquotients is independent of the series.
1. **(L2)** *Schur's lemma.* An endomorphism of a simple module
commuting with the action is zero or invertible; over an algebraically
closed $k$ it is a scalar. In particular a central element acts on a simple
module by a scalar, nonzero when the element is invertible.
1. **(L3)** *Tensor filtration.* A tensor product, exterior power or
dual of representations carrying filtrations carries the induced filtration,
whose graded pieces are the corresponding constructions on the graded
pieces; consequently the constituents of such a construction are determined
by the constituents of its arguments.

The three propositions that follow — [sk-p-linear-filtration],
[sk-p-linear-triangular] and [sk-p-linear-spectra] — are *not*
part of this library: they are proved.

Uses: [sk-d-linear]
