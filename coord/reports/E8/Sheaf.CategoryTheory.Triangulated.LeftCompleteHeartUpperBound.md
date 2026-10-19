## What changed

Proved `DerivedCategory.upperBound_of_heart_of_leftComplete` with its original signature.
The proof follows the finite lower-truncation induction and eventual stabilization in the
node. Two proved private helpers construct the recursive solution of the tower difference
equations and prove that the mapped Roos endomorphism is epi. Applying the long exact
sequence to the mapped Roos triangle finishes the proof.

Retained the current source's public imports and theorem signature. The proof imports
Mathlib's homology-sequence API and the upstream countable-product theorem directly.
Updated the node to record direct mapping of the Roos triangle and recursive splitting.
The earlier attempt's public-import narrowing was withdrawn: two modules now import this
module, so its claim of no consumers was stale. No consumer needs adaptation.

## Proved and sorry left

Closed 1 hole: `DerivedCategory.upperBound_of_heart_of_leftComplete`
(node `lem-sfb-left-complete-heart-upper-bound`). Added 0 holes. No `sorry` remains in the
delivered module. Both private helpers are proved. The existing named dependency
`CategoryTheory.derivedCategory_countableProducts_core` is used as supplied; no additional
assertion or axiom is introduced. The final module compiled through `lcompile.py`
in 3.1 seconds with exit code 0 and no warnings (rechecked on 2026-10-19). Its
signature and public-import list were compared directly with the current source and
are identical. The proof docstring now describes the direct mapping of the triangle,
matching the Lean proof and updated node.

## No longer needed

Removed imports:

- `WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit`: the node
  `lem-pc-homotopy-limit-map` is unnecessary. Map the given Roos triangle directly with
  `T.map_distinguished` and work with its mapped limiting projection fan.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`: this retired wrapper is
  replaced by `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`, which
  supplies the same recorded dependency `lem-weil-derived-limit-products-core`.
- `Mathlib.CategoryTheory.Shift.ShiftSequence`: the proof uses the t-structure shift
  bound directly; no separate shift-sequence lemma is used.

All public imports remain as in the source. In particular, the truncation dependency
`def-kun-truncations` stays. No unit statement or step is bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The retained report's no-consumer assertion was stale:
`Sheaf.Paper.IntegralProperDirectSums` and
`Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` now import this module.
With the original public imports restored, this delivery changes no exported interface.
The planned transport to a chosen product of the image tower
is unnecessary: preservation identifies the mapped fan as limiting, so projection
extensionality suffices. The recursive splitting also works by induction on the finite
prefix before stabilization, followed by an ordinary forward natural-number recursion.
The cases N=0, a=b+1, a>b+1, arbitrary negative b and c, and j=b+c+1 are all covered by the
same proof. No closure of S under isomorphisms or assumption that S contains zero is used.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
