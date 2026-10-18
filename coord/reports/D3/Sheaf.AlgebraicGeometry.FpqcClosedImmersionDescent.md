## What changed

Proved `AlgebraicGeometry.isClosedImmersion_of_fpqc_cover` in
`Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent`, with its signature and public imports
unchanged. The proof installs the source library's proved singleton descent theorem and
specializes its proved covering-family descent theorem to closed immersions and the canonical
pullback squares. The generated sieve is covering by
`Precoverage.generate_mem_toGrothendieck hg`.

The two proof imports are now
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. Both import-direction checks passed.
The node's proof and proof dependencies now describe these existing proved declarations.
No definitions, statements, instances, or other modules were changed.

The final proof compiled through `lcompile.py` in 2.6 seconds. A separate compilation of
`#print axioms AlgebraicGeometry.isClosedImmersion_of_fpqc_cover` checked the complete
transitive proof. The delivery dry run performs its independent compile and axiom probe.
The family universe remains arbitrary; neither a nonempty index set nor a nonempty scheme
is assumed, and the generic covering theorem handles the empty cover of the empty scheme.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.isClosedImmersion_of_fpqc_cover`
(node `lem-pc-fpqc-descend-closed-immersion`). Added 0 holes; split off 0 theorems.
No `sorry` remains in the delivered module. The axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.FpqcAffineDescent`.
- `Sheaf.AlgebraicGeometry.Morphisms.ClosedImmersionOfSurjectiveStructureStalks`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.

The proof no longer directly uses any of the old seven declared proof dependencies:

- `lem-weil-pbc-closed-immersion-integral-separated-uc`.
- `lem-weil-pbc-fpqc-descend-affine`.
- `lem-pc-flat-base-change-cohom`.
- `lem-weil-pbc-closed-immersion-affine-cover-criterion`.
- `lem-pc-local-flat-faithful-flat-reflects-surjective`.
- `def-weil-flat-morphism` (flatness enters through the existing descent API).
- `lem-pc-affine-surjective-structure-map-closed-immersion`.

The existing source-library proofs supply the required descent facts, so the unfinished
Sheaf affine-descent and structure-stalk-criterion modules are unnecessary for this proof.
The cohomological pushforward and local-ring tensor argument is unnecessary as well.
The node's six obsolete top-level tool approvals were removed: two occurrences each of
`lem-weil-pbc-fpqc-descend-affine`, `lem-pc-flat-base-change-cohom`, and
`lem-weil-pbc-closed-immersion-affine-cover-criterion`.
These are removals from this item's dependency route; other parents can still need them.
No unit statement or unit proof step is bypassed: the unit's closed-immersion descent
assertion is still proved, using already proved source declarations below that level.

## Where the brief, the DAG or earlier work was wrong

The original route missed the source library's existing closed-immersion singleton-descent
and generic fpqc covering-family descent declarations. Their combination gives this exact
statement without any unfinished dependencies or new lemmas.

The recorded attachment of `lem-pc-flat-base-change-cohom` is
`AlgebraicGeometry.Scheme.Modules.finrankH_pullback`, a cohomology-dimension equality for
field extensions. It does not state the sheaf-level flat-base-change isomorphism required
by the original step 2. That attachment is not used or changed by this delivery.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
