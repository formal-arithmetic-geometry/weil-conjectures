## What changed

Filled both holes in `WeilConjectures.ConstructibleSheaf.FiniteMorphism` by reusing the
existing abelian-sheaf theorems `exists_dense_open_lisse_finite_directImage` and
`isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian`. Convert source module
constructibility using `isConstructibleEtaleModuleSheaf_iff` and
`isConstructibleEtaleSheafOfSets_of_module`. Direct image commutes definitionally with
forgetting the module structure. For the conclusion, compose the module/abelian
pullback comparison with the abelian/set pullback comparison, transport the
trivializing cover and finite stalks, and apply
`IsFiniteLocallyConstantSheaf.of_forget`. One proved private helper shares this
conversion and calls the existing `AlgebraicGeometry.Scheme.lisse_of_iso` lemma. Every added import is proof-only. All existing public signatures,
definitions and public imports, and the already-proved reflection theorem, are unchanged.
The existing private `Scheme.lisse_of_iso` in the unclaimed module
`Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian` is exposed for reuse;
its type and proof are unchanged. Removed the duplicate private
`AlgebraicGeometry.lisse_of_iso` from the returned delivery.
Change record: `coord/changes/T1-finite-pushforward-lisse-iso-reuse.md`.
The node proof wording now calls the existing helper shared rather than private.

The abelian theorems are the existing Lean realizations of the same blueprint nodes.
Their proofs retain the declared generic-source/preservation/intersection argument
and the generic-lissity/finite-base-change/Noetherian-induction argument. This delivery
only transfers those results to finite module coefficients; it does not change the
mathematical route of either node and does not bypass a unit step.

Validation: both delivered modules compiled through `lcompile.py --all`: the shared
helper module in 3.1 seconds and the repaired item in 5.9 seconds, without diagnostics.
The proof transports local constancy through isomorphisms and stalk finiteness
through equivalences, so it handles empty schemes, empty strata and the zero ring
without extra hypotheses. The finite coefficient hypothesis is used by the existing
module-comparison and local-constancy reconstruction theorems.

## Proved and sorry left

Closed 2 of the original 2 holes:

- `AlgebraicGeometry.Etale.exists_dense_isFiniteLocallyConstantSheaf_lowerStar`
  (`lem-weil-pbc-finite-pushforward-generic-constructible`).
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isFinite`
  (`lem-weil-pbc-finite-pushforward-constructible-noetherian`).

Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The reflection theorem `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_lowerStar_of_isFinite`
was already proved and its proof is unchanged. Imported declarations retain their
existing proof dependencies; no claim is made that the entire transitive library is
sorry-free.

## No longer needed

Removed the duplicate private `AlgebraicGeometry.lisse_of_iso` helper from the
returned delivery. No existing imports, nodes or modules are pruned. All seven added proof-only
imports supply declarations used explicitly. The declared proof dependencies of the
original nodes remain used inside their existing abelian realizations.

## Where the brief, the DAG or earlier work was wrong

Return point 1 repaired: the prior delivery repeated the statement and proof of
private lissity-transport lemmas. Those private declarations cannot be reused through
an import. Exposing the equivalent helper in an already-imported, unclaimed module
permits direct reuse without any new proof or mathematical statement.

No mathematical defect found. The source module repeats finite-module versions of
results whose DAG attachments currently name the already-proved abelian modules.
The existing module/set comparison APIs make these holes a coefficient-transfer
problem; no new intermediate statements or definition repairs are needed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
