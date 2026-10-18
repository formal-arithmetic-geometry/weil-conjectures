## What changed

Proved `AlgebraicGeometry.exists_integral_fibre_etale_splitting` in
`Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting`, with its public statement and public
imports unchanged. All supporting lemmas are private, proved helpers in the same module.
No definition, existing auxiliary statement, or consumer was changed.

The proof uses the first proof of Stacks Tag 0BSR rather than the DAG's idempotent-lifting
route. After the existing residue-splitting theorem, finitely many separating elements give
a finite intermediate algebra for one selected fibre point. The existing proved elementary
étale finite-neighbourhood theorem supplies a clopen singleton neighbourhood. Finite
induction makes these disjoint, and closedness of the integral projection removes the
empty-fibre remainder. Residue-field isomorphisms and a scalar tower transport pure
inseparability. Empty fibres and an empty family of separating generators are included.

Added proof imports of `WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint`,
`WeilConjectures.AlgebraicGeometry.FinitePiecePersistence` (with `import all`, using only its
proved private pullback-point uniqueness and residue-isomorphism helpers),
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
and `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
Updated the existing node's proof, proof dependencies and proof origin to describe the
actual proof. Removed its obsolete idempotent-lifting tool-use approval. The new use of
`lem-weil-pbc-etale-local-finite-at-point-elementary` is a proved theorem from unit
`sk-thm-p1`; its tool-use approval is left to the maintainer. The existing residue-splitting
tool use is retained. No blueprint unit statement or realized proof step is bypassed.

Validation: the consolidated module compiled cleanly with `lcompile.py` (6.8 seconds).
A separate Lean probe printed precisely `[propext, Classical.choice, Quot.sound]` for
`AlgebraicGeometry.exists_integral_fibre_etale_splitting`; there is no `sorryAx` dependency.
The probe was removed from the delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_integral_fibre_etale_splitting`
(node `lem-weil-pbc-integral-fibre-etale-splitting`).
One of one original sorries proved; zero sorries left; zero added; zero split off.
This is a proof, not a decomposition into new obligations.

## No longer needed

Removed proof imports:

- `Sheaf.RingTheory.LiftIdempotentUpstairs`;
- `WeilConjectures.RingTheory.LiftIdempotentUpstairs`;
- `Mathlib.AlgebraicGeometry.OpenImmersion`;
- `Mathlib.AlgebraicGeometry.Pullbacks`;
- `Mathlib.AlgebraicGeometry.Fiber`;
- `Mathlib.RingTheory.Spectrum.Prime.Topology`;
- `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`.

The Mathlib imports above are redundant with the retained imports; their relevant APIs are
still used where needed. `Mathlib.RingTheory.Ideal.GoingUp` remains necessary for
incomparability. The idempotent-lifting source module is not used at all.

Removed these direct dependencies from this node's planned route:

- `lem-weil-pbc-fibre-product-affine-spectra`: no tensor-product presentation is constructed;
- `def-pc-scheme-fibre`: no explicit fibre-ring construction in this proof (still a
  transitive dependency of the existing finite-neighbourhood theorem);
- `lem-weil-pbc-integral-prime-over-maximal-maximal`: discrete fibres are used only for the
  finite intermediate morphism, via the existing Mathlib quasi-finite API;
- `lem-weil-pbc-spec-clopen-idempotent`: clopens come from proper open inclusions;
- `lem-weil-pbc-lift-idempotent-upstairs`: replaced by the finite-model argument; its module
  `WeilConjectures.RingTheory.LiftIdempotentUpstairs` and retired Sheaf re-export
  `Sheaf.RingTheory.LiftIdempotentUpstairs` are unnecessary for this item;
- `lem-weil-pbc-etale-localization-functor-adjoint`: ordinary étale composition suffices;
- `lem-weil-pbc-affine-open-section-vanishing-prime`: no principal-open coordinate argument;
- `lem-weil-pbc-spec-localization-away-basic-open`: choose an arbitrary affine open inside
  the complement of the closed image instead.

Withdrawn tool-use approval: `lem-weil-pbc-lift-idempotent-upstairs`.
These are pruning recommendations for this item's route; other parents may still need them.

## Where the brief, the DAG or earlier work was wrong

The original statement is true and was kept exactly. Its planned idempotent descent and
lifting steps are unnecessary because the already proved 02LK theorem can be applied to a
finite intermediate algebra. The private finite-model lemma proves the precise singleton
property needed; it does not assume the integral morphism itself is finite or locally of
finite type. No process failure or forced consumer adaptation occurred.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
