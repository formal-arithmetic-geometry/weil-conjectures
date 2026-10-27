## What changed

Filled four theorem bodies in
`Sheaf.AlgebraicGeometry.EtaleNormalizedMatesCompositionPasting`, without changing any
existing signature, definition, public import, attribute, or target.

- `etaleNormalizedMates_refinement` applies the existing
  `EtaleSupportExchange.rightAdjointIso_refinement` to the same canonical graph comparison.
- `etaleNormalizedMates_exchange_adjunct` applies the adjunction hom-equivalence and
  Mathlib's `mateEquiv_counit`.
- `etaleNormalizedMates_pullback_pasting` first pastes flipped sheaf inverse-image squares,
  then descends this equation using the proved finite exact-derived transformation
  pasting theorem. Explicit word-cell calculations identify every descended cell with
  the specified square comparison or pullback compositor.
- `etaleNormalizedMates_normalization_pasting` uses a proved private categorical lemma.
  Precomposition and postcomposition by the two compositor isomorphisms allow substitution
  of the existing B-pasting and pullback-pasting equations. The two normalization
  hypotheses, functoriality, and naturality then prove the conclusion.

Validation: `lcompile.py` compiled the delivered module in 31.7 seconds (exit code 0).
A signature audit confirmed every original public declaration signature and public import
is unchanged, and the node proof-dependency union matches its proof-step uses.

Updated the item's DAG proof, proof dependencies, and proof origin to record these routes.
The finite exact-derived pasting theorem is an existing, proved tool from
`lem-sp-exact-derived-transformation-pasting`; it implements precisely the localization
step of this node and bypasses no blueprint unit.

## Proved and sorry left

Closed four of the original eleven holes:

- `AlgebraicGeometry.Etale.etaleNormalizedMates_refinement`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_pullback_pasting`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_normalization_pasting`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_exchange_adjunct`.

Seven original named theorem holes remain unchanged, all attached to
`lem-pur-etale-normalized-mates-composition-pasting` with their original sources and
natural-language proofs:

- `AlgebraicGeometry.Etale.etaleNormalizedMates_composition`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_identity`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_baseChange_pasting`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_exchange_refinement`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_composition_refinement`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_composition_restriction`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_openRestriction`.

Added zero holes and zero split-off statements. The conditional normalization theorem
still uses the original named B-pasting obligation, as intended by stage 3.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` (the needed exactness
  instances are already available through the existing imports).

The direct proof dependency edges to
`lem-weil-pbc-derived-inverse-image-composition`,
`lem-weil-pbc-inverse-image-composition-module-linear`, and
`lem-weil-pbc-localization-universal-property` are replaced by the sheaf square-pasting
and exact-derived transformation-pasting nodes. The latter already proves the required
localization calculation. No existing module or declaration is withdrawn, and no claim
is made that these modules are globally unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The planned inverse-image composition theorem is stated for abelian-group coefficients
and bounded-below derived categories. It does not directly supply this module's
unbounded constant-ring-module pasting identity. The existing sheaf square-pasting
laws apply to the required coefficients, and the existing exact-derived transformation
pasting theorem descends them to the entire unbounded category. This repairs the proof
route without changing the statement. No mathematical statement is disputed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
