## What changed

Replaced the hole in
`AlgebraicGeometry.exists_perfect_split_degree_zero` by a proof from the existing
finite-free refinement and affine cut declarations, and an affine fibre-map comparison.
The existing public signature is preserved.

The proof constructs a bounded-above finite-free module model by lifting a local free
sheaf complex through fully faithful affine sheafification. It applies the affine cut,
realizes its principal-localization splitting on an open subscheme, and identifies the
nonpositive summand with restricted H⁰ using the unit tensor and the standard t-structure.

Added `AffinePrincipalModelComparison.lean`: the principal neighbourhood, its spectrum
isomorphism, the exact sheafification functor and its natural model comparison are
constructed explicitly. Added `AffinePerfectCutSheafRealization.lean`: finite-projective
retracts give perfectness, flatness and positive tensor amplitude; exactness and the
biproduct splitting identify the first summand with the canonical truncation.

Added `AffinePerfectFibreSurjectivity.lean`, which reduces the canonical fibre arrow
comparison to the affine stalk scalar comparison. The proof transports the local derived
model to the original stalk ring and uses a common K-flat roof to compare canonical arrows.
Added `AffineModelStalkBaseChange.lean` for the remaining localization and residue-field
comparison. Updated the parent DAG route and added matching nodes for four new statements.

## Proved and sorry left

Original item: one hole. Closed:
`AlgebraicGeometry.exists_perfect_split_degree_zero`.

New public declarations with complete proofs:
`AlgebraicGeometry.affine_principal_model_comparison`,
`AlgebraicGeometry.affine_perfect_cut_sheaf_realization`, and
`AlgebraicGeometry.affine_perfect_fibre_surjectivity`.

Added one hole:
`AlgebraicGeometry.affine_model_stalk_baseChange`
(node `lem-sc-affine-model-stalk-base-change`). It remains exactly `:= by sorry`.
It must identify the affine associated-sheaf stalk of a supplied K-flat module complex
with its localization, transfer K-flatness, and compare the two canonical base-change
arrows after residue-field transport. It has no global derived object, chosen sheaf
representative, splitting, perfection, or surjectivity hypothesis. Existing affine
stalk-presentation and residue scalar-transport declarations supply the geometric
identifications; their compatibility with the canonical arrow still needs assembly.

The fibre-surjectivity module contains the proved private local-model stalk comparison
`local_model_derived_stalk_iso`, constructed from the existing open restriction-stalk
comparison, and the proved private helpers
`cohomologyBaseChange_naturality`,
`epi_cohomologyBaseChange_iff_of_quasiIso`, and
`epi_cohomologyBaseChange_iff_of_kFlat_derivedIso`. They prove the representative
independence part of its recorded argument directly from the adjunction unit and
a common K-flat roof. The proved private `kFlat_of_acyclic_tensor` translates the
stalk criterion to the quasi-isomorphism localization API. These are used in the
public fibre-surjectivity proof.

This is a decomposition of one original hole into one strictly smaller comparison
obligation, with the other geometric and categorical steps proved. The delivery adds
one hole and closes one hole; it claims no positive net hole reduction.

All five Lean modules were compiled individually with `lcompile.py`, without errors
or warnings. The original public signature and the node/declaration text were also
checked locally.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`.
The parent proof no longer needs node `lem-sc-perfect-finite-free-residue-model` or
its prescribed residue-cohomology ranks. The affine cut accepts any bounded-above
finite-free representative, so the proved finite-free refinement and elementary
full-faithfulness lifting construction suffice. The module may still be needed by
other consumers; this report only prunes its edge from the assigned item.

The proof still uses `Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero` and its
positive finite-projective model. There are no withdrawn modules.

## Where the brief, the DAG or earlier work was wrong

The original DAG required a minimal-rank residue model before the affine cut. That
extra construction is unnecessary for this argument: Tag 0A1U starts with a
bounded-above finite-free complex, and the negative Tor bound is only needed to
identify the nonpositive summand with H⁰ afterward.

The previously described passage from stalk fibre-surjectivity to the canonical
module base-change map is a substantive comparison. The exact-stalk and K-flat
representative comparisons are now proved; the compatibility of affine localization
and residue transport with the canonical arrow is the remaining named obligation.
The passage from a localized module splitting to the sheaf splitting has been proved
explicitly in this delivery.

No existing statement or definition was changed. There are no forced consumer
adaptations, target changes or disputed statements.

## New nodes

`lem-sc-affine-perfect-fibre-surjectivity` records the proved affine fibre-arrow
comparison, without a Tor-amplitude assumption or a splitting conclusion. Its source
is the affine reduction of Tag 0A1U and the K-flat stalk/resolution comparison. It
uses the one remaining scalar comparison.

`lem-sc-affine-model-stalk-base-change` records that remaining comparison. It is
independent of the global derived object and its model isomorphism, and is valid
without finite-free or boundedness assumptions. Its docstring explains the natural
affine localization, tensor and residue-field maps, canonical-arrow compatibility,
and the empty-open, zero-module and acyclic-complex edge cases.

`lem-sc-affine-principal-model-comparison` records the proved exact principal-open
associated-sheaf comparison. It assumes only a supplied affine model and an element
outside the point prime; it has no perfection, Tor or splitting assumption.

`lem-sc-affine-perfect-cut-sheaf-realization` records the proved realization of a
supplied algebraic cut and positive finite-projective model. It does not choose a
cut or assume the fibre-surjectivity condition.

No change records were needed: the existing public interface and definitions are
preserved, and all additional statements are in new modules.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
