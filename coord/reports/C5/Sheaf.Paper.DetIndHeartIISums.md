## What changed

Proved AlgebraicGeometry.ProEtale.det_ind_heart_ii_sums by the blueprint's three-step
finite-subcoproduct argument, using constructible_sheaf_ext_continuity. Two private,
fully proved categorical helpers supply the universal-property argument and identify
the additive-group coproduct with the displayed DirectSum.toAddMonoid.

Corrected the coefficient interface to bind a condensed ring with its canonical ring
structure, matching the continuity theorem. See
coord/changes/C5-det-ind-heart-ii-sums-canonical-ring.md. The mathematical statement
already specifies these canonical field coefficients. No target changes. The universal-property proofs include the empty index set:
its empty finite subcoproduct is initial, and the explicit direct sum is zero.
The shift stays arbitrary, so negative and zero Ext degrees use the same argument.

## Proved and sorry left

Closed the one original hole in
AlgebraicGeometry.ProEtale.det_ind_heart_ii_sums (node det-ind-heart-ii-sums).
Zero new holes; zero sorry declarations remain in the delivered module.
Both the module and its unchanged direct consumer compiled successfully against
the corrected coefficient interface. Both compiled again after all four redundant
imports were pruned (6.3 seconds and 24.3 seconds respectively). The unchanged
consumer was copied only for this check and is not included in the delivery.
The proof uses the existing, still-open
AlgebraicGeometry.ProEtale.constructible_sheaf_ext_continuity
(node sk-lem-constructible-ext-continuity), as the assigned proof route requires.

## No longer needed

The separately stated ringed-site generator theorem
lem-pur-ringed-site-grothendieck-abelian / WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
is not used: the ambient module category already has the required instances.
The DAG proof dependencies were updated accordingly. Removed redundant public imports:

- Sheaf.Paper.CondensedConstantConstructibility;
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility;
- WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod;
- Mathlib.Algebra.Homology.DerivedCategory.Basic;

The constructibility, module and derived-category APIs are already public through
CoefficientHeartCommonStratification. The coefficient-extension compatibility theorem
module is unrelated to the finite-subset proof.

The unlanded earlier draft's preserves_coproduct_of_finite_subcoproducts,
directSum_postcomp_bijective and single_coproduct_isColimit sorry declarations were
removed. There is no new node det-ind-heart-ii-single-coproduct in this delivery.
The proof only needs preservation of finite sums by the derived single functor.

## Where the brief, the DAG or earlier work was wrong

The earlier draft's directSum_postcomp_bijective incorrectly inferred arbitrary
coproduct preservation from additivity alone. It is false, for example for Hom from
an infinite-rank free abelian group. The replacement explicitly requires coproduct
preservation, and that hypothesis is proved from finite additivity and filtered
Ext continuity, retaining the unit's route.

The original coefficient signature equated underlying abelian sheaves but left the
MonObj structure arbitrary. The change record explains its correction. The
ind-constructibility hypothesis is retained; the available continuity theorem is
strong enough to apply to all module diagrams.

The required downstream.py audit completed: 204 transitive importers and no
application of det_ind_heart_ii_sums outside its owning declaration. The change record
lists every downstream module and its holder, with an independent exact source-import
inventory covering 204 modules. Independent name/import searches confirm exactly
one direct importer, ConstructibleCompactnessBounded; its original compiled against
the corrected interface and pruned imports. No consumer was edited. The item compiled
again against the current published build in this resumed session (5.0 seconds,
exit code 0). The delivery tools remain the required final gates.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
