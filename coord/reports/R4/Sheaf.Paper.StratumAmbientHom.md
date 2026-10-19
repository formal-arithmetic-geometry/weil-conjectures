## What changed

Proved both declarations of `Sheaf.Paper.StratumAmbientHom`. The etale clause reuses
`Etale.immersionInternalHomIso` and forgets its additional evaluation normalization.
The pro-etale clause proves the open and closed projection formulas for the actual
intrinsic constant-ring derived categories, composes them along the given factorization,
and applies parametrized tensor–Hom adjunction and conjugate isomorphisms.

The private helpers prove joint isomorphism detection from sheaf zero detection via
kernels, cokernels and derived homology; derive disjoint-support vanishing and the
open unit/closed counit isomorphisms; construct the actual projection maps as mates;
and check their invertibility after the two complementary restrictions. The tensor
model is explicitly the restriction of the existing K-flat representative comparison.
The open complement of an arbitrary open immersion is realized by the vanishing-ideal
closed subscheme. No helper proof is postponed and no existing definition is changed.

Added a public import of `Sheaf.AlgebraicGeometry.EtaleGenericStratumMate` because its
two functor names now appear in the definitionally identical etale signature. Other
new imports are proof-only. Removed redundant public imports listed below. Updated the
existing node's proof, proof dependencies, proof origin, Lean signature text and obsolete
top-level tool approvals. The enclosing blueprint unit's route is retained.

The etale signature presentation and its consumer check are recorded in
`coord/changes/StratumAmbientHomEtalePresentation.md`. The item compiled after integration
and import pruning. All eight unchanged direct importing modules compiled against the
pruned public interface; their slowest compile was 37.3 seconds. No consumer adaptation
is delivered. The final delivery tool performs its own compile and axiom checks.

## Proved and sorry left

Closed both original holes (node `lem-weil-stratum-ambient-hom`):

- `AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso`.
- `AlgebraicGeometry.ProEtale.nonempty_stratumAmbientHomIso`.

Actual item hole count: 2 originally, 0 remaining. Holes added: 0. Split-off statements: 0.
All private helper declarations are proved. Existing declared dependencies can still
have their own unfinished proofs, as intended by stage 3; this packet adds none.

## No longer needed

Removed these redundant public imports (the declarations needed in the public statements
are still supplied by the four retained public imports):

- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.

The direct etale proof reuses the existing immersion theorem rather than reproducing
its stalk, tensor and Hom arguments. The pro-etale proof uses the already stated
closed tensor–Hom model and proves both projection formulas by support detection,
so it needs neither a separate open projection theorem nor a second total-complex
or Hom-complex construction. Accordingly these old direct proof dependencies and
their associated modules are no longer separate obligations of this item:

- `lemma-openclosed-stalk-lowerstar` (`WeilConjectures.SixFunctors.OpenClosed.Stalk`).
- `prop-weil-pbc-geometric-stalks-exact` (Mathlib leaf).
- `lemma-weil-pbc-geometric-stalk-conservative` (`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`).
- `lem-kun-04ca` (`Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`).
- `lem-weil-pbc-site-pullback-abelian-exact` (`Sheaf.CategoryTheory.SitePullbackAbelianExact`).
- `lem-weil-pbc-ringed-topoi-module-adjunction` (`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`).
- `prop-pur-kinjective-resolutions-exist` (`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`).
- `lem-weil-pbc-right-adjoint-preserves-kinjective` (`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`).
- `lem-weil-pbc-kinjective-hom-derived` (Mathlib leaf).
- `lem-weil-pbc-kinjective-total-derived` (`Sheaf.CategoryTheory.KInjectiveTotalDerived`).
- `lem-weil-pbc-extension-by-zero-adjunction` (`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`).
- `lem-weil-pbc-extension-by-zero-exact` (`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`).
- `lem-exc-closed-ambient` (`Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`).
- `def-pc-kflat-complex` (`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`).
- `lem-weil-pbc-open-immersion-etale` (Mathlib leaf).
- `lem-weil-pbc-etale-inverse-image-restriction` (`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`).
- `lem-weil-proetale-weakly-etale-localization` (`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`).
- `lem-weil-pbc-ringed-slice-extension-tensor` (`Sheaf.CategoryTheory.RingedSliceExtensionTensor`).
- `lem-pc-kflat-resolution` (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`).
- `lem-weil-pbc-site-derived-tensor-descent` (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`).
- `lem-cbc-extension-zero-projection-formula` (`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`).
- `lem-pur-hom-kflat-into-kinjective` (`Sheaf.Algebra.Homology.KInjectiveHomComplex`).
- `lem-sc-derived-hom-tensor-total` (`Sheaf.Algebra.Homology.HomTensorTotal`).
- `lem-pur-rhom-global-sections` (`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`).
- `def-pur-derived-internal-hom` (`Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`).
- `lem-pc-sheaf-modules-tensor-closed` (`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`).

Some of these results remain in statement dependencies or transitively inside the
reused theorems; no globally unreachable module is claimed and no existing module is
withdrawn. The two draft projection modules from the earlier sandbox packet are not
delivered: the complete projection proofs are private helpers in this item. No new
nodes are required.

Removed the obsolete top-level `tool_uses` entries corresponding to the list above,
except `def-pc-kflat-complex` and `def-pur-derived-internal-hom`, which had no such
entries. Retained approvals keep their original order; no approvals were added.
The candidate proof imports `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange` and
`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction` were also eliminated before
delivery: the first supplied only an elementary transported adjunction, now constructed
locally, and the second supplied no additional API used by this proof.

## Where the brief, the DAG or earlier work was wrong

The blueprint's stalkwise shorthand does not suffice to detect pro-etale isomorphisms.
The expanded DAG already requires open/closed detection; this proof implements that
requirement using the existing ringed theorem and derives its unbounded-complex form explicitly. The open projection formula admits
the same support argument as the closed formula, avoiding the earlier unfinished
split-off projection statements altogether.

The earlier expanded etale functor spelling caused expensive kernel conversion.
The existing `immersionLowerShriek` and `immersionUpperShriek` names unfold to precisely
those composites and keep every binder and universe. No target statement is changed.
The old node docstrings remain the source's expanded plan; the updated DAG proof
records the shorter actual argument. There is no remaining mathematical dispute.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
