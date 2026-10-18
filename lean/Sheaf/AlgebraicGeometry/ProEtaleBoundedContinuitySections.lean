/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex
import Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence
import Sheaf.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-!
# Bounded-below filtered-colimit continuity of pro-etale hypercohomology

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
det-pe-bounded-continuity-sections.md and its proof
(blueprint: det-pe-bounded-continuity-sections).

## Main definitions

- `ringHypercohomology`: integer-degree derived sections with arbitrary ring-sheaf coefficients.

## Main statements

- `ringHypercohomology_transport_preservesZeroMorphisms`: transport acts on complexes.
- `isIso_ringHypercohomology_colimitPost`: the canonical bounded-below continuity map is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The published sectionwise transport preserves zero maps, as needed to apply it
termwise to complexes. Source: the blueprint's small-site size convention and
Stacks Project, Tag 03D1 (blueprint: det-pe-bounded-continuity-sections).
Proof: transport precomposes every component with `AsSmall.down`; a zero module-sheaf
map has a zero component at every object, which remains zero after precomposition. -/
theorem ringHypercohomology_transport_preservesZeroMorphisms (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).PreservesZeroMorphisms := by
  sorry

attribute [instance] ringHypercohomology_transport_preservesZeroMorphisms

/-- Hypercohomology at an object of the small pro-etale site, with arbitrary ring-sheaf
coefficients. Transport to the published small site model is sectionwise precomposition;
then take the published functorial K-injective resolution, evaluate its underlying abelian
section complex, and take its integer-degree homology. On bounded-below complexes this is
canonically the evaluation of a bounded-below injective resolution: both compute the right
derived evaluation functor, and comparison with a K-injective resolution is unique up to
homotopy. This construction retains all original site objects and the original coefficients.

Source: the blueprint, det-pe-bounded-continuity-sections.md, convention for `H^q(U,-)`;
Stacks Project, Tags 079P and 09A2 (blueprint: det-pe-bounded-continuity-sections). -/
noncomputable def ringHypercohomology (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) (q : ℤ) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤ AddCommGrpCat.{u + 1} :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    CochainComplex.kInjectiveResolutionFunctor.{u + 1} (ringedSiteModules.{u + 1} S) ⋙
    (SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
      forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U))))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q

/-- Hypercohomology on every qcqs pro-etale object commutes with filtered colimits of
complexes having one common strict lower bound. The map is `colimit.post`, whose composite
with each colimit inclusion is the hypercohomology of the original complex colimit leg.
Complex colimits are termwise sheaf colimits by `HomologicalComplex`'s colimit construction.

Source: Weil conjectures blueprint, snapshot main-20261015,
det-pe-bounded-continuity-sections.md and its proof
(blueprint: det-pe-bounded-continuity-sections).

Proof for stage 3:
1. Module sheaves have small colimits by lem-weil-pbc-ring-sheaves-grothendieck.
   Form the termwise colimit complex using the universal cocone in every degree.
   Its differential is induced by the differentials of the diagram. The chain identities
   and square-zero identity follow on every colimit leg. Its terms below a are zero.
2. By det-pe-hypercover-existence choose one affine weakly contractible hypercover of U,
   fixed for the entire diagram. By det-pe-hypercover-complex its section totals compute
   the hypercohomology of each complex and the colimit, naturally. In degree n only
   the finitely many hypercover degrees 0 through n-a contribute, with none when n<a.
3. Apply det-pe-sections-limits-colimits in every bidegree. The underlying abelian-group
   colimit is also the module colimit: scalar multiplication is induced on the additive
   colimit by its universal property, and the module laws and linearity are checked on
   its legs. These comparisons commute with face restrictions and complex differentials.
4. Exchange the finite diagonal sums with the colimit. The resulting degreewise
   isomorphisms commute with both alternating-face and signed vertical differentials,
   so identify the total complexes, including empty diagonals.
5. Filtered colimits of abelian groups are exact by
   lem-weil-pbc-filtered-colimit-abelian-groups-exact. Apply this to the compatible short
   exact sequences of cycles, boundaries and cohomology. It identifies cohomology of
   the colimit total with the colimit of its cohomology, with the canonical cycle maps.
6. Naturality of det-pe-hypercover-complex identifies the composite isomorphism on every
   colimit leg with hypercohomology of that leg. The colimit universal property makes
   it exactly colimit.post below, in every integer degree, also q<a. -/
theorem isIso_ringHypercohomology_colimitPost (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (ringedSiteModules.{u + 1} R) ℤ)
    (a : ℤ) (hK : ∀ (i : I) (b : ℤ), b < a → IsZero ((K.obj i).X b)) (q : ℤ) :
    IsIso (colimit.post K (ringHypercohomology X R U q)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
