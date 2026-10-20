/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C7
-/
module

public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.RingedSiteModules

import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Unbounded closed projection with arbitrary ringed coefficients

Source: current blueprint main-20261015, six-functors basics, middle projection
identity of closed-costalk duality (blueprint: lem-sf-etale-closed-projection-unbounded).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Exactness of the actual module pushforward, including restriction of scalars.
The composite with forgetting coefficients is the exact finite etale direct image;
the target forgetful functor reflects finite colimits. -/
private theorem closedEtaleModulePushExact
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (R : Sheaf (T.smallGrothendieckTopology @Etale) RingCat.{u + 1})
    (S : Sheaf (Z.smallGrothendieckTopology @Etale) RingCat.{u + 1})
    (φ : R ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous
      RingCat.{u + 1} (T.smallGrothendieckTopology @Etale)
      (Z.smallGrothendieckTopology @Etale)).obj S) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1} φ) := by
  let F := SheafOfModules.pushforward.{u + 1} φ
  let V := SheafOfModules.toSheaf R
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} S) := by
    infer_instance
  have : PreservesFiniteColimits (Etale.lowerStar AddCommGrpCat.{u + 1} i) := by
    infer_instance
  have : PreservesFiniteColimits (F ⋙ V) := by
    change PreservesFiniteColimits
      (SheafOfModules.toSheaf S ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} i)
    infer_instance
  have : ReflectsFiniteColimits V :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves F V

/-- Closed projection for the normalized derived tensor on the small etale site.
The rings and the module direct image below are the actual inverse-image ring and
sectionwise direct image. The termwise comparisons allow any presentations of the
exact derived operations. No exceptional inverse image or dualizing object occurs.

Source: current blueprint main-20261015, six-functors basics,
`sk-prop-sf-biduality-general/lem-weil-closed-costalk-duality.proof.md`, middle
projection identity; Stacks, Tags 04CA, 07A4 and 08J9.
(blueprint: lem-sf-etale-closed-projection-unbounded).

Proof: the closed module pushforward is exact by finite etale direct-image
exactness, reflected through the forgetful functor, as proved in the private
helper above. Its inverse-image counit is invertible and its open restriction
is zero: check these on geometric stalks, forgetting the coefficient action.
The maps are linear, and forgetting reflects isomorphisms. The closed and open
inverse images are jointly conservative, first
on sheaves and then on cohomology of arbitrary complexes. Their exact termwise
functors and adjunction descend through quasi-isomorphism localization, with the
given factorization comparisons. Inverse image commutes with the derived tensor:
resolve by flat K-flat complexes and use the sheafified scalar tensor comparison.
The models' representative comparisons identify these tensors with the specified
normalized tensors. Form the natural projection map from i_*N tensor K to
i_*(N tensor i^*K) as the adjoint of the inverse-image tensor comparison followed
by the closed counit tensor identity. Closed restriction makes it invertible by
the counit and its triangle identity. Open restriction makes it a map between
zero objects. Both restrictions preserve cones; joint detection on cohomology
makes its cone zero, so the projection map is invertible. Take its inverse to
obtain the orientation displayed below. All constructions are natural in N,K.
The argument applies to the empty closed or open subscheme and to zero complexes,
and uses no boundedness or Tor bound. -/
theorem closedImmersionEtaleProjection
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}) :
    let RZ := (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @Etale ⊤ i) CommRingCat.{u + 1}
      (T.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj R
    let MT := ringedSiteModules.{u + 1} ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    let MZ := ringedSiteModules.{u + 1} ((sheafCompose Z.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ)
    letI : HasDerivedCategory.{u + 2} MT := HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 2} MZ := HasDerivedCategory.standard _
    let V₀ : MZ ⥤ MT :=
      SheafOfModules.pushforward.{u + 1}
      (F := MorphismProperty.Over.pullback @Etale ⊤ i)
      (J := T.smallGrothendieckTopology @Etale) (K := Z.smallGrothendieckTopology @Etale)
      (S := (sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose Z.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @Etale ⊤ i) CommRingCat.{u + 1}
      (T.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj R))
      ⟨Functor.whiskerRight ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ i) CommRingCat.{u + 1}
      (T.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    letI : V₀.Additive := ⟨by intros; rfl⟩
    ∀ (iStar : MT ⥤ MZ) [iStar.Additive] (ai : iStar ⊣ V₀)
      (iPull : DerivedCategory MT ⥤ DerivedCategory MZ)
      (pullFactors : DerivedCategory.Q ⋙ iPull ≅
        iStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (iPush : DerivedCategory MZ ⥤ DerivedCategory MT)
      (pushFactors : DerivedCategory.Q ⋙ iPush ≅
        V₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (t : RingedSiteDualityModel.{u + 1, u, 0, u + 2} T.smallEtaleTopology R)
      (z : RingedSiteDualityModel.{u + 1, u, 0, u + 2} Z.smallEtaleTopology RZ),
      Nonempty (((𝟭 (DerivedCategory MZ)).prod iPull) ⋙ z.closed.tensor ⋙ iPush ≅
        (iPush.prod (𝟭 (DerivedCategory MT))) ⋙ t.closed.tensor) := by
  sorry

end AlgebraicGeometry.Scheme
