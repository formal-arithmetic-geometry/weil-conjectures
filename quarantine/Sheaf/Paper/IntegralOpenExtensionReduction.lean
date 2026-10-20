/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

import Sheaf.SixFunctors.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Extension by zero commutes naturally with integral reduction

Source: blueprint main-20261015, integral extension by zero
(blueprint: lem-sfb-integral-open-extension-reduction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private def pointPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X) :
    (upperStarFromPoint X).mapMod Λ ⋙ upperStar Λ j ≅
      (upperStarFromPoint U).mapMod Λ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapModCompIso (upperStarFromPoint X)
        (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} j)
        (upperStarFromPointComp j).hom Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ j))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)) ≪≫
        (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).unitIso.symm) ≪≫
    Functor.rightUnitor _

private def identityDirectImageIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (lowerStar Λ (𝟙 X)).rightDerivedFunctor ≅ 𝟭 _ := by
  let e := AlgebraicGeometry.ProEtale.CondensedRing.lowerStarId Λ X
  have : PreservesFiniteColimits (lowerStar Λ (𝟙 X)) :=
    preservesFiniteColimits_of_natIso e.symm
  exact (lowerStar Λ (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

private theorem openTensorProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Nonempty ((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (derivedTensor Λ X).flip.obj B ≅
      (derivedTensor Λ U).flip.obj ((upperStar Λ j).mapDerivedCategory.obj B) ⋙
        (openImmersionLowerShriek Λ j).mapDerivedCategory) := by
  obtain ⟨e⟩ := locallyClosedImmersionTensorProjection Λ k j j (𝟙 X) (by simp)
  let e' := ((CategoryTheory.flipFunctor _ _ _).mapIso e).app B
  let F := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let G := (lowerStar Λ (𝟙 X)).rightDerivedFunctor
  let α : F ⋙ G ≅ F := Functor.isoWhiskerLeft F (identityDirectImageIso Λ X) ≪≫
    Functor.rightUnitor F
  exact ⟨Functor.isoWhiskerRight α.symm _ ≪≫ e' ≪≫ Functor.isoWhiskerLeft
    ((derivedTensor Λ U).flip.obj ((upperStar Λ j).mapDerivedCategory.obj B)) α⟩

/-- Extension by zero commutes naturally with integral reduction in the standing
separated finite-type setting over a field.

Source: blueprint main-20261015, sk-cor-int-compactness-ii-extension-zero.proof.md,
proof (1), reduction modulo a uniformizer power; det-lem-int-tensor-projection.

Proof: specialize locallyClosedImmersionTensorProjection to the factorization of j
as j followed by the identity. Identify the derived identity direct image with the
identity functor. Evaluate the resulting bifunctor isomorphism at the pulled-back
quotient module in degree zero. The coefficient pullback from the point composes
with j^* up to the mapMod composition and the restriction-extension equivalence.
The exact derived pullback commutes with degree-zero realization, so its value on
this quotient is the corresponding quotient on U. Tensoring this identification
and composing with the projection isomorphism proves the comparison naturally in K.
This applies to every coefficient module and hence every n, including n = 0; no
boundedness or completeness hypothesis is used.
(blueprint: lem-sfb-integral-open-extension-reduction). -/
theorem integralOpenExtensionReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    ∀ n : ℕ, Nonempty
      ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ⋙
          integralReductionFunctor l E X n ≅
        integralReductionFunctor l E U n ⋙
          (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory) := by
  intro n
  let Λ := integralCoefficientRing l E
  let M := DerivedNakayama.quotientModule l E n
  let FX := DerivedNakayama.pullback l E X
  let FU := DerivedNakayama.pullback l E U
  let J := upperStar Λ j
  let B := (DerivedCategory.singleFunctor _ 0).obj (FX.obj M)
  let b : J.mapDerivedCategory.obj B ≅
      (DerivedCategory.singleFunctor _ 0).obj (FU.obj M) :=
    (J.mapDerivedCategorySingleFunctor 0).app (FX.obj M) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso ((pointPullbackIso Λ j).app M)
  obtain ⟨e⟩ := openTensorProjection Λ k j B
  exact ⟨e ≪≫ Functor.isoWhiskerRight
    ((derivedTensor Λ U).flip.mapIso b) _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
