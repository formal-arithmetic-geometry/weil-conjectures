/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTate
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalTensor

/-!
# The reduction of all the Tate twists

test
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definitions of the Tate twist families: with them the monoidal
-- structure of `Ψ` and the families are stated in the same presentation
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (k : ℕ) (hk : ringChar Λ = ringChar Λ' * k)

section Twist

variable (X : Scheme.{u})

/-- The monoidal structure of the derived extension of scalars `Ψ`, the left derived functor of
the strong monoidal extension of scalars of étale sheaves
(`CategoryTheory.Functor.leftDerivedFunctorMonoidal`). -/
noncomputable abbrev derivedExtendScalarsMonoidal : (derivedExtendScalars hρ ha X).Monoidal :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal

variable [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]

set_option profiler true


/-- doc -/
noncomputable def reductionTateTwistIso (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj (tateObject Λ X m) ≅ tateObject Λ' X m :=
  letI := derivedExtendScalarsMonoidal hρ ha X
  IntTensorFamily.iso ((tateTwistIntTensorFamily Λ X).map (derivedExtendScalars hρ ha X))
    (tateTwistIntTensorFamily Λ' X) (reductionTateTwistOneIso hρ ha k hk X) m

lemma reductionTateTwistIso_one :
    reductionTateTwistIso hρ ha k hk X 1 = reductionTateTwistOneIso hρ ha k hk X :=
  IntTensorFamily.iso_one _ _ _

lemma reductionTateTwistIso_mul (m m' : ℤ) :
    letI := derivedExtendScalarsMonoidal hρ ha X
    (derivedExtendScalars hρ ha X).map (HasTateTwist.twistObjectAddIso (Λ := Λ) X m m').hom ≫
        (reductionTateTwistIso hρ ha k hk X (m + m')).hom =
      Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) (tateObject Λ X m)
          (tateObject Λ X m') ≫
        ((reductionTateTwistIso hρ ha k hk X m).hom ⊗ₘ
          (reductionTateTwistIso hρ ha k hk X m').hom) ≫
          (HasTateTwist.twistObjectAddIso (Λ := Λ') X m m').hom :=
  letI := derivedExtendScalarsMonoidal hρ ha X
  IntTensorFamily.map_iso_mul (tateTwistIntTensorFamily Λ X) (derivedExtendScalars hρ ha X)
    (tateTwistIntTensorFamily Λ' X) (reductionTateTwistOneIso hρ ha k hk X) m m'

lemma reductionTateTwistIso_zero :
    letI := derivedExtendScalarsMonoidal hρ ha X
    (reductionTateTwistIso hρ ha k hk X 0).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ') X).hom =
      (derivedExtendScalars hρ ha X).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).hom ≫
        Functor.OplaxMonoidal.η (derivedExtendScalars hρ ha X) :=
  letI := derivedExtendScalarsMonoidal hρ ha X
  IntTensorFamily.map_iso_zero _ _ _ _

lemma derivedExtendScalarsConstantComplexIso_hom_eq_η :
    letI := derivedExtendScalarsMonoidal hρ ha X
    (derivedExtendScalarsConstantComplexIso hρ ha X).hom =
      Functor.OplaxMonoidal.η (derivedExtendScalars hρ ha X) :=
  derivedExtendScalarsConstantComplexIso_hom hρ ha X

end Twist

section Pullback

open Functor.OplaxMonoidal

variable {U X : Scheme.{u}} (e : U ⟶ X)

/-- The commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` is compatible with the tensor comparisons `δ`
of `Ψ` and of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackOfCounit_app_tensor_comp`). -/
@[reassoc]
lemma derivedExtendScalarsPullbackIso_hom_app_tensor_comp
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := derivedExtendScalarsMonoidal hρ ha X
    letI := derivedExtendScalarsMonoidal hρ ha U
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
    (derivedExtendScalarsPullbackIso hρ ha e).hom.app (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map (δ (derivedExtendScalars hρ ha X) K M) ≫
          δ L((e)^*[ModuleCat.{u + 1} Λ']) _ _ =
      (derivedExtendScalars hρ ha U).map (δ L((e)^*[ModuleCat.{u + 1} Λ]) K M) ≫
        δ (derivedExtendScalars hρ ha U) _ _ ≫
          ((derivedExtendScalarsPullbackIso hρ ha e).hom.app K ⊗ₘ
            (derivedExtendScalarsPullbackIso hρ ha e).hom.app M) := by
  sorry

variable [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U]
  [HasInvertibleExponent Λ' X]

/-- The compatibility of the identifications `Le^* Λ_X(m) ≅ Λ_U(m)` with the products, written
with the tensor comparison `δ` of the derived pullback. -/
lemma leftDerivedUpperStar_map_twistObjectAddIso_δ (Λ : Type (u + 1)) [CommRing Λ]
    [NeZero (ringChar Λ)] [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ X] (m m' : ℤ) :
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    L((e)^*[ModuleCat.{u + 1} Λ]).map (HasTateTwist.twistObjectAddIso (Λ := Λ) X m m').hom ≫
        (leftDerivedUpperStarTateObjectIso e (m + m')).hom =
      δ L((e)^*[ModuleCat.{u + 1} Λ]) (tateObject Λ X m) (tateObject Λ X m') ≫
        ((leftDerivedUpperStarTateObjectIso e m).hom ⊗ₘ
          (leftDerivedUpperStarTateObjectIso e m').hom) ≫
          (HasTateTwist.twistObjectAddIso (Λ := Λ) U m m').hom := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  exact leftDerivedUpperStar_map_tateTwistObjectAddIso Λ e m m'


/-- The naturality of `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*`, without composites of functors. -/
@[reassoc]
lemma derivedExtendScalarsPullbackIso_hom_naturality
    {K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : K ⟶ M) :
    (derivedExtendScalars hρ ha U).map (L((e)^*[ModuleCat.{u + 1} Λ]).map f) ≫
        (derivedExtendScalarsPullbackIso hρ ha e).hom.app M =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app K ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map ((derivedExtendScalars hρ ha X).map f) :=
  (derivedExtendScalarsPullbackIso hρ ha e).hom.naturality f

/-- `AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso_hom_app_tensor_comp` for the Tate
twists. -/
@[reassoc]
lemma derivedExtendScalarsPullbackIso_hom_app_tensor_comp_tateObject (m m' : ℤ) :
    letI := derivedExtendScalarsMonoidal hρ ha X
    letI := derivedExtendScalarsMonoidal hρ ha U
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
    (derivedExtendScalarsPullbackIso hρ ha e).hom.app (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (HasTateTwist.twistObject (Λ := Λ) X m)).obj (HasTateTwist.twistObject (Λ := Λ) X m')) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map
          (δ (derivedExtendScalars hρ ha X) (tateObject Λ X m) (tateObject Λ X m')) ≫
          δ L((e)^*[ModuleCat.{u + 1} Λ']) _ _ =
      (derivedExtendScalars hρ ha U).map
          (δ L((e)^*[ModuleCat.{u + 1} Λ]) (tateObject Λ X m) (tateObject Λ X m')) ≫
        δ (derivedExtendScalars hρ ha U) _ _ ≫
          ((derivedExtendScalarsPullbackIso hρ ha e).hom.app (tateObject Λ X m) ⊗ₘ
            (derivedExtendScalarsPullbackIso hρ ha e).hom.app (tateObject Λ X m')) :=
  derivedExtendScalarsPullbackIso_hom_app_tensor_comp hρ ha e _ _

variable (Λ) in
/-- The coherent family `Ψ_U Le^* Λ_X(m)` on `U`. -/
noncomputable def reductionPullbackTateTwistIntTensorFamily :
    IntTensorFamily (DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :=
  letI := derivedExtendScalarsMonoidal hρ ha U
  letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_η (ModuleCat.{u + 1} Λ) e
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
  ((tateTwistIntTensorFamily Λ X).map L((e)^*[ModuleCat.{u + 1} Λ])).map
    (derivedExtendScalars hρ ha U)

lemma reductionPullbackTateTwistIntTensorFamily_addIso_hom (m m' : ℤ) :
    letI := derivedExtendScalarsMonoidal hρ ha U
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
    ((reductionPullbackTateTwistIntTensorFamily Λ hρ ha e).addIso m m').hom =
      inv (δ (derivedExtendScalars hρ ha U) _ _) ≫ (derivedExtendScalars hρ ha U).map
        (inv (δ L((e)^*[ModuleCat.{u + 1} Λ]) (tateObject Λ X m) (tateObject Λ X m')) ≫
          L((e)^*[ModuleCat.{u + 1} Λ]).map (HasTateTwist.twistObjectAddIso (Λ := Λ) X m m').hom) :=
  rfl

/-- The identifications `Ψ_U Le^* Λ_X(m) ≅ Ψ_U Λ_U(m) ≅ Λ'_U(m)` are multiplicative. -/
lemma reductionTateTwistIso_pullback_left_mul (m m' : ℤ) :
    ((reductionPullbackTateTwistIntTensorFamily Λ hρ ha e).addIso m m').hom ≫
        (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e (m + m')).hom ≫
          (reductionTateTwistIso hρ ha k hk U (m + m')).hom =
      (((derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e m).hom ≫
          (reductionTateTwistIso hρ ha k hk U m).hom) ⊗ₘ
        ((derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e m').hom ≫
          (reductionTateTwistIso hρ ha k hk U m').hom)) ≫
        (HasTateTwist.twistObjectAddIso (Λ := Λ') U m m').hom := by
  letI := derivedExtendScalarsMonoidal hρ ha U
  letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
  rw [reductionPullbackTateTwistIntTensorFamily_addIso_hom, Category.assoc,
    ← Functor.map_comp_assoc, Category.assoc, leftDerivedUpperStar_map_twistObjectAddIso_δ,
    IsIso.inv_hom_id_assoc, Functor.map_comp_assoc, reductionTateTwistIso_mul,
    ← δ_natural_assoc, IsIso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

/-- The identifications `Ψ_U Le^* Λ_X(m) ≅ Le^* Ψ_X Λ_X(m) ≅ Le^* Λ'_X(m) ≅ Λ'_U(m)` are
multiplicative. -/
lemma reductionTateTwistIso_pullback_right_mul (m m' : ℤ) :
    ((reductionPullbackTateTwistIntTensorFamily Λ hρ ha e).addIso m m').hom ≫
        (derivedExtendScalarsPullbackIso hρ ha e).hom.app (tateObject Λ X (m + m')) ≫
          L((e)^*[ModuleCat.{u + 1} Λ']).map (reductionTateTwistIso hρ ha k hk X (m + m')).hom ≫
            (leftDerivedUpperStarTateObjectIso e (m + m')).hom =
      (((derivedExtendScalarsPullbackIso hρ ha e).hom.app (tateObject Λ X m) ≫
          L((e)^*[ModuleCat.{u + 1} Λ']).map (reductionTateTwistIso hρ ha k hk X m).hom ≫
            (leftDerivedUpperStarTateObjectIso e m).hom) ⊗ₘ
        ((derivedExtendScalarsPullbackIso hρ ha e).hom.app (tateObject Λ X m') ≫
          L((e)^*[ModuleCat.{u + 1} Λ']).map (reductionTateTwistIso hρ ha k hk X m').hom ≫
            (leftDerivedUpperStarTateObjectIso e m').hom)) ≫
        (HasTateTwist.twistObjectAddIso (Λ := Λ') U m m').hom := by
  letI := derivedExtendScalarsMonoidal hρ ha U
  letI := derivedExtendScalarsMonoidal hρ ha X
  letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
  rw [reductionPullbackTateTwistIntTensorFamily_addIso_hom, Functor.map_comp, Category.assoc,
    Category.assoc, derivedExtendScalarsPullbackIso_hom_naturality_assoc hρ ha e
      (M := tateObject Λ X (m + m')) (HasTateTwist.twistObjectAddIso X m m').hom,
    ← Functor.map_comp_assoc, reductionTateTwistIso_mul, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, leftDerivedUpperStar_map_twistObjectAddIso_δ,
    ← δ_natural_assoc, derivedExtendScalarsPullbackIso_hom_app_tensor_comp_tateObject_assoc]
  simp only [Functor.map_inv, IsIso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]


/-- **The reductions `Ψ(Λ_X(m)) ≅ Λ'_X(m)` of the Tate twists are compatible with the derived
pullbacks.** Both composites `Ψ_U Le^* Λ_X(m) ⟶ Λ'_U(m)` are multiplicative
(`AlgebraicGeometry.Etale.reductionTateTwistIso_pullback_left_mul`,
`AlgebraicGeometry.Etale.reductionTateTwistIso_pullback_right_mul`), and they agree in degree one
(`AlgebraicGeometry.Etale.reductionTateTwistOneIso_pullback`), so they agree
(`CategoryTheory.MonoidalCategory.IntTensorFamily.iso_unique_mul`). -/
theorem reductionTateTwistIso_pullback (m : ℤ) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e m).hom ≫
        (reductionTateTwistIso hρ ha k hk U m).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (reductionTateTwistIso hρ ha k hk X m).hom ≫
          (leftDerivedUpperStarTateObjectIso e m).hom := by
  let s (m : ℤ) := (derivedExtendScalars hρ ha U).mapIso (leftDerivedUpperStarTateObjectIso e m) ≪≫
    reductionTateTwistIso hρ ha k hk U m
  let t (m : ℤ) := (derivedExtendScalarsPullbackIso hρ ha e).app (tateObject Λ X m) ≪≫
    (L((e)^*[ModuleCat.{u + 1} Λ'])).mapIso (reductionTateTwistIso hρ ha k hk X m) ≪≫
      leftDerivedUpperStarTateObjectIso e m
  have hs := IntTensorFamily.iso_unique_mul (reductionPullbackTateTwistIntTensorFamily Λ hρ ha e)
    (tateTwistIntTensorFamily Λ' U) (s 1) s rfl
    (fun m m' ↦ reductionTateTwistIso_pullback_left_mul hρ ha k hk e m m') m
  have ht := IntTensorFamily.iso_unique_mul (reductionPullbackTateTwistIntTensorFamily Λ hρ ha e)
    (tateTwistIntTensorFamily Λ' U) (s 1) t (by
      ext
      dsimp only [s, t, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
      rw [reductionTateTwistIso_one, reductionTateTwistIso_one]
      exact (reductionTateTwistOneIso_pullback hρ ha k hk e).symm)
    (fun m m' ↦ reductionTateTwistIso_pullback_right_mul hρ ha k hk e m m') m
  exact congrArg Iso.hom (hs.trans ht.symm)

end Pullback

end AlgebraicGeometry.Etale
