/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTate
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalPullback

/-!
# The canonical Tate data of the reduction of coefficients

Let `ρ : Λ →+* Λ'` be a surjective morphism of coefficient rings with principal kernel, with
characteristics `n = n' k`, and `Ψ` the derived extension of scalars along `ρ`, a monoidal functor
(`AlgebraicGeometry.Etale.extendScalarsDerivedMonoidal`). The reduction
`σ_X : Ψ(Λ_X(1)) ≅ Λ'_X(1)` of the Tate twist (`AlgebraicGeometry.Etale.reductionTateTwistOneIso`)
extends uniquely to a multiplicative family `Ψ(Λ_X(m)) ≅ Λ'_X(m)`, `m ∈ ℤ`
(`AlgebraicGeometry.Etale.reductionTateTwistIso`), since the Tate twists form coherent integer
tensor families. By uniqueness, this family is compatible with the derived pullbacks
(`AlgebraicGeometry.Etale.reductionTateTwistIso_pullback`), which gives the canonical Tate data
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` of the reduction
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData`, blueprint
`det-sp-purity-coefficient-change`), with the hypotheses `hunit`
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData_unit`) and `hμ`
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData_mul`) of
`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesKummerBoundaries`.

All statements are written with the instances used in the definition of the Tate twist families
(`SymmetricCategory.toBraidedCategory` on `ModuleCat`): with the default braiding instance the
kernel has to compare two presentations of the monoidal structure of the derived category, which
it does not do in reasonable time.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definitions of the Tate twist families: with them the monoidal
-- structure of `Ψ` and the families are stated in the same presentation
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)
  [F.CommShift ℤ]

/-- The commutations of a functor with the shifts by two equal integers `n = N`, through the
equality transports of the shifted objects. -/
lemma map_eqToHom_comp_commShiftIso_hom_app_comp {n N : ℤ} (h : n = N) {T T' : C} (hT : T = T')
    {L : D} (f : F.obj T' ⟶ L) (p : T⟦n⟧ = T'⟦N⟧) (q : L⟦n⟧ = L⟦N⟧) :
    F.map (eqToHom p) ≫ (F.commShiftIso N).hom.app T' ≫ f⟦N⟧' =
      (F.commShiftIso n).hom.app T ≫ (eqToHom (congrArg F.obj hT) ≫ f)⟦n⟧' ≫ eqToHom q := by
  subst h hT
  simp

end CategoryTheory.Functor

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
noncomputable abbrev extendScalarsDerivedMonoidal : (derivedExtendScalars hρ ha X).Monoidal :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal

variable [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]



/-- **The reduction of the Tate twists**, `Ψ(Λ_X(m)) ≅ Λ'_X(m)`: the unique multiplicative
extension (`CategoryTheory.MonoidalCategory.IntTensorFamily.iso`) of the reduction
`Ψ(Λ_X(1)) ≅ Λ'_X(1)` of the Tate twist (`AlgebraicGeometry.Etale.reductionTateTwistOneIso`). -/
noncomputable def reductionTateTwistIso (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj (tateObject Λ X m) ≅ tateObject Λ' X m :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  IntTensorFamily.iso ((tateTwistIntTensorFamily Λ X).map (derivedExtendScalars hρ ha X))
    (tateTwistIntTensorFamily Λ' X) (reductionTateTwistOneIso hρ ha k hk X) m

/-- In degree one, the reduction of the Tate twists is `Ψ(Λ_X(1)) ≅ Λ'_X(1)`. -/
lemma reductionTateTwistIso_one :
    reductionTateTwistIso hρ ha k hk X 1 = reductionTateTwistOneIso hρ ha k hk X :=
  IntTensorFamily.iso_one _ _ _

/-- The reduction of the Tate twists is multiplicative. -/
lemma reductionTateTwistIso_mul (m m' : ℤ) :
    letI := extendScalarsDerivedMonoidal hρ ha X
    (derivedExtendScalars hρ ha X).map (HasTateTwist.twistObjectAddIso (Λ := Λ) X m m').hom ≫
        (reductionTateTwistIso hρ ha k hk X (m + m')).hom =
      Functor.OplaxMonoidal.δ (derivedExtendScalars hρ ha X) (tateObject Λ X m)
          (tateObject Λ X m') ≫
        ((reductionTateTwistIso hρ ha k hk X m).hom ⊗ₘ
          (reductionTateTwistIso hρ ha k hk X m').hom) ≫
          (HasTateTwist.twistObjectAddIso (Λ := Λ') X m m').hom :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  IntTensorFamily.map_iso_mul (tateTwistIntTensorFamily Λ X) (derivedExtendScalars hρ ha X)
    (tateTwistIntTensorFamily Λ' X) (reductionTateTwistOneIso hρ ha k hk X) m m'

/-- In degree zero, the reduction of the Tate twists is the unit comparison of `Ψ`. -/
lemma reductionTateTwistIso_zero :
    letI := extendScalarsDerivedMonoidal hρ ha X
    (reductionTateTwistIso hρ ha k hk X 0).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ') X).hom =
      (derivedExtendScalars hρ ha X).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).hom ≫
        Functor.OplaxMonoidal.η (derivedExtendScalars hρ ha X) :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  IntTensorFamily.map_iso_zero _ _ _ _

omit [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ' X] in
/-- `Ψ Λ_X ≅ Λ'_X` is the unit comparison of `extendScalarsDerivedMonoidal`. -/
lemma derivedExtendScalarsConstantComplexIso_hom_eq_η :
    letI := extendScalarsDerivedMonoidal hρ ha X
    (derivedExtendScalarsConstantComplexIso hρ ha X).hom =
      Functor.OplaxMonoidal.η (derivedExtendScalars hρ ha X) :=
  derivedExtendScalarsConstantComplexIso_hom hρ ha X

end Twist

section Pullback

open Functor.OplaxMonoidal

variable {U X : Scheme.{u}} (e : U ⟶ X)

/-- The commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` is compatible with the tensor comparisons `δ`
of `Ψ` and of the derived pullbacks. -/
@[reassoc]
lemma derivedExtendScalarsPullbackIso_hom_app_tensor_comp
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := extendScalarsDerivedMonoidal hρ ha X
    letI := extendScalarsDerivedMonoidal hρ ha U
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
    (derivedExtendScalarsPullbackIso hρ ha e).hom.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M) ≫
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


omit [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] [HasInvertibleExponent Λ U]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X] in
/-- The naturality of `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*`, without composites of functors. -/
@[reassoc]
lemma derivedExtendScalarsPullbackIso_hom_naturality
    {K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : K ⟶ M) :
    (derivedExtendScalars hρ ha U).map (L((e)^*[ModuleCat.{u + 1} Λ]).map f) ≫
        (derivedExtendScalarsPullbackIso hρ ha e).hom.app M =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app K ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map ((derivedExtendScalars hρ ha X).map f) :=
  (derivedExtendScalarsPullbackIso hρ ha e).hom.naturality f

omit [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U]
  [HasInvertibleExponent Λ' X] in
/-- `AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso_hom_app_tensor_comp` for the Tate
twists. -/
@[reassoc]
lemma derivedExtendScalarsPullbackIso_hom_app_tensor_comp_tateObject (m m' : ℤ) :
    letI := extendScalarsDerivedMonoidal hρ ha X
    letI := extendScalarsDerivedMonoidal hρ ha U
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
  letI := extendScalarsDerivedMonoidal hρ ha U
  letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_η (ModuleCat.{u + 1} Λ) e
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
  ((tateTwistIntTensorFamily Λ X).map L((e)^*[ModuleCat.{u + 1} Λ])).map
    (derivedExtendScalars hρ ha U)

omit [NeZero (ringChar Λ')] [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U]
  [HasInvertibleExponent Λ' X] in
/-- The multiplication of the family `Ψ_U Le^* Λ_X(m)`. -/
lemma reductionPullbackTateTwistIntTensorFamily_addIso_hom (m m' : ℤ) :
    letI := extendScalarsDerivedMonoidal hρ ha U
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
    ((reductionPullbackTateTwistIntTensorFamily Λ hρ ha e).addIso m m').hom =
      inv (δ (derivedExtendScalars hρ ha U) _ _) ≫ (derivedExtendScalars hρ ha U).map
        (inv (δ L((e)^*[ModuleCat.{u + 1} Λ]) (tateObject Λ X m) (tateObject Λ X m')) ≫
          L((e)^*[ModuleCat.{u + 1} Λ]).map (HasTateTwist.twistObjectAddIso (Λ := Λ) X m m').hom) :=
  rfl

omit [HasInvertibleExponent Λ' X] in
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
  let := extendScalarsDerivedMonoidal hρ ha U
  let := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
  rw [reductionPullbackTateTwistIntTensorFamily_addIso_hom, Category.assoc,
    ← Functor.map_comp_assoc, Category.assoc, leftDerivedUpperStar_map_twistObjectAddIso_δ,
    IsIso.inv_hom_id_assoc, Functor.map_comp_assoc, reductionTateTwistIso_mul,
    ← δ_natural_assoc, IsIso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

omit [HasInvertibleExponent Λ U] in
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
  let := extendScalarsDerivedMonoidal hρ ha U
  let := extendScalarsDerivedMonoidal hρ ha X
  let := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  let := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ (ModuleCat.{u + 1} Λ) e
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

section Data

open Functor.OplaxMonoidal

/-- In degree zero, the reduction `Ψ(Λ_U(0)) ≅ Λ'_U(0)` of the Tate twists is, through
`Λ(0) ≅ Λ`, the identification `Ψ Λ_U ≅ Λ'_U`. -/
lemma map_twistObjectZeroIso_hom_comp_derivedExtendScalarsConstantComplexIso_hom
    (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] :
    (derivedExtendScalars hρ ha U).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha U).hom =
      (reductionTateTwistIso hρ ha k hk U 0).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).hom := by
  rw [derivedExtendScalarsConstantComplexIso_hom_eq_η]
  exact (reductionTateTwistIso_zero hρ ha k hk U).symm

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The canonical Tate data of the reduction of coefficients**: the identifications
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` attached (`AlgebraicGeometry.Etale.reductionTateData`) to the
multiplicative family `Ψ(Λ_X(m)) ≅ Λ'_X(m)` extending the reduction `Ψ(Λ_X(1)) ≅ Λ'_X(1)` of the
Tate twist (`AlgebraicGeometry.Etale.reductionTateTwistIso`). -/
noncomputable def reductionTateTwistShiftData : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha :=
  reductionTateData hρ ha (fun X _ _ m ↦ reductionTateTwistIso hρ ha k hk X m)
    (fun e m ↦ reductionTateTwistIso_pullback hρ ha k hk e m)

/-- The canonical Tate data are the commutation of `Ψ` with the shifts followed by the shifted
reduction of the Tate twists. -/
lemma reductionTateTwistShiftData_iso_hom (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] (m : ℤ) :
    ((reductionTateTwistShiftData hρ ha k hk).iso X m).hom =
      ((derivedExtendScalars hρ ha X).commShiftIso (2 * m)).hom.app _ ≫
        (reductionTateTwistIso hρ ha k hk X m).hom⟦2 * m⟧' :=
  rfl

variable [Finite Λ] [Finite Λ'] in
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

The hypothesis `hunit` of
`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesKummerBoundaries` for the
reduction of coefficients with its canonical Tate data
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData`). -/
theorem reductionTateTwistShiftData_unit (U : Scheme.{u}) [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ' U] :
    ((reductionSupportedCoefficientChange hρ ha
        (reductionTateTwistShiftData hρ ha k hk)).functor U).map
        ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
          (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) ≫
        ((reductionSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U 0).hom =
      ((reductionSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).constantComplexIso U).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).inv ≫
          (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _ :=
  reductionSupportedCoefficientChange_unit hρ ha _ _
    (fun U _ _ ↦ map_twistObjectZeroIso_hom_comp_derivedExtendScalarsConstantComplexIso_hom
      hρ ha k hk U) U


/-- **The tensor comparison of `Ψ` commutes with the shifts**: through the commutations of `Ψ`
with the shifts, `δ : Ψ(K ⊗ᴸ M) ⟶ Ψ K ⊗ᴸ Ψ M` is compatible with the isomorphisms
`K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧` (`AlgebraicGeometry.Etale.derivedTensorShiftIso`). This is the
analogue for `Ψ` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_derivedTensorShiftIso`. -/
@[reassoc]
lemma derivedExtendScalars_map_derivedTensorShiftIso_hom (X : Scheme.{u})
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a b : ℤ) :
    letI := extendScalarsDerivedMonoidal hρ ha X
    (derivedExtendScalars hρ ha X).map
        (derivedTensorShiftIso (ModuleCat.{u + 1} Λ) K M a b).hom ≫
        ((derivedExtendScalars hρ ha X).commShiftIso (a + b)).hom.app
          (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M) ≫
          (δ (derivedExtendScalars hρ ha X) K M)⟦a + b⟧' =
      δ (derivedExtendScalars hρ ha X) (K⟦a⟧) (M⟦b⟧) ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ')
          (((derivedExtendScalars hρ ha X).commShiftIso a).hom.app K)
          (((derivedExtendScalars hρ ha X).commShiftIso b).hom.app M) ≫
          (derivedTensorShiftIso (ModuleCat.{u + 1} Λ') _ _ a b).hom := by
  sorry

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

The hypothesis `hμ` of
`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesKummerBoundaries` for the
reduction of coefficients with its canonical Tate data, the tensor comparison of the change of
coefficients being `δ : Ψ(K ⊗ᴸ M) ⟶ Ψ K ⊗ᴸ Ψ M`: the identifications
`Ψ(Λ(m)[2m]) ≅ Λ'(m)[2m]` are compatible with the multiplications
`Λ(m)[2m] ⊗ᴸ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`). -/
theorem reductionTateTwistShiftData_mul (U : Scheme.{u}) [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ' U] (m m' : ℤ) :
    letI := extendScalarsDerivedMonoidal hρ ha U
    (derivedExtendScalars hρ ha U).map (shiftTateObjectAddIso Λ U m m').hom ≫
        ((reductionTateTwistShiftData hρ ha k hk).iso U (m + m')).hom =
      δ (derivedExtendScalars hρ ha U) _ _ ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ')
          ((reductionTateTwistShiftData hρ ha k hk).iso U m).hom
          ((reductionTateTwistShiftData hρ ha k hk).iso U m').hom ≫
          (shiftTateObjectAddIso Λ' U m m').hom := by
  let := extendScalarsDerivedMonoidal hρ ha U
  simp only [reductionTateTwistShiftData_iso_hom, shiftTateObjectAddIso, Iso.trans_hom,
    Functor.mapIso_hom, eqToIso.hom, Functor.map_comp, Category.assoc]
  have h₁ :
      (derivedExtendScalars hρ ha U).map (HasTateTwist.twistObjectAddIso (Λ := Λ) U m m').hom ≫
          (reductionTateTwistIso hρ ha k hk U (m + m')).hom =
        δ (derivedExtendScalars hρ ha U) (tateObject Λ U m) (tateObject Λ U m') ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ') (reductionTateTwistIso hρ ha k hk U m).hom
            (reductionTateTwistIso hρ ha k hk U m').hom ≫
            (HasTateTwist.twistObjectAddIso (Λ := Λ') U m m').hom := by
    rw [reductionTateTwistIso_mul, MonoidalCategory.tensorHom_def]
    rfl
  have h₂ := derivedExtendScalars_map_derivedTensorShiftIso_hom hρ ha U (tateObject Λ U m)
    (tateObject Λ U m') (2 * m) (2 * m')
  have h₃ := derivedTensorHom_shift_comp_derivedTensorShiftIso_hom (ModuleCat.{u + 1} Λ')
    (reductionTateTwistIso hρ ha k hk U m).hom (reductionTateTwistIso hρ ha k hk U m').hom
    (2 * m) (2 * m')
  dsimp only [tateObject] at h₁ h₂ h₃ ⊢
  rw [Functor.map_eqToHom_comp_commShiftIso_hom_app_comp _ (by ring) rfl, eqToHom_refl,
    Category.id_comp, Functor.commShiftIso_hom_naturality_assoc,
    ← Functor.map_comp_assoc, h₁, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc,
    reassoc_of% h₂, ← reassoc_of% h₃,
    derivedTensorHom_comp_assoc]

end Data

end AlgebraicGeometry.Etale
