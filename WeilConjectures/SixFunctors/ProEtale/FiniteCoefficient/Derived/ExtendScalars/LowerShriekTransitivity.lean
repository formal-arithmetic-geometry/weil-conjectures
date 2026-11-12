/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateWhiskerHComp
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.TwoSquareTrans
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence

/-!
# Transitivity of the scalar extension comparison for `Rf_!`

Let `R → S → T` be maps of finite commutative rings and write `Ψ_{R,S} = - ⊗ᴸ_R S` for the
derived extension of scalars of pro-étale sheaves. The comparison
`τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`
(`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompMap`) is induced, through the
universal property of the left derived functor `Ψ_{R,T}`, by the isomorphism
`T ⊗_S (S ⊗_R -) ≅ T ⊗_R -` of the underived extensions of scalars
(`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompIso`).

The comparison `b` for `Rf_!` of blueprint `lemma-sp-reduction` is transitive along `τ`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap_trans`,
`lemma-sp-reduction--4`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Comp

variable {R S T : Type (u + 1)} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
  (ψ : S →+* T) (χ : R →+* T) (hχ : χ = ψ.comp φ) (X : Scheme.{u})

/-- Restriction of scalars of pro-étale sheaves along `χ = ψ ∘ φ` is restriction along `ψ` followed
by restriction along `φ`. -/
noncomputable def sheafRestrictScalarsCompIso :
    sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} ψ) ⋙
        sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) ≅
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} χ) where
  hom := sheafCompose_map (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalarsComp'.{u + 1} φ ψ χ hχ).inv
  inv := sheafCompose_map (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalarsComp'.{u + 1} φ ψ χ hχ).hom
  hom_inv_id := by
    rw [← sheafCompose_comp, Iso.inv_hom_id, sheafCompose_id]
    rfl
  inv_hom_id := by
    rw [← sheafCompose_comp, Iso.hom_inv_id, sheafCompose_id]

/-- Extension of scalars of pro-étale sheaves along `ψ ∘ φ` is extension along `φ` followed by
extension along `ψ`: the conjugate of `sheafRestrictScalarsCompIso`. -/
noncomputable def sheafExtendScalarsCompIso :
    sheafExtendScalars χ X ≅ sheafExtendScalars φ X ⋙ sheafExtendScalars ψ X :=
  (conjugateIsoEquiv ((sheafExtendScalarsAdjunction φ X).comp (sheafExtendScalarsAdjunction ψ X))
    (sheafExtendScalarsAdjunction χ X)).symm (sheafRestrictScalarsCompIso φ ψ χ hχ X)

/-- The inverse of `sheafExtendScalarsCompIso` is conjugate to the inverse of
`sheafRestrictScalarsCompIso`. -/
lemma conjugateEquiv_sheafExtendScalarsCompIso_inv :
    conjugateEquiv (sheafExtendScalarsAdjunction χ X)
        ((sheafExtendScalarsAdjunction φ X).comp (sheafExtendScalarsAdjunction ψ X))
        (sheafExtendScalarsCompIso φ ψ χ hχ X).inv =
      (sheafRestrictScalarsCompIso φ ψ χ hχ X).inv :=
  congrArg Iso.inv ((conjugateIsoEquiv _ _).apply_symm_apply
    (sheafRestrictScalarsCompIso φ ψ χ hχ X))

set_option hygiene false in
local notation "aR" => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R)
set_option hygiene false in
local notation "aS" => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S)
set_option hygiene false in
local notation "aT" => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} T)

/-- **Transitivity of the commutation of scalar extension with pullback.** The isomorphism
`g^* (T ⊗_R F) ≅ T ⊗_R g^* F` is, along `T ⊗_S (S ⊗_R -) ≅ T ⊗_R -`, the composite of the
isomorphisms `g^* (T ⊗_S -) ≅ T ⊗_S g^*` and `g^* (S ⊗_R -) ≅ S ⊗_R g^*`. -/
lemma sheafExtendScalarsCompUpperStarIso_hom_app_trans {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} T) g).map
        ((sheafExtendScalarsCompIso φ ψ χ hχ Y).inv.app F) ≫
      (sheafExtendScalarsCompUpperStarIso χ g).hom.app F =
    (sheafExtendScalarsCompUpperStarIso ψ g).hom.app ((sheafExtendScalars φ Y).obj F) ≫
      (sheafExtendScalars ψ Z).map ((sheafExtendScalarsCompUpperStarIso φ g).hom.app F) ≫
      (sheafExtendScalarsCompIso φ ψ χ hχ Z).inv.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) g).obj F) := by
  have key : Functor.whiskerRight (sheafExtendScalarsCompIso φ ψ χ hχ Y).inv
        (ProEtale.upperStar (ModuleCat.{u + 1} T) g) ≫
      (sheafExtendScalarsCompUpperStarIso χ g).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (sheafExtendScalarsCompUpperStarIso ψ g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (sheafExtendScalarsCompUpperStarIso φ g).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (sheafExtendScalarsCompIso φ ψ χ hχ Z).inv := by
    let eφY := sheafExtendScalarsAdjunction φ Y
    let eψY := sheafExtendScalarsAdjunction ψ Y
    let eχY := sheafExtendScalarsAdjunction χ Y
    let eφZ := sheafExtendScalarsAdjunction φ Z
    let eψZ := sheafExtendScalarsAdjunction ψ Z
    let eχZ := sheafExtendScalarsAdjunction χ Z
    apply (conjugateEquiv ((aR g).comp eχZ) ((eφY.comp eψY).comp (aT g))).injective
    rw [← conjugateEquiv_comp _ (eχY.comp (aT g)),
      ← conjugateEquiv_comp _ (eφY.comp (eψY.comp (aT g))),
      ← conjugateEquiv_comp _ (eφY.comp ((aS g).comp eψZ)),
      ← conjugateEquiv_comp _ ((eφY.comp (aS g)).comp eψZ),
      ← conjugateEquiv_comp _ (((aR g).comp eφZ).comp eψZ),
      ← conjugateEquiv_comp _ ((aR g).comp (eφZ.comp eψZ))]
    rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
      conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom, conjugateEquiv_associator_hom,
      conjugateEquiv_associator_inv, conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom,
      conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom,
      conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom,
      conjugateEquiv_sheafExtendScalarsCompIso_inv, conjugateEquiv_sheafExtendScalarsCompIso_inv]
    ext F U
    simp [sheafRestrictScalarsCompIso]
    rfl
  simpa using NatTrans.congr_app key F

end Comp

variable {R S T : Type (u + 1)} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable (R S T) in
/-- The comparison `τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}` of the derived extensions of scalars of
pro-étale sheaves along `R → S → T`: the morphism into the left derived functor `Ψ_{R,T}` induced
by the composite of the counits of `Ψ_{R,S}` and `Ψ_{S,T}` and the isomorphism
`T ⊗_S (S ⊗_R -) ≅ T ⊗_R -` (`sheafExtendScalarsCompIso`). -/
noncomputable def leftDerivedSheafExtendScalarsCompMap (X : Scheme.{u}) :
    L(sheafExtendScalars (algebraMap R S) X) ⋙ L(sheafExtendScalars (algebraMap S T) X) ⟶
      L(sheafExtendScalars (algebraMap R T) X) :=
  (L(sheafExtendScalars (algebraMap R T) X)).leftDerivedLift
    (sheafExtendScalars (algebraMap R T) X).leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (L(sheafExtendScalars (algebraMap R S) X) ⋙ L(sheafExtendScalars (algebraMap S T) X))
    (Functor.whiskerRight (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorCounit
        L(sheafExtendScalars (algebraMap S T) X) ≫
      Functor.whiskerLeft
        ((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (ComplexShape.up ℤ))
        (sheafExtendScalars (algebraMap S T) X).leftDerivedFunctorCounit ≫
      Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
        (sheafExtendScalarsCompIso (algebraMap R S) (algebraMap S T) (algebraMap R T)
          (IsScalarTower.algebraMap_eq R S T) X).symm (ComplexShape.up ℤ)).hom
        DerivedCategory.Qh)

variable (R S T) in
/-- On the image of a complex, the comparison `τ` is induced, through the counits, by
`T ⊗_S (S ⊗_R -) ≅ T ⊗_R -`. -/
lemma leftDerivedSheafExtendScalarsCompMap_app_comp_counit (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedSheafExtendScalarsCompMap R S T X).app (DerivedCategory.Qh.obj K) ≫
        (sheafExtendScalars (algebraMap R T) X).leftDerivedFunctorCounit.app K =
      L(sheafExtendScalars (algebraMap S T) X).map
          ((sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorCounit.app K) ≫
        (sheafExtendScalars (algebraMap S T) X).leftDerivedFunctorCounit.app
          (((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (sheafExtendScalarsCompIso (algebraMap R S) (algebraMap S T) (algebraMap R T)
            (IsScalarTower.algebraMap_eq R S T) X).symm (.up ℤ)).hom.app K) :=
  Functor.leftDerived_fac_app _ _ _ _ _ K

omit [Algebra S T] [Algebra R T] [IsScalarTower R S T] in
variable (R S) in
/-- The expanded form of `leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit`, with the
composite counits written out. -/
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit_expand [IsNoetherianRing R]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app (DerivedCategory.Qh.obj K) ≫
        L(sheafExtendScalars (algebraMap R S) Z).map
          (((g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit.app K) ≫
        (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit.app
          (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) =
      L((g)^*[ModuleCat.{u + 1} S]).map
          ((sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit.app K) ≫
        ((g)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit.app
          (((sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K) := by
  simpa only [leftDerivedSheafExtendScalarsUpperStarCounit,
    leftDerivedUpperStarSheafExtendScalarsCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] using
    leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g K

variable (R S T) in
/-- **Transitivity of the commutation of derived scalar extension with `Lg^*`.** Along
`τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`, the commutation `Lg^* Ψ_{R,T} ≅ Ψ_{R,T} Lg^*` is the composite
of the commutations for `Ψ_{R,S}` and `Ψ_{S,T}`. -/
lemma leftDerivedUpperStarExtendScalarsIso_hom_trans [IsNoetherianRing R] [IsNoetherianRing S]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    Functor.whiskerRight (leftDerivedSheafExtendScalarsCompMap R S T Y)
        L((g)^*[ModuleCat.{u + 1} T]) ≫ (leftDerivedUpperStarExtendScalarsIso R T g).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L(sheafExtendScalars (algebraMap R S) Y)
          (leftDerivedUpperStarExtendScalarsIso S T g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarExtendScalarsIso R S g).hom
          L(sheafExtendScalars (algebraMap S T) Z) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L((g)^*[ModuleCat.{u + 1} R])
          (leftDerivedSheafExtendScalarsCompMap R S T Z) :=
  Functor.leftDerived_square_trans (HomotopyCategory.quasiIso _ (.up ℤ))
    (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap S T) Y).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R T) Y).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap S T) Z).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R T) Z).leftDerivedFunctorCounit
    ((g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit
    ((g)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit
    ((g)^*[ModuleCat.{u + 1} T]).leftDerivedFunctorCounit
    (leftDerivedUpperStarSheafExtendScalarsCounit R T g) rfl
    (leftDerivedSheafExtendScalarsCompMap R S T Y) _
    (leftDerivedSheafExtendScalarsCompMap_app_comp_counit R S T Y)
    (leftDerivedSheafExtendScalarsCompMap R S T Z) _
    (leftDerivedSheafExtendScalarsCompMap_app_comp_counit R S T Z)
    (leftDerivedUpperStarExtendScalarsIso R S g).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit_expand R S g)
    (leftDerivedUpperStarExtendScalarsIso S T g).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso S T g).hom
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit_expand S T g)
    (leftDerivedUpperStarExtendScalarsIso R T g).hom
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R T g).hom
    (leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit_expand R T g)
    (Functor.mapHomotopyCategory_square_trans _ _ _ _ _
      (sheafExtendScalarsCompUpperStarIso_hom_app_trans (algebraMap R S) (algebraMap S T)
        (algebraMap R T) (IsScalarTower.algebraMap_eq R S T) g) _ _ _ _ _
      (fun _ ↦ rfl)
      (fun _ ↦ rfl)
      (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl))

variable (R S T) in
/-- **Transitivity of the base change map of derived scalar extension along `Rg_*`.** Along
`τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`, the base change map `Ψ_{R,T} (Rg_* N) ⟶ Rg_* (Ψ_{R,T} N)` is
the composite of the base change maps for `Ψ_{R,S}` and `Ψ_{S,T}`: it is the mate of the
commutation with `Lg^*`, which is transitive
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso_hom_trans`). -/
lemma rightDerivedLowerStarExtendScalarsMap_trans [IsNoetherianRing R] [IsNoetherianRing S]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    (leftDerivedSheafExtendScalarsCompMap R S T Y).app (R((g)_*[ModuleCat.{u + 1} R]).obj N) ≫
        (rightDerivedLowerStarExtendScalarsMap R T g).app N =
      L(sheafExtendScalars (algebraMap S T) Y).map
          ((rightDerivedLowerStarExtendScalarsMap R S g).app N) ≫
        (rightDerivedLowerStarExtendScalarsMap S T g).app
          (L(sheafExtendScalars (algebraMap R S) Z).obj N) ≫
        R((g)_*[ModuleCat.{u + 1} T]).map ((leftDerivedSheafExtendScalarsCompMap R S T Z).app N) :=
  app_comp_mateEquiv_app_of_whiskerRight_comp_eq (derivedUpperStarLowerStarAdjunction _ g)
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedUpperStarExtendScalarsIso R S g).hom
    (leftDerivedUpperStarExtendScalarsIso S T g).hom
    (leftDerivedUpperStarExtendScalarsIso R T g).hom _ _
    (leftDerivedUpperStarExtendScalarsIso_hom_trans R S T g) N

variable (R S T) in
/-- **Transitivity of the commutation of derived scalar extension with `j_!`.** Along
`τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`, the isomorphism `Ψ_{R,T} (j_! K) ≅ j_! (Ψ_{R,T} K)` is the
composite of the isomorphisms for `Ψ_{R,S}` and `Ψ_{S,T}`: the mates of their inverses are the
commutations with `Lj^*`, which are transitive
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso_hom_trans`). -/
lemma openImmersionLowerShriekExtendScalarsIso_hom_app_trans [IsNoetherianRing R]
    [IsNoetherianRing S] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))) :
    (leftDerivedSheafExtendScalarsCompMap R S T X).app
        (D((j)_!open[ModuleCat.{u + 1} R]).obj K) ≫
        (openImmersionLowerShriekExtendScalarsIso R T j).hom.app K =
      L(sheafExtendScalars (algebraMap S T) X).map
          ((openImmersionLowerShriekExtendScalarsIso R S j).hom.app K) ≫
        (openImmersionLowerShriekExtendScalarsIso S T j).hom.app
          (L(sheafExtendScalars (algebraMap R S) U).obj K) ≫
        D((j)_!open[ModuleCat.{u + 1} T]).map
          ((leftDerivedSheafExtendScalarsCompMap R S T U).app K) := by
  refine app_comp_hom_app_of_mateEquiv_inv
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} R) j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} S) j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} T) j)
    (openImmersionLowerShriekExtendScalarsIso R S j)
    (openImmersionLowerShriekExtendScalarsIso S T j)
    (openImmersionLowerShriekExtendScalarsIso R T j) _ _ ?_ K
  rw [mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv,
    mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv,
    mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv]
  exact whiskerLeft_comp_inv_eq_of_whiskerRight_comp_hom_eq
    (leftDerivedUpperStarExtendScalarsIso R S j) (leftDerivedUpperStarExtendScalarsIso S T j)
    (leftDerivedUpperStarExtendScalarsIso R T j) _ _
    (leftDerivedUpperStarExtendScalarsIso_hom_trans R S T j)

variable (R S T) in
/-- **Transitivity of the comparison for `Rf_!(c)`**, for an arbitrary compactification `c` of
`f`: along `τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`, the comparison
`Ψ_{R,T} (Rf_!(c) M) ⟶ Rf_!(c) (Ψ_{R,T} M)`
is the composite of the comparisons for `Ψ_{R,S}` and `Ψ_{S,T}`. -/
lemma rightDerivedLowerShriekOfCompactificationExtendScalarsMap_trans [IsNoetherianRing R]
    [IsNoetherianRing S] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    (leftDerivedSheafExtendScalarsCompMap R S T Y).app ((Rf_!(c)[ModuleCat.{u + 1} R]).obj M) ≫
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R T c).app M =
      L(sheafExtendScalars (algebraMap S T) Y).map
          ((rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app M) ≫
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap S T c).app
          (L(sheafExtendScalars (algebraMap R S) X).obj M) ≫
        (Rf_!(c)[ModuleCat.{u + 1} T]).map
          ((leftDerivedSheafExtendScalarsCompMap R S T X).app M) := by
  have h := (rightDerivedLowerStarExtendScalarsMap S T c.g).naturality
    ((openImmersionLowerShriekExtendScalarsIso R S c.i).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at h
  simp only [rightDerivedLowerShriekOfCompactificationExtendScalarsMap_app, Functor.map_comp,
    Category.assoc, Functor.comp_map, rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  rw [reassoc_of% (rightDerivedLowerStarExtendScalarsMap_trans R S T c.g
      (D((c.i)_!open[ModuleCat.{u + 1} R]).obj M)), reassoc_of% h, ← Functor.map_comp,
    openImmersionLowerShriekExtendScalarsIso_hom_app_trans R S T c.i M]
  simp only [Functor.map_comp]

variable [Finite R] [Finite S] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `lemma-sp-reduction--4`: **transitivity of the comparison for `Rf_!`**. For
`R → S → T` and every `M`, the comparison `b_{R,T}(M)` is the composite of `b_{R,S}`
and `b_{S,T}`, along `τ : Ψ_{S,T} ∘ Ψ_{R,S} ⟶ Ψ_{R,T}`:

`b_{R,T}(M) ∘ τ(Rf_! M) = Rf_!(τ(M)) ∘ b_{S,T}(Ψ_{R,S} M) ∘ Ψ_{S,T}(b_{R,S}(M))`.

Both comparisons are built through the compactification from the base change maps of the
extensions of scalars along `Rg_*` and from their commutation with `i_!`, and these are transitive
by associativity of the tensor product (`sheafExtendScalarsCompIso`). -/
theorem rightDerivedLowerShriekExtendScalarsMap_trans
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    (leftDerivedSheafExtendScalarsCompMap R S T Y).app ((R(f)_![ModuleCat.{u + 1} R]).obj M) ≫
        (rightDerivedLowerShriekExtendScalarsMap R T f).app M =
      (L(sheafExtendScalars (algebraMap S T) Y)).map
          ((rightDerivedLowerShriekExtendScalarsMap R S f).app M) ≫
        (rightDerivedLowerShriekExtendScalarsMap S T f).app
          ((L(sheafExtendScalars (algebraMap R S) X)).obj M) ≫
        (R(f)_![ModuleCat.{u + 1} T]).map
          ((leftDerivedSheafExtendScalarsCompMap R S T X).app M) :=
  rightDerivedLowerShriekOfCompactificationExtendScalarsMap_trans R S T _ M

end AlgebraicGeometry.ProEtale
