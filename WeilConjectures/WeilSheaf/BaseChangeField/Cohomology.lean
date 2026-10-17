/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.WeilSheaf.BaseChangeField.Derived
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.BaseChangeField.GlobalSections
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# Cohomology under a finite extension of the base field

Let `k₀'/k₀` be an extension of finite fields of degree `r`, `X` a `k₀`-scheme of finite type
and `X' = X ×_{k₀} k₀'`. The cohomology `Hⁱ(X' ⊗ k̄', ℚ̄_ℓ)` of `X'` relative to `k₀'` is
`Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`, with the geometric Frobenius of `k₀'` acting as the `r`-th power `Fʳ` of
that of `k₀` (`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_of_iso`,
`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_baseChangeField`).

The identification `θ : X ×_{k₀} k̄ ≅ X' ×_{k₀'} k̄'` of the geometric fibers
(`AlgebraicGeometry.Scheme.Hom.geometricFiberBaseChangeIso`) carries the `r`-th power of the
geometric Galois Frobenius of `X` to that of `X'`. Transport along `θ`
(`AlgebraicGeometry.ProEtaleWeilSheaf.transport`) sends the constant Weil sheaf on `X` to that on
`X'` and commutes with the pushforwards to the base points, hence with their derived functors;
on global sections, the Frobenius of a transported Weil sheaf is the `r`-th power of the original
one.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

lemma forget_map_frobeniusPowIso_zero_hom (K : ProEtaleWeilSheaf k₀ l Y)
    (h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _) :
    (AdicSheaf.forget _).map (K.frobeniusPowIso 0).hom =
      (lowerStarCongr _ h).hom.app K.carrier.X ≫ (lowerStarId _ _).hom.app K.carrier.X := by
  rw [frobeniusPowIso_zero K h, Iso.trans_hom, Functor.map_comp]
  rfl

lemma forget_map_frobeniusPowIso_succ_hom (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ)
    (h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv) :
    (AdicSheaf.forget _).map (K.frobeniusPowIso (m + 1)).hom =
      (lowerStarCongr _ h).hom.app K.carrier.X ≫
        (lowerStarComp _ _ _).inv.app K.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom) ≫
        (AdicSheaf.forget _).map K.str.hom := by
  rw [frobeniusPowIso_succ K m h]
  simp only [Iso.trans_hom, Functor.map_comp]
  rfl

/-- The endomorphism of the global sections defined by the iterated Weil structure `φ_m` is the
`m`-th power of the Frobenius. -/
theorem globalSectionsStr_frobeniusPowIso (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ) :
    globalSectionsStr ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
        ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom) =
      @HPow.hPow (End ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X)) ℕ _ _
        (globalSectionsStr (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
          ((AdicSheaf.forget _).map K.str.hom)) m := by
  induction m with
  | zero =>
    have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ := by
      rw [pow_zero]; rfl
    rw [forget_map_frobeniusPowIso_zero_hom K h, globalSectionsStr_id, pow_zero]
    rfl
  | succ m ih =>
    have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    rw [forget_map_frobeniusPowIso_succ_hom K m h, globalSectionsStr_comp, ih, pow_succ',
      End.mul_def]

end ProEtaleWeilSheaf

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

lemma forget_map_adicLowerStarSquareIso_hom_app {Z Y Y' X : Scheme.{u}} {p : Z ⟶ Y}
    {q : Y ⟶ X} {p' : Z ⟶ Y'} {q' : Y' ⟶ X} (h : p ≫ q = p' ≫ q') (M : AdicSheaf l Z) :
    (AdicSheaf.forget X).map ((adicLowerStarSquareIso l h).hom.app M) =
      (lowerStarComp _ p q).hom.app M.X ≫ (lowerStarCongr _ h).hom.app M.X ≫
        (lowerStarComp _ p' q').inv.app M.X := by
  simp only [adicLowerStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rfl

/-- The `ℚ̄_ℓ`-linear maps induced by the powers of an endomorphism are the powers of the induced
map. -/
lemma toModuleCat_map_pow {M : WeilCoefficients.{u} l} (f : End M) (r : ℕ) :
    ((WeilCoefficients.toModuleCat l).map (f ^ r)).hom =
      ((WeilCoefficients.toModuleCat l).map f).hom ^ r := by
  induction r with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ r ih =>
    rw [pow_succ, pow_succ, End.mul_def, Functor.map_comp, ModuleCat.hom_comp, ih,
      Module.End.mul_eq_comp]

/-- An isomorphism `E` of `ℚ̄_ℓ`-modules intertwining automorphisms `Φ` and `Ψʳ` induces a linear
equivalence intertwining the induced automorphism of `Φ` with the `r`-th power of that of `Ψ`. -/
lemma linearEquivOfIso_apply_linearEquivOfIso {M N : WeilCoefficients.{u} l} (Φ : M ≅ M)
    (Ψ : N ≅ N) (E : M ≅ N) (r : ℕ)
    (h : Φ.hom ≫ E.hom = E.hom ≫ @HPow.hPow (End N) ℕ _ _ Ψ.hom r)
    (x : (WeilCoefficients.toModuleCat l).obj M) :
    WeilCoefficients.linearEquivOfIso E (WeilCoefficients.linearEquivOfIso Φ x) =
      ((WeilCoefficients.linearEquivOfIso Ψ).toLinearMap ^ r)
        (WeilCoefficients.linearEquivOfIso E x) := by
  have h' := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom x) h
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, toModuleCat_map_pow]
    at h'
  exact h'

end ProEtale

namespace WeilSheaf

open ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] [Fact (ringChar k₀' ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  {X' : Scheme.{u}} [X'.Over (Spec (CommRingCat.of k₀'))]
  [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀'))]
  [QuasiSeparated (X' ↘ Spec (CommRingCat.of k₀'))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀'))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber)
  (ψ : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (X' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
  (hψ : ψ.hom ≫ (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.hom =
    ((Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).hom ≫
      ψ.hom)
  (hsq : θ.hom ≫ Scheme.Hom.geometricFiberMap (X' ↘ Spec (CommRingCat.of k₀'))
      (comp_over (X' ↘ Spec (CommRingCat.of k₀')) _) =
    Scheme.Hom.geometricFiberMap (X ↘ Spec (CommRingCat.of k₀))
      (comp_over (X ↘ Spec (CommRingCat.of k₀)) _) ≫ ψ.hom)

section Unfold

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

lemma cohomology_eq (F : WeilSheaf k₀ l Y) (i : ℤ) :
    F.cohomology i = ((WeilComplex.homologySheaf i).obj
      ((WeilComplex.derivedLowerStar (Y ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj F))).globalSections :=
  rfl

lemma globalSections_frobenius_apply (F : WeilSheaf k₀ l Y) (x : F.globalSections.carrier) :
    F.globalSections.frobenius x = WeilCoefficients.linearEquivOfIso
      (((globalSectionsLowerStarIso _
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).app F.obj.carrier.X).symm ≪≫
        (Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso F.obj.str)) x :=
  rfl

lemma globalSections_frobeniusEnd (F : WeilSheaf k₀ l Y) :
    F.globalSections.frobeniusEnd = (WeilCoefficients.linearEquivOfIso
      (((globalSectionsLowerStarIso _
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).app F.obj.carrier.X).symm ≪≫
        (Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso F.obj.str))).toLinearMap :=
  rfl

end Unfold

include hθ hψ hsq in
/-- Let `θ : X̄ ≅ X̄'` and `ψ : Spec k̄ ≅ Spec k̄'` identify the geometric fibers of a `k₀`-scheme
`X` and of `Spec k₀` with those of a `k₀'`-scheme `X'` and of `Spec k₀'`, compatibly with the
structure morphisms, such that the geometric Galois Frobenii relative to `k₀'` correspond to the
`r`-th powers of those relative to `k₀`. Then `Hⁱ(X' ⊗ k̄', ℚ̄_ℓ) ≅ Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`, the geometric
Frobenius of `k₀'` corresponding to the `r`-th power of that of `k₀`. -/
theorem exists_linearEquiv_cohomology_adicConstant_of_iso (i : ℤ) :
    ∃ e : ((adicConstant k₀' l X').cohomology i).carrier ≃ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology i).carrier,
      ∀ x, e (((adicConstant k₀' l X').cohomology i).frobenius x) =
        (((adicConstant k₀ l X).cohomology i).frobeniusEnd ^ r) (e x) := by
  rw [cohomology_eq, cohomology_eq]
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  let TX := transport (l := l) θ r hθ
  let Tp := transport (l := l) ψ r hψ
  let L := ProEtaleWeilSheaf.lowerStar k₀ l (X ↘ Spec (CommRingCat.of k₀))
  let L' := ProEtaleWeilSheaf.lowerStar k₀' l (X' ↘ Spec (CommRingCat.of k₀'))
  let Q := (DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
    (ProEtaleWeilSheaf.adicConstant k₀ l X)
  let Q' := (DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀' l X') 0).obj
    (ProEtaleWeilSheaf.adicConstant k₀' l X')
  let M := L.rightDerivedFunctor.obj Q
  let M' := L'.rightDerivedFunctor.obj Q'
  let N := (DerivedCategory.homologyFunctor _ i).obj M
  let N' := (DerivedCategory.homologyFunctor _ i).obj M'
  let ε : TX ⋙ IsoAlgebra.forget _ ≅ IsoAlgebra.forget _ ⋙ (θ.hom)_*ᵃ[l] :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans
      (Category.id_comp _).symm)
  let iso₁ : Q' ≅ TX.mapDerivedCategory.obj Q :=
    (DerivedCategory.singleFunctor _ 0).mapIso (adicConstantTransportIso θ r hθ) ≪≫
      ((TX.mapDerivedCategorySingleFunctor 0).app _).symm
  let iso₂ : M' ≅ Tp.mapDerivedCategory.obj M :=
    L'.rightDerivedFunctor.mapIso iso₁ ≪≫
      ((IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIso TX ε
        (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l
          (X' ↘ Spec (CommRingCat.of k₀')) (comp_over _ _))).app Q).symm ≪≫
      (Functor.rightDerivedFunctorNatIso
        (transportLowerStarIso θ r hθ ψ hψ _ _ hsq)).app Q ≪≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso L Tp).app Q
  let J : N' ≅ Tp.obj N :=
    (DerivedCategory.homologyFunctor _ i).mapIso iso₂ ≪≫
      ((Tp.mapDerivedCategoryHomologyFunctorIso i).app M).symm
  let E : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj N'.carrier.X ≅
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj N.carrier.X :=
    (Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso ((IsoAlgebra.forget _).mapIso J)) ≪≫
      (globalSectionsLowerStarIso _ ψ.hom).app N.carrier.X
  refine ⟨WeilCoefficients.linearEquivOfIso E, fun x ↦ ?_⟩
  rw [globalSections_frobenius_apply, globalSections_frobeniusEnd]
  refine ProEtale.linearEquivOfIso_apply_linearEquivOfIso _ _ E r ?_ x
  change globalSectionsStr _ ((AdicSheaf.forget _).map N'.str.hom) ≫ E.hom =
    E.hom ≫ @HPow.hPow (End _) ℕ _ _ (globalSectionsStr _ ((AdicSheaf.forget _).map N.str.hom)) r
  rw [← globalSectionsStr_frobeniusPowIso N r]
  have hf : ((Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.inv)_*[
      WeilCoefficients.{u} l].map ((AdicSheaf.forget _).map J.hom.hom.f) ≫
        (AdicSheaf.forget _).map (Tp.obj N).str.hom =
      (AdicSheaf.forget _).map N'.str.hom ≫ (AdicSheaf.forget _).map J.hom.hom.f := by
    have := congrArg (AdicSheaf.forget _).map J.hom.hom.h
    rw [Functor.map_comp, Functor.map_comp] at this
    exact this
  have nat := globalSectionsStr_naturality _ ((AdicSheaf.forget _).map J.hom.hom.f) hf
  have tr := globalSectionsStr_transport ψ.hom _ _ (hom_comp_geometricGaloisFrobenius_inv ψ r hψ)
    ((AdicSheaf.forget _).map (N.frobeniusPowIso r).hom)
  have hstr : (AdicSheaf.forget _).map (Tp.obj N).str.hom =
      (lowerStarComp _ _ _).hom.app N.carrier.X ≫
        (lowerStarCongr _ (hom_comp_geometricGaloisFrobenius_inv ψ r hψ)).hom.app N.carrier.X ≫
        (lowerStarComp _ _ _).inv.app N.carrier.X ≫
        (ψ.hom)_*[_].map ((AdicSheaf.forget _).map (N.frobeniusPowIso r).hom) := by
    rw [transport_obj_str, Iso.trans_hom, Functor.map_comp, Iso.app_hom, transportCommIso_eq,
      forget_map_adicLowerStarSquareIso_hom_app, Category.assoc, Category.assoc]
    rfl
  rw [hstr] at nat
  simp only [E, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, IsoAlgebra.forget_map]
  rw [← reassoc_of% nat, tr, Category.assoc]

omit [Finite k₀'] [Fact (ringChar k₀' ≠ l)] [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀'))]
  [QuasiSeparated (X' ↘ Spec (CommRingCat.of k₀'))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀'))] in
/-- Blueprint `sk-def-weil` (Frobenius-operator convention, `def-weil-frobenius-detailed`): for a
finite extension `k₀'/k₀` of degree `r`, the cohomology `Hⁱ((X ×_{k₀} k₀') ⊗ k̄', ℚ̄_ℓ)` of the
base change is `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`, the geometric Frobenius of `k₀'` corresponding to the `r`-th
power of that of `k₀`. -/
theorem exists_linearEquiv_cohomology_adicConstant_baseChangeField [Finite k₀']
    [Algebra k₀ k₀'] [Fact (ringChar k₀' ≠ l)]
    [QuasiCompact (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀'))]
    [QuasiSeparated (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀'))] (i : ℤ) :
    ∃ e : ((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).carrier ≃ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology i).carrier,
      ∀ x, e (((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).frobenius x) =
        (((adicConstant k₀ l X).cohomology i).frobeniusEnd ^ Module.finrank k₀ k₀') (e x) := by
  let := Fintype.ofFinite k₀
  let := Fintype.ofFinite k₀'
  have hr : Nat.card k₀' = Nat.card k₀ ^ Module.finrank k₀ k₀' := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := k₀) (V := k₀')]
  have hg : IsPullback (pullback.fst _ _) (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀'))
      (X ↘ Spec (CommRingCat.of k₀)) (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))) :=
    IsPullback.of_hasPullback _ _
  have hgB : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀')))
      (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀'))
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))) :=
    have : IsIso (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀')) :=
      inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_vert_isIso ⟨rfl⟩
  exact exists_linearEquiv_cohomology_adicConstant_of_iso
    (Scheme.Hom.geometricFiberBaseChangeIso hg) (Scheme.Hom.geometricFiberBaseChangeIso hgB) _
    (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hg _ hr)
    (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hgB _ hr)
    (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricFiberMap hg hgB _ _
      pullback.condition.symm) i

end WeilSheaf

end AlgebraicGeometry
