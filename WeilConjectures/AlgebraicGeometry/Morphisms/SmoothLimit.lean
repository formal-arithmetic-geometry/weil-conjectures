/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Smoothness descends to a stage of a limit

Let `{Dⱼ}` be a cofiltered system of affine Noetherian schemes with affine transition maps and
let `Y` be of finite presentation over a stage `Dᵢ`. If the base change of `Y` to `lim Dⱼ` is
smooth, then so is the base change of `Y` to some stage `Dⱼ` (EGA IV 17.7.8).

## Main statements

- `AlgebraicGeometry.Scheme.exists_smooth_pullback_snd_of_isLimit`
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

/-- **Smooth algebras over a filtered colimit of rings descend to a stage.** Let `R = colim Rⱼ`
be a filtered colimit of commutative rings and `B` a smooth `R`-algebra. Then there is a stage `j`
and a smooth `Rⱼ`-algebra `Bⱼ` with `B ≃ₐ[R] R ⊗[Rⱼ] Bⱼ`. -/
theorem Algebra.Smooth.exists_of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {s : Cocone F} (hs : IsColimit s)
    (B : Type u) [CommRing B] [Algebra s.pt B] [Algebra.Smooth s.pt B] :
    ∃ (j : J) (Bj : Type u) (_ : CommRing Bj) (_ : Algebra (F.obj j) Bj),
      Algebra.Smooth (F.obj j) Bj ∧
      letI : Algebra (F.obj j) s.pt := (s.ι.app j).hom.toAlgebra
      Nonempty (B ≃ₐ[s.pt] s.pt ⊗[F.obj j] Bj) := by
  classical
  let A : Type u := s.pt
  let : Algebra (ULift.{u} ℤ) A :=
    ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : ∀ i, Algebra (ULift.{u} ℤ) (F.obj i) := fun i ↦
    ((Int.castRingHom (F.obj i)).comp ULift.ringEquiv.toRingHom).toAlgebra
  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg (ULift.{u} ℤ) A B
  have : Algebra.FiniteType (ULift.{u} ℤ) A₀ := A₀.fg_iff_finiteType.mp hfg
  let R := CommRingCat.of (ULift.{u} ℤ)
  let α : (Functor.const J).obj R ⟶ F :=
    { app := fun i ↦ CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (F.obj i))
      naturality := by
        intro i k h
        ext ⟨x⟩
        change (x : F.obj k) = (F.map h).hom (x : F.obj i)
        simp }
  let j : R ⟶ CommRingCat.of A₀ := CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A₀)
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hj : j.hom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨i, g, _, hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R F α j s hs hj
      (CommRingCat.ofHom A₀.val.toRingHom) (by
        intro i
        ext ⟨x⟩
        change (x : A) = (s.ι.app i).hom (x : F.obj i)
        exact (map_intCast _ x).symm)
  let : Algebra A₀ (F.obj i) := g.hom.toAlgebra
  let : Algebra (F.obj i) A := (s.ι.app i).hom.toAlgebra
  have : IsScalarTower A₀ (F.obj i) A :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hg)
  refine ⟨i, F.obj i ⊗[A₀] B₀, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A₀ (F.obj i) A A B₀).symm⟩

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- **A smooth affine scheme over the limit has a smooth model at a stage.** Let `{Dⱼ}` be a
cofiltered system of affine schemes with affine transition maps and `g : X ⟶ lim Dⱼ` a smooth
morphism from an affine scheme. Then `g` is the base change of a smooth morphism from an affine
scheme to some stage `Dⱼ`. -/
theorem Scheme.exists_smooth_isPullback_of_isAffine {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [Smooth g] :
    ∃ (j : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj j) (h : X ⟶ Y),
      IsAffine Y ∧ Smooth p ∧ IsPullback h g p (c.π.app j) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ hc i₀
  have : IsAffine c.pt := isAffine_of_isAffineHom (c.π.app i₀)
  let s := Scheme.Γ.mapCocone c.op
  let hs : IsColimit s := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let : Algebra Γ(c.pt, ⊤) Γ(X, ⊤) := g.appTop.hom.toAlgebra
  have hsmooth : Algebra.Smooth Γ(c.pt, ⊤) Γ(X, ⊤) :=
    ((HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := g)).mp ‹_›).toAlgebra
  let : Algebra s.pt Γ(X, ⊤) := g.appTop.hom.toAlgebra
  have : Algebra.Smooth s.pt Γ(X, ⊤) := hsmooth
  obtain ⟨⟨j⟩, Bj, _, alg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_of_isColimit hs Γ(X, ⊤)
  let : Algebra Γ(D.obj j, ⊤) Bj := alg
  have : Algebra.Smooth Γ(D.obj j, ⊤) Bj := hsm
  let : Algebra Γ(D.obj j, ⊤) Γ(c.pt, ⊤) := (c.π.app j).appTop.hom.toAlgebra
  let e' : Γ(X, ⊤) ≃ₐ[Γ(c.pt, ⊤)] Γ(c.pt, ⊤) ⊗[Γ(D.obj j, ⊤)] Bj := e
  let φ : Γ(D.obj j, ⊤) ⟶ CommRingCat.of Bj := CommRingCat.ofHom (algebraMap Γ(D.obj j, ⊤) Bj)
  have : IsAffine (((Functor.const I).obj c.pt).obj j) := ‹IsAffine c.pt›
  have H := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(D.obj j, ⊤) Γ(c.pt, ⊤) Bj)).flip
  let e₁ : X ≅ Spec (CommRingCat.of (Γ(c.pt, ⊤) ⊗[Γ(D.obj j, ⊤)] Bj)) :=
    X.isoSpec ≪≫ Scheme.Spec.mapIso e'.symm.toRingEquiv.toCommRingCatIso.op
  refine ⟨j, Spec (CommRingCat.of Bj), Spec.map φ ≫ (D.obj j).isoSpec.inv,
    e₁.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom),
    inferInstance, ?_, ?_⟩
  · have : Smooth (Spec.map φ) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance
  · refine H.of_iso' e₁ (Iso.refl _) c.pt.isoSpec (D.obj j).isoSpec (by simp) ?_ (by simp) ?_
    · simp only [e₁, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
        Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp]
      rw [← Scheme.isoSpec_hom_naturality]
      congr 2
      ext x
      exact e'.symm.commutes x
    · exact (Scheme.isoSpec_hom_naturality (c.π.app j)).symm

/-- **Smoothness descends to a stage of a limit.** Let `{Dⱼ}` be a cofiltered system of affine
Noetherian schemes with affine transition maps, `c` a limit cone, and `p : Y ⟶ Dᵢ` of finite
presentation. If the base change `Y ×_{Dᵢ} lim Dⱼ ⟶ lim Dⱼ` is smooth, then so is
`Y ×_{Dᵢ} Dⱼ ⟶ Dⱼ` for some `j ⟶ i`. -/
theorem Scheme.exists_smooth_pullback_snd_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    [∀ i, IsNoetherian (D.obj i)] {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [Smooth (pullback.snd p (c.π.app i))] :
    ∃ (j : I) (f : j ⟶ i), Smooth (pullback.snd p (D.map f)) := by
  sorry

end AlgebraicGeometry
