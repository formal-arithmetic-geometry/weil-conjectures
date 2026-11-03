/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Invertibility of the native positive Tate line

Source: Bhatt--Scholze, Section 6.8, and the root-line construction in
sk-def-sp-tate-twist (blueprint: lem-sf-native-tate-line-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem invertible_map
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    {M : A} (hM : IsInvertible M) : IsInvertible (F.obj M) := by
  obtain ⟨N, ⟨p⟩, ⟨q⟩⟩ := hM
  exact ⟨F.obj N,
    ⟨Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso p ≪≫ (Functor.Monoidal.εIso F).symm⟩,
    ⟨Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso q ≪≫ (Functor.Monoidal.εIso F).symm⟩⟩

private theorem invertible_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hC : ∀ i : C.I₀, Nonempty ((L((C.f i)^*⟦Λ⟧)).obj M ≅ 𝟙_ _)) :
    IsInvertible M := by
  let _ : BraidedCategory (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    (DerivedCategory.nonempty_braidedCategory _).some
  have hv : IsIso ((ihom.ev M).app (𝟙_ _)) := by
    apply isIso_of_forall_isIso_leftDerivedUpperStar_map C
    intro i
    have : WeaklyEtale (C.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ ⟨i⟩
    let F := L((C.f i)^*⟦Λ⟧)
    let _ := monoidal_leftDerivedUpperStar Λ (C.f i)
    obtain ⟨e⟩ := hC i
    have : (tensorLeft (F.obj M)).IsEquivalence := Functor.isEquivalence_of_iso
      (((tensoringLeft _).mapIso e ≪≫ leftUnitorNatIso _).symm)
    have : IsIso ((ihom.ev (F.obj M)).app (F.obj (𝟙_ _))) :=
      inferInstanceAs (IsIso ((ihom.adjunction (F.obj M)).counit.app (F.obj (𝟙_ _))))
    have := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale Λ (C.f i) M
    have : IsIso (Functor.LaxMonoidal.μ F M _ ≫ F.map ((ihom.ev M).app (𝟙_ _))) := by
      rw [← Functor.LaxMonoidal.ihomComparison_ev]
      infer_instance
    exact IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ F M _) _
  let _ := hv
  exact (isInvertible_iff_of_braided M).2 ⟨(ihom M).obj (𝟙_ _), ⟨asIso ((ihom.ev M).app (𝟙_ _))⟩⟩

private theorem monoidal_unit_iso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal] :
    Nonempty (F.obj (𝟙_ A) ≅ 𝟙_ B) := ⟨(Functor.Monoidal.εIso F).symm⟩

private theorem map_unit_triviality
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    (M : A) (h : Nonempty (M ≅ 𝟙_ A)) : Nonempty (F.obj M ≅ 𝟙_ B) := by
  obtain ⟨e⟩ := h
  exact ⟨F.mapIso e ≪≫ (Functor.Monoidal.εIso F).symm⟩

private theorem powers_local_unit
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    (L : ℕ → A) (M : A) (h₀ : L 0 = 𝟙_ A)
    (hₛ : ∀ d, L (d + 1) = L d ⊗ M) (hM : Nonempty (F.obj M ≅ 𝟙_ B))
    (d : ℕ) : Nonempty (F.obj (L d) ≅ 𝟙_ B) := by
  obtain ⟨e⟩ := hM
  induction d with
  | zero => simpa only [h₀] using monoidal_unit_iso F
  | succ d hd =>
    obtain ⟨ed⟩ := hd
    rw [hₛ]
    exact ⟨(Functor.Monoidal.μIso F _ _).symm ≪≫ tensorIso ed e ≪≫ λ_ _⟩

private theorem scalar_pull_unit
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : Nonempty ((upperStar Λ f).obj M ≅ 𝟙_ _)) :
    Nonempty ((upperStar Λ' f).obj
      ((Mod.extendScalars (coefficientMap a Y)).obj M) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := hM
  let H := Mod.extendScalars (coefficientMap a X)
  let _ := Mod.extendScalarsMonoidal (coefficientMap a X)
  obtain ⟨h⟩ := monoidal_unit_iso H
  exact ⟨(pullIso a f).symm.app M ≪≫ H.mapIso e ≪≫ h⟩

private theorem integral_cover_unit (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Nonempty (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) Y)).obj
          (tateModule Y ell) ≅ 𝟙_ _)) :
    Nonempty ((upperStar (Profinite.continuousMapRingObj.{u} ℤ_[ell]) f).obj
      (tateModule Y ell) ≅ 𝟙_ _) := by
  let R := Profinite.continuousMapRingObj.{u} ℤ_[ell]
  let G := Mod.extendScalars (condensedPullbackHom R f)
  exact map_unit_triviality G _ h

private theorem line_local_unit (ell : ℕ) [Fact ell.Prime]
    (c : PurityTransport.Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Nonempty ((upperStar (Profinite.continuousMapRingObj.{u} ℤ_[ell]) f).obj
      (tateModule Y ell) ≅ 𝟙_ _)) (d : ℕ) :
    Nonempty ((upperStar (c.obj ell) f).obj (c.line ell Y d) ≅ 𝟙_ _) := by
  have e := scalar_pull_unit (c.integralMap ell) f (tateModule Y ell) h
  exact powers_local_unit (upperStar (c.obj ell) f)
    (c.line ell Y) (c.firstLine ell Y) rfl (fun _ ↦ rfl) e d

/-- Positive root-tower Tate lines, including their degree-zero derived models
and any displayed isomorphic coefficient coordinates, are tensor invertible.
Source: Bhatt--Scholze, Section 6.8; blueprint sk-def-sp-tate-twist
(blueprint: lem-sf-native-tate-line-invertible).

Proof: a compatible primitive-root pro-etale cover trivializes the integral
Tate module. Cartesian coefficient extension transports this trivialization to
the first line over c, and the monoidal pullback comparison transports it to each
tensor power. Exact derived inverse image identifies the degree-zero model with
the degree-zero unit on every cover member. The closed evaluation into the unit
is an isomorphism there, since tensoring with a unit is an equivalence; the
internal-Hom comparison for weakly etale pullback carries this evaluation to the
local evaluation. Conservativity of the cover makes evaluation an isomorphism
globally. It exhibits the internal dual as a tensor inverse; symmetry gives
the inverse in the other order. Finally strong monoidal coefficient change
preserves both inverse isomorphisms. The zero ring and empty scheme are included. -/
theorem native_tateLine_isInvertible (ell : ℕ) [Fact ell.Prime]
    (Λ : ScalarSixRing.{u}) (c : PurityTransport.Coefficient ell)
    (e : c.bundled.{u} ell ≅ Λ) (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ) :
    IsInvertible (smoothTraceCoefficientLine ell Λ c e X d) := by
  have hInv : IsUnit (ell : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (ell : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : X.residueField x)
  obtain ⟨C, hC⟩ := tateModule_locally_trivial X ell hInv
  have hL : IsInvertible ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X d)) := by
    apply invertible_of_cover (c.obj ell) X C
    intro i
    obtain ⟨ei⟩ := line_local_unit ell c (C.f i) (integral_cover_unit ell (C.f i) (hC i)) d
    exact ⟨leftDerivedUpperStarSingleFunctorIso (c.obj ell) (C.f i) _ 0 ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso ei ≪≫
      DerivedCategory.singleFunctorObjUnitIso _⟩
  let _ := scalarSixChangeMonoidal e.hom X
  exact invertible_map (scalarSixChange e.hom X) hL

end AlgebraicGeometry.ProEtale.CondensedRing
