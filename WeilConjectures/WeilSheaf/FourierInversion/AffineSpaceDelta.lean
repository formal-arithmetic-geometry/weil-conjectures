/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Delta
public import WeilConjectures.WeilSheaf.WeilAffineSpaceTrace
public import WeilConjectures.WeilSheaf.FourierFirstFormula
public import WeilConjectures.WeilSheaf.ArtinSchreierMul
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.OpenClosedTriangle

/-!
# Fourier inversion: the delta kernel on a trivial vector bundle

Let `h = (h_k)` be a family of functions on a `k₀`-scheme `X`, viewed as a morphism
`X ⟶ 𝔸ⁿ`, with zero locus `i : Z ⟶ X`, and let `π : Y ⟶ X` be the trivial vector bundle of
rank `n` with fibre coordinates `s = (s_k)`. For a nontrivial additive character `ψ`,

`Rπ₀!(ℒ_ψ(∑ₖ hₖ sₖ) ⊗ π^* P) ≅ Ri₀!((i^* P)(-n)[-2n])`

naturally in the Weil complex `P` on `X`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_sum`).
This is the key step of Fourier inversion on an affine space of arbitrary rank.

## Implementation details

The statement is first proved for the standard bundle `𝔸ⁿ_X ⟶ X`, by induction on the finite
coordinate type. For the empty type both `π` and `i` are isomorphisms. In the inductive step for
`Option m`, the bundle `𝔸^{Option m}_X` is the trivial line bundle over `𝔸ᵐ_X` with fibre
coordinate `s_none`; the rank-one delta kernel
`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul`
integrates out that coordinate and cuts down to the zero locus `Z₀` of `h_none`, over which the
induction hypothesis applies to the remaining coordinates. Reindexing the coordinates and passing
from the standard bundle to an arbitrary trivial one are both isomorphisms over `X`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

open AffineSpace

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

set_option hygiene false in
/-- The base `Spec k₀`. -/
local notation "S₀" => Spec (CommRingCat.of k₀)

/-- Tensoring with `ℒ_ψ(a)` and then with `ℒ_ψ(b)` is tensoring with `ℒ_ψ(a + b)`. -/
theorem nonempty_iso_tensorLisse_artinSchreierOf_add {X : Scheme.{u}} [X.Over S₀]
    [LocallyOfFiniteType (X ↘ S₀)] (ψ : AddChar k₀ (PadicAlgCl l)) (a b : Γ(X, ⊤)) :
    Nonempty (tensorLisse (artinSchreierOf ψ a) (isLisse_artinSchreierOf ψ a) ⋙
        tensorLisse (artinSchreierOf ψ b) (isLisse_artinSchreierOf ψ b) ≅
      tensorLisse (artinSchreierOf ψ (a + b)) (isLisse_artinSchreierOf ψ (a + b))) := by
  obtain ⟨eComp⟩ := nonempty_iso_tensorLisse_comp (artinSchreierOf ψ b) (artinSchreierOf ψ a)
    (isLisse_artinSchreierOf ψ b) (isLisse_artinSchreierOf ψ a)
  obtain ⟨eMul⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ b a
  obtain ⟨eT⟩ := nonempty_iso_tensorLisse_of_iso
    (eMul ≪≫ eqToIso (congrArg (artinSchreierOf ψ) (add_comm b a)))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ b).dual
      (isLisse_artinSchreierOf ψ a))
    (isLisse_artinSchreierOf ψ (a + b))
  exact ⟨eComp ≪≫ eT⟩

/-- An isomorphism `E : Y ⟶ Y'` over `X` identifies the integral along `Y' ⟶ X` of an
Artin–Schreier kernel `ℒ_ψ(φ)` with the integral along `Y ⟶ X` of `ℒ_ψ(E^* φ)`. -/
theorem nonempty_iso_upperStar_tensorLisse_derivedLowerShriek_of_isIso
    (ψ : AddChar k₀ (PadicAlgCl l)) {X Y Y' : Scheme.{u}} [X.Over S₀] [Y.Over S₀] [Y'.Over S₀]
    (π : Y ⟶ X) (π' : Y' ⟶ X) (E : Y ⟶ Y') [IsIso E] [π.IsOver S₀] [π'.IsOver S₀]
    [E.IsOver S₀] [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π']
    [LocallyOfFiniteType π'] [QuasiCompact π'] [LocallyOfFiniteType (X ↘ S₀)]
    [QuasiCompact (X ↘ S₀)] [QuasiSeparated (X ↘ S₀)] [LocallyOfFiniteType (Y ↘ S₀)]
    [LocallyOfFiniteType (Y' ↘ S₀)] (hE : E ≫ π' = π) (φ : Γ(Y', ⊤)) :
    Nonempty (upperStar π' ⋙ tensorLisse (artinSchreierOf ψ φ) (isLisse_artinSchreierOf ψ φ) ⋙
        derivedLowerShriek k₀ l π' ≅
      upperStar π ⋙ tensorLisse (artinSchreierOf ψ (E.appTop φ))
          (isLisse_artinSchreierOf ψ _) ⋙ derivedLowerShriek k₀ l π) := by
  have : QuasiCompact (Y' ↘ S₀) := by rw [← comp_over π' S₀]; infer_instance
  have : QuasiSeparated (Y' ↘ S₀) := by rw [← comp_over π' S₀]; infer_instance
  obtain ⟨eId⟩ := nonempty_iso_upperStar_comp_derivedLowerShriek_of_isIso (k₀ := k₀) (l := l) E
  obtain ⟨eD⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) E π'
  obtain ⟨eT⟩ := nonempty_iso_tensorLisse_comp_upperStar E (artinSchreierOf ψ φ)
    (isLisse_artinSchreierOf ψ φ)
  obtain ⟨a⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) E ψ φ
  obtain ⟨eA⟩ := nonempty_iso_tensorLisse_of_iso a
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ φ))
    (isLisse_artinSchreierOf ψ _)
  let T := tensorLisse (artinSchreierOf ψ φ) (isLisse_artinSchreierOf ψ φ)
  let T' := tensorLisse (artinSchreierOf ψ (E.appTop φ)) (isLisse_artinSchreierOf ψ _)
  let D := derivedLowerShriek k₀ l E
  let D' := derivedLowerShriek k₀ l π'
  have s₁ : upperStar π' ⋙ T ⋙ D' ≅ upperStar π' ⋙ T ⋙ (upperStar E ⋙ D) ⋙ D' :=
    Functor.isoWhiskerLeft (upperStar π') (Functor.isoWhiskerLeft T
      ((Functor.leftUnitor D').symm ≪≫ Functor.isoWhiskerRight eId.symm D'))
  have s₂ : upperStar π' ⋙ T ⋙ (upperStar E ⋙ D) ⋙ D' ≅
      upperStar π' ⋙ (upperStar E ⋙ T') ⋙ D ⋙ D' :=
    Functor.isoWhiskerLeft (upperStar π')
      (Functor.isoWhiskerRight (eT ≪≫ Functor.isoWhiskerLeft (upperStar E) eA) (D ⋙ D'))
  have s₃ : upperStar π' ⋙ (upperStar E ⋙ T') ⋙ D ⋙ D' ≅ upperStar π ⋙ T' ⋙ D ⋙ D' :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((upperStarCompIso E π').symm ≪≫ upperStarCongrIso hE)
        (T' ⋙ D ⋙ D')
  have s₄ : upperStar π ⋙ T' ⋙ D ⋙ D' ≅ upperStar π ⋙ T' ⋙ derivedLowerShriek k₀ l π :=
    Functor.isoWhiskerLeft (upperStar π) (Functor.isoWhiskerLeft T'
      (eD.symm ≪≫ derivedLowerShriekIsoOfEq hE))
  exact ⟨s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄⟩

variable (k₀ l) in
/-- The delta kernel statement for the standard bundle `𝔸ⁿ_X ⟶ X` with coordinates `coord X k`,
for all `X`, `h` and zero loci `i`. -/
private def DeltaClaim (ψ : AddChar k₀ (PadicAlgCl l)) (n : Type u) [Fintype n] : Prop :=
  ∀ (X Z : Scheme.{u}) [X.Over S₀] [Z.Over S₀] [IsSeparated (X ↘ S₀)]
    [LocallyOfFiniteType (X ↘ S₀)] [QuasiCompact (X ↘ S₀)] [LocallyOfFiniteType (Z ↘ S₀)]
    (h : X ⟶ 𝔸(n; S₀)) [h.IsOver S₀] (i : Z ⟶ X) [i.IsOver S₀] [IsClosedImmersion i]
    (_ : IsPullback (Z ↘ S₀) i (zeroSection n S₀) h),
    letI : (𝔸(n; X)).Over S₀ := ⟨(𝔸(n; X) ↘ X) ≫ (X ↘ S₀)⟩
    haveI : (𝔸(n; X) ↘ X).IsOver S₀ := ⟨rfl⟩
    haveI : LocallyOfFiniteType (𝔸(n; X) ↘ S₀) :=
      inferInstanceAs (LocallyOfFiniteType ((𝔸(n; X) ↘ X) ≫ (X ↘ S₀)))
    Nonempty (upperStar (𝔸(n; X) ↘ X) ⋙
        tensorLisse (artinSchreierOf ψ
          (∑ k, (𝔸(n; X) ↘ X).appTop (h.appTop (coord S₀ k)) * coord X k))
          (isLisse_artinSchreierOf ψ _) ⋙ derivedLowerShriek k₀ l (𝔸(n; X) ↘ X) ≅
      upperStar i ⋙ tateTwist k₀ l Z (-(Fintype.card n : ℤ)) ⋙
        shiftFunctor _ (-(2 * (Fintype.card n : ℤ))) ⋙ derivedLowerShriek k₀ l i)

/-- The delta kernel statement in rank zero. -/
private theorem deltaClaim_pempty (ψ : AddChar k₀ (PadicAlgCl l)) :
    DeltaClaim k₀ l ψ PEmpty.{u + 1} := by
  intro X Z _ _ _ _ _ _ h _ i _ _ hi
  let : (𝔸(PEmpty.{u + 1}; X)).Over S₀ := ⟨(𝔸(PEmpty.{u + 1}; X) ↘ X) ≫ (X ↘ S₀)⟩
  have : (𝔸(PEmpty.{u + 1}; X) ↘ X).IsOver S₀ := ⟨rfl⟩
  have : LocallyOfFiniteType (𝔸(PEmpty.{u + 1}; X) ↘ S₀) :=
    inferInstanceAs (LocallyOfFiniteType ((𝔸(PEmpty.{u + 1}; X) ↘ X) ≫ (X ↘ S₀)))
  have : QuasiCompact (Z ↘ S₀) := by rw [← comp_over i S₀]; infer_instance
  have : QuasiSeparated (Z ↘ S₀) := by rw [← comp_over i S₀]; infer_instance
  have hΦ : (∑ k : PEmpty.{u + 1}, (𝔸(PEmpty.{u + 1}; X) ↘ X).appTop (h.appTop (coord S₀ k)) *
      coord X k) = 0 := Fintype.sum_empty _
  have : IsIso (zeroSection PEmpty.{u + 1} S₀ ≫ 𝔸(PEmpty.{u + 1}; S₀) ↘ S₀) := by
    rw [zeroSection_over]; infer_instance
  have : IsIso (zeroSection PEmpty.{u + 1} S₀) :=
    IsIso.of_isIso_comp_right _ (𝔸(PEmpty.{u + 1}; S₀) ↘ S₀)
  have : IsIso i := hi.isIso_snd_of_isIso
  obtain ⟨eπ⟩ := nonempty_iso_upperStar_comp_derivedLowerShriek_of_isIso (k₀ := k₀) (l := l)
    (𝔸(PEmpty.{u + 1}; X) ↘ X)
  obtain ⟨ei⟩ := nonempty_iso_upperStar_comp_derivedLowerShriek_of_isIso (k₀ := k₀) (l := l) i
  obtain ⟨a₀⟩ := nonempty_iso_artinSchreierOf_zero (k₀ := k₀) (l := l)
    (X := 𝔸(PEmpty.{u + 1}; X)) ψ
  obtain ⟨t₀⟩ := nonempty_iso_tensorLisse_of_iso
    (eqToIso (congrArg (artinSchreierOf ψ) hΦ) ≪≫ a₀) (isLisse_artinSchreierOf ψ _)
    (WeilSheaf.isLisse_adicConstant k₀ l _)
  obtain ⟨t₁⟩ := nonempty_iso_tensorLisse_adicConstant (k₀ := k₀) (l := l)
    (X := 𝔸(PEmpty.{u + 1}; X))
  obtain ⟨tw⟩ := nonempty_iso_tensorLisse_adicConstant (k₀ := k₀) (l := l) (X := Z)
  have tw₀ : tateTwist k₀ l Z 0 ≅ 𝟭 _ := tw
  simp only [Fintype.card_pempty, Nat.cast_zero, neg_zero, mul_zero]
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (t₀ ≪≫ t₁) _ ≪≫
      Functor.leftUnitor _) ≪≫ eπ ≪≫ ei.symm ≪≫
    Functor.isoWhiskerLeft (upperStar i) (Functor.isoWhiskerRight tw₀ _ ≪≫
      Functor.leftUnitor _ ≪≫ Functor.isoWhiskerRight (shiftFunctorZero _ ℤ) _ ≪≫
        Functor.leftUnitor _).symm⟩

/-- The delta kernel statement is invariant under reindexing the coordinates. -/
private theorem deltaClaim_of_equiv (ψ : AddChar k₀ (PadicAlgCl l)) {α β : Type u} [Fintype α]
    [Fintype β] (e : α ≃ β) (ih : DeltaClaim k₀ l ψ α) : DeltaClaim k₀ l ψ β := by
  intro X Z _ _ _ _ _ _ h _ i _ _ hi
  let pα := 𝔸(α; X) ↘ X
  let pβ := 𝔸(β; X) ↘ X
  let : (𝔸(α; X)).Over S₀ := ⟨pα ≫ X ↘ S₀⟩
  let : (𝔸(β; X)).Over S₀ := ⟨pβ ≫ X ↘ S₀⟩
  have : pα.IsOver S₀ := ⟨rfl⟩
  have : pβ.IsOver S₀ := ⟨rfl⟩
  have : LocallyOfFiniteType (𝔸(α; X) ↘ S₀) :=
    inferInstanceAs (LocallyOfFiniteType (pα ≫ X ↘ S₀))
  have : LocallyOfFiniteType (𝔸(β; X) ↘ S₀) :=
    inferInstanceAs (LocallyOfFiniteType (pβ ≫ X ↘ S₀))
  let R := reindex e S₀
  have : R.IsOver S₀ := ⟨reindex_over _ _⟩
  have : IsIso R := (reindexIso (S := S₀) e).isIso_hom
  have hi' : IsPullback (Z ↘ S₀) i (zeroSection α S₀) (h ≫ R) := by
    have sq : IsPullback (zeroSection β S₀) (𝟙 S₀) R (zeroSection α S₀) :=
      IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, zeroSection_comp_reindex]⟩
    simpa using (hi.flip.paste_vert sq).flip
  obtain ⟨eα⟩ := ih X Z (h ≫ R) i hi'
  let E := reindex e.symm X
  have hE : E ≫ pβ = pα := reindex_over _ X
  have : E.IsOver S₀ := ⟨by
    change E ≫ (pβ ≫ X ↘ S₀) = pα ≫ X ↘ S₀
    rw [← Category.assoc, hE]⟩
  have : IsIso E := (reindexIso (S := X) e.symm).isIso_hom
  obtain ⟨eT⟩ := nonempty_iso_upperStar_tensorLisse_derivedLowerShriek_of_isIso ψ pα pβ E hE
    (∑ k, pβ.appTop (h.appTop (coord S₀ k)) * coord X k)
  have hΦ : E.appTop (∑ k, pβ.appTop (h.appTop (coord S₀ k)) * coord X k) =
      ∑ k, pα.appTop ((h ≫ R).appTop (coord S₀ k)) * coord X k := by
    rw [map_sum, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hE]
    simp [E, R]
  have hc : (Fintype.card α : ℤ) = Fintype.card β := by rw [Fintype.card_congr e]
  rw [hΦ] at eT
  rw [hc] at eα
  exact ⟨eT ≪≫ eα⟩

/-- The bookkeeping of the inductive step: the composite of the natural isomorphisms used in
`deltaClaim_option`, for abstract functors. -/
private theorem nonempty_iso_of_optionStep {CX CY CB CZ₀ CZ₁ CZ : Type*} [Category CX]
    [Category CY] [Category CB] [Category CZ₀] [Category CZ₁] [Category CZ]
    {Uπ : CX ⥤ CY} {TΦ : CY ⥤ CY} {Dπ : CY ⥤ CX} {Up : CX ⥤ CB} {Uq : CB ⥤ CY}
    {Tq TA : CY ⥤ CY} {Dq : CY ⥤ CB} {Dp : CB ⥤ CX} {T' : CB ⥤ CB} {Ui₁ : CB ⥤ CZ₁}
    {tw₁ sh₁ T₁ : CZ₁ ⥤ CZ₁} {Di₁ : CZ₁ ⥤ CB} {Uj₀ : CX ⥤ CZ₀} {Up₁ : CZ₀ ⥤ CZ₁}
    {Dp₁ : CZ₁ ⥤ CZ₀} {Dj₀ : CZ₀ ⥤ CX} {tw₀ sh₀ : CZ₀ ⥤ CZ₀} {Ui' : CZ₀ ⥤ CZ}
    {twm shm twZ shZ tw sh : CZ ⥤ CZ} {Di' : CZ ⥤ CZ₀} {Ui : CX ⥤ CZ} {Di : CZ ⥤ CX}
    (uπ : Uπ ≅ Up ⋙ Uq) (dπ : Dπ ≅ Dq ⋙ Dp) (tΦ : TΦ ≅ Tq ⋙ TA) (eTq : T' ⋙ Uq ≅ Uq ⋙ Tq)
    (e₁ : Uq ⋙ TA ⋙ Dq ≅ Ui₁ ⋙ tw₁ ⋙ sh₁ ⋙ Di₁) (eTi₁ : T' ⋙ Ui₁ ≅ Ui₁ ⋙ T₁)
    (uI : Up ⋙ Ui₁ ≅ Uj₀ ⋙ Up₁) (dI : Di₁ ⋙ Dp ≅ Dp₁ ⋙ Dj₀) (s₁ : sh₁ ⋙ Dp₁ ≅ Dp₁ ⋙ sh₀)
    (t₁ : tw₁ ⋙ Dp₁ ≅ Dp₁ ⋙ tw₀) (e₂ : Up₁ ⋙ T₁ ⋙ Dp₁ ≅ Ui' ⋙ twm ⋙ shm ⋙ Di')
    (t' : twZ ⋙ Di' ≅ Di' ⋙ tw₀) (s' : shZ ⋙ Di' ≅ Di' ⋙ sh₀) (cs : shm ⋙ twZ ≅ twZ ⋙ shm)
    (ta : twm ⋙ twZ ≅ tw) (sa : shm ⋙ shZ ≅ sh) (ui : Uj₀ ⋙ Ui' ≅ Ui)
    (di : Di' ⋙ Dj₀ ≅ Di) :
    Nonempty (Uπ ⋙ TΦ ⋙ Dπ ≅ Ui ⋙ tw ⋙ sh ⋙ Di) := by
  have c₁ : Uπ ⋙ TΦ ⋙ Dπ ≅ Up ⋙ (Uq ⋙ Tq) ⋙ TA ⋙ Dq ⋙ Dp :=
    Functor.isoWhiskerRight uπ _ ≪≫ Functor.isoWhiskerLeft (Up ⋙ Uq)
      (Functor.isoWhiskerRight tΦ Dπ ≪≫ Functor.isoWhiskerLeft (Tq ⋙ TA) dπ)
  have c₂ : Up ⋙ (Uq ⋙ Tq) ⋙ TA ⋙ Dq ⋙ Dp ≅ (Up ⋙ T') ⋙ (Uq ⋙ TA ⋙ Dq) ⋙ Dp :=
    Functor.isoWhiskerLeft Up (Functor.isoWhiskerRight eTq.symm (TA ⋙ Dq ⋙ Dp))
  have c₃ : (Up ⋙ T') ⋙ (Uq ⋙ TA ⋙ Dq) ⋙ Dp ≅ (Up ⋙ T' ⋙ Ui₁) ⋙ tw₁ ⋙ sh₁ ⋙ Di₁ ⋙ Dp :=
    Functor.isoWhiskerLeft (Up ⋙ T') (Functor.isoWhiskerRight e₁ Dp)
  have c₄ : (Up ⋙ T' ⋙ Ui₁) ⋙ tw₁ ⋙ sh₁ ⋙ Di₁ ⋙ Dp ≅
      (Uj₀ ⋙ Up₁ ⋙ T₁) ⋙ tw₁ ⋙ sh₁ ⋙ Dp₁ ⋙ Dj₀ :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft Up eTi₁ ≪≫
        Functor.isoWhiskerRight uI T₁) _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft tw₁ (Functor.isoWhiskerLeft sh₁ dI))
  have c₅ : (Uj₀ ⋙ Up₁ ⋙ T₁) ⋙ tw₁ ⋙ sh₁ ⋙ Dp₁ ⋙ Dj₀ ≅
      Uj₀ ⋙ (Up₁ ⋙ T₁ ⋙ Dp₁) ⋙ tw₀ ⋙ sh₀ ⋙ Dj₀ :=
    Functor.isoWhiskerLeft (Uj₀ ⋙ Up₁ ⋙ T₁)
      (Functor.isoWhiskerLeft tw₁ (Functor.isoWhiskerRight s₁ Dj₀) ≪≫
        Functor.isoWhiskerRight t₁ (sh₀ ⋙ Dj₀))
  have c₆ : Uj₀ ⋙ (Up₁ ⋙ T₁ ⋙ Dp₁) ⋙ tw₀ ⋙ sh₀ ⋙ Dj₀ ≅
      Uj₀ ⋙ Ui' ⋙ twm ⋙ shm ⋙ (Di' ⋙ tw₀ ⋙ sh₀) ⋙ Dj₀ :=
    Functor.isoWhiskerLeft Uj₀ (Functor.isoWhiskerRight e₂ (tw₀ ⋙ sh₀ ⋙ Dj₀))
  have c₇ : Uj₀ ⋙ Ui' ⋙ twm ⋙ shm ⋙ (Di' ⋙ tw₀ ⋙ sh₀) ⋙ Dj₀ ≅
      Uj₀ ⋙ Ui' ⋙ twm ⋙ (shm ⋙ twZ) ⋙ shZ ⋙ Di' ⋙ Dj₀ :=
    Functor.isoWhiskerLeft (Uj₀ ⋙ Ui' ⋙ twm ⋙ shm)
      (Functor.isoWhiskerRight
        ((Functor.isoWhiskerLeft twZ s' ≪≫ Functor.isoWhiskerRight t' sh₀).symm) Dj₀)
  have c₈ : Uj₀ ⋙ Ui' ⋙ twm ⋙ (shm ⋙ twZ) ⋙ shZ ⋙ Di' ⋙ Dj₀ ≅ Ui ⋙ tw ⋙ sh ⋙ Di :=
    Functor.isoWhiskerRight ui (twm ⋙ (shm ⋙ twZ) ⋙ shZ ⋙ Di' ⋙ Dj₀) ≪≫
      Functor.isoWhiskerLeft Ui
      (Functor.isoWhiskerLeft twm (Functor.isoWhiskerRight cs (shZ ⋙ Di' ⋙ Dj₀)) ≪≫
        Functor.isoWhiskerRight ta (shm ⋙ shZ ⋙ Di' ⋙ Dj₀) ≪≫
        Functor.isoWhiskerLeft tw (Functor.isoWhiskerRight sa (Di' ⋙ Dj₀) ≪≫
          Functor.isoWhiskerLeft sh di))
  exact ⟨c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ c₄ ≪≫ c₅ ≪≫ c₆ ≪≫ c₇ ≪≫ c₈⟩

/-- The inductive step: the delta kernel statement for `m` implies it for `Option m`. -/
private theorem deltaClaim_option (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) (m : Type u)
    [Fintype m] (ih : DeltaClaim k₀ l ψ m) : DeltaClaim k₀ l ψ (Option m) := by
  intro X Z _ _ _ _ _ _ h _ i _ _ hi
  -- the standard bundles `𝔸^{Option m}_X ⟶ 𝔸ᵐ_X ⟶ X`
  let p := 𝔸(m; X) ↘ X
  let π := 𝔸(Option m; X) ↘ X
  let q : 𝔸(Option m; X) ⟶ 𝔸(m; X) := reindex (Option.some : m → Option m) X
  let : (𝔸(m; X)).Over S₀ := ⟨p ≫ X ↘ S₀⟩
  let : (𝔸(Option m; X)).Over S₀ := ⟨π ≫ X ↘ S₀⟩
  have : p.IsOver S₀ := ⟨rfl⟩
  have : π.IsOver S₀ := ⟨rfl⟩
  have hqp : q ≫ p = π := reindex_over _ X
  have : q.IsOver S₀ := ⟨by
    change q ≫ p ≫ X ↘ S₀ = π ≫ X ↘ S₀
    rw [← Category.assoc, hqp]⟩
  have : LocallyOfFiniteType (𝔸(m; X) ↘ S₀) := inferInstanceAs (LocallyOfFiniteType (p ≫ X ↘ S₀))
  have : QuasiCompact (𝔸(m; X) ↘ S₀) := inferInstanceAs (QuasiCompact (p ≫ X ↘ S₀))
  have : IsSeparated (𝔸(m; X) ↘ S₀) := inferInstanceAs (IsSeparated (p ≫ X ↘ S₀))
  have : LocallyOfFiniteType (𝔸(Option m; X) ↘ S₀) :=
    inferInstanceAs (LocallyOfFiniteType (π ≫ X ↘ S₀))
  -- `q` is the trivial line bundle with fibre coordinate `t = s_none`
  let t : 𝔸(Option m; X) ⟶ affineLine k₀ :=
    reindex (fun _ : PUnit.{u + 1} ↦ (none : Option m)) X ≫ map PUnit.{u + 1} (X ↘ S₀)
  have hq0 := (isPullback_reindex_some_reindex_none m X).flip.paste_horiz
    (isPullback_map (n := PUnit.{u + 1}) (X ↘ S₀))
  have hq : IsPullback q t (𝔸(m; X) ↘ S₀) (affineLine k₀ ↘ S₀) := hq0.flip
  have : IsSeparated q := MorphismProperty.of_isPullback hq0 inferInstance
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback hq0 inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq0 inferInstance
  -- the coordinates of `𝔸^{Option m}`
  let Rs := reindex (Option.some : m → Option m) S₀
  let Rn := reindex (fun _ : PUnit.{u + 1} ↦ (none : Option m)) S₀
  have : Rs.IsOver S₀ := ⟨reindex_over _ _⟩
  have : Rn.IsOver S₀ := ⟨reindex_over _ _⟩
  have hzs : zeroSection (Option m) S₀ ≫ Rs = zeroSection m S₀ := zeroSection_comp_reindex _ _
  have hzn : zeroSection (Option m) S₀ ≫ Rn = zeroSection PUnit.{u + 1} S₀ :=
    zeroSection_comp_reindex _ _
  -- the zero locus `j₀ : Z₀ ⟶ X` of `h_none`
  let h₀ : X ⟶ affineLine k₀ := h ≫ Rn
  let Z₀ := pullback (zeroSection PUnit.{u + 1} S₀) h₀
  let j₀ : Z₀ ⟶ X := pullback.snd _ _
  let : Z₀.Over S₀ := ⟨pullback.fst _ _⟩
  have hi₀ : IsPullback (Z₀ ↘ S₀) j₀ (zeroSection PUnit.{u + 1} S₀) h₀ :=
    IsPullback.of_hasPullback _ _
  have : j₀.IsOver S₀ := ⟨by
    rw [← comp_over h₀ S₀, ← Category.assoc, ← hi₀.w, Category.assoc, zeroSection_over,
      Category.comp_id]⟩
  have : IsClosedImmersion j₀ := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsSeparated (Z₀ ↘ S₀) := by rw [← comp_over j₀ S₀]; infer_instance
  have : LocallyOfFiniteType (Z₀ ↘ S₀) := by rw [← comp_over j₀ S₀]; infer_instance
  have : QuasiCompact (Z₀ ↘ S₀) := by rw [← comp_over j₀ S₀]; infer_instance
  have : QuasiCompact (Z ↘ S₀) := by rw [← comp_over i S₀]; infer_instance
  have : QuasiSeparated (Z ↘ S₀) := by rw [← comp_over i S₀]; infer_instance
  -- the zero locus `i₁ : 𝔸ᵐ_{Z₀} ⟶ 𝔸ᵐ_X` of `p^* h_none`
  let p₁ := 𝔸(m; Z₀) ↘ Z₀
  let i₁ : 𝔸(m; Z₀) ⟶ 𝔸(m; X) := map m j₀
  let : (𝔸(m; Z₀)).Over S₀ := ⟨p₁ ≫ Z₀ ↘ S₀⟩
  have : p₁.IsOver S₀ := ⟨rfl⟩
  have hi₁p : i₁ ≫ p = p₁ ≫ j₀ := map_over j₀
  have : i₁.IsOver S₀ := ⟨by
    change i₁ ≫ p ≫ X ↘ S₀ = p₁ ≫ Z₀ ↘ S₀
    rw [← Category.assoc, hi₁p, Category.assoc, comp_over j₀ S₀]⟩
  have : IsClosedImmersion i₁ :=
    MorphismProperty.of_isPullback (isPullback_map (n := m) j₀).flip inferInstance
  have : LocallyOfFiniteType (𝔸(m; Z₀) ↘ S₀) :=
    inferInstanceAs (LocallyOfFiniteType (p₁ ≫ Z₀ ↘ S₀))
  let h₁ : 𝔸(m; X) ⟶ affineLine k₀ := p ≫ h₀
  have hi₁ : IsPullback (𝔸(m; Z₀) ↘ S₀) i₁ (zeroSection PUnit.{u + 1} S₀) h₁ :=
    (isPullback_map (n := m) j₀).flip.paste_horiz hi₀
  -- the zero locus `i' : Z ⟶ Z₀` of the remaining coordinates `h'`
  let h' : Z₀ ⟶ 𝔸(m; S₀) := j₀ ≫ h ≫ Rs
  let i' : Z ⟶ Z₀ := hi₀.lift (Z ↘ S₀) i (by
    rw [← hzn, ← Category.assoc, hi.w, Category.assoc])
  have hi'j : i' ≫ j₀ = i := hi₀.lift_snd _ _ _
  have hi'f : i' ≫ Z₀ ↘ S₀ = Z ↘ S₀ := hi₀.lift_fst _ _ _
  have : i'.IsOver S₀ := ⟨hi'f⟩
  have key {W : Scheme.{u}} (a : W ⟶ S₀) (b : W ⟶ Z₀) (hab : a ≫ zeroSection m S₀ = b ≫ h') :
      b ≫ Z₀ ↘ S₀ = a := by
    have e := congrArg (· ≫ 𝔸(m; S₀) ↘ S₀) hab
    simp only [Category.assoc, zeroSection_over, Category.comp_id] at e
    rw [e, ← comp_over j₀ S₀]
    simp [h', Rs]
  have hi' : IsPullback (Z ↘ S₀) i' (zeroSection m S₀) h' := by
    refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ hi.lift s.fst (s.snd ≫ j₀) ?_)
      (fun s ↦ ?_) (fun s ↦ ?_) (fun s l hl₁ hl₂ ↦ ?_)⟩⟩
    · change _ = i' ≫ j₀ ≫ h ≫ Rs
      rw [← Category.assoc i', hi'j, ← Category.assoc, ← hi.w, Category.assoc, hzs]
    · apply (isPullback_reindex_some_reindex_none m S₀).hom_ext
      · change s.fst ≫ zeroSection (Option m) S₀ ≫ Rs = s.snd ≫ j₀ ≫ h ≫ Rs
        rw [hzs, s.condition]
      · change s.fst ≫ zeroSection (Option m) S₀ ≫ Rn = s.snd ≫ j₀ ≫ h ≫ Rn
        rw [hzn, ← key s.fst s.snd s.condition, Category.assoc]
        exact congrArg (s.snd ≫ ·) hi₀.w
    · exact hi.lift_fst _ _ _
    · apply hi₀.hom_ext
      · rw [Category.assoc, hi'f, hi.lift_fst, key s.fst s.snd s.condition]
      · rw [Category.assoc, hi'j, hi.lift_snd]
    · apply hi.hom_ext
      · rw [hl₁, hi.lift_fst]
      · rw [hi.lift_snd, ← hi'j, ← Category.assoc, hl₂]
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback hi' inferInstance
  have : h'.IsOver S₀ := by dsimp only [h']; infer_instance
  have : h₁.IsOver S₀ := by dsimp only [h₁, h₀]; infer_instance
  obtain ⟨e₁⟩ := nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul (l := l) ψ hψ
    h₁ q t hq i₁ hi₁
  obtain ⟨e₂⟩ := ih Z₀ Z h' i' hi'
  -- the phases
  have hc {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (x : Γ(X₃, ⊤)) :
      f.appTop (g.appTop x) = (f ≫ g).appTop x := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  let Φ' : Γ(𝔸(m; X), ⊤) := ∑ j, p.appTop ((h ≫ Rs).appTop (coord S₀ j)) * coord X j
  let A : Γ(𝔸(Option m; X), ⊤) :=
    q.appTop (h₁.appTop (coord S₀ PUnit.unit)) * t.appTop (coord S₀ PUnit.unit)
  let Φ₁ : Γ(𝔸(m; Z₀), ⊤) := ∑ j, p₁.appTop (h'.appTop (coord S₀ j)) * coord Z₀ j
  have hΦ : (∑ k, π.appTop (h.appTop (coord S₀ k)) * coord X k) = q.appTop Φ' + A := by
    rw [Fintype.sum_option, add_comm]
    congr 1
    · simp only [Φ', map_sum, map_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hc q p, hqp]
      simp [q, Rs]
    · simp only [A, h₁, h₀, t, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [hc q p, hqp]
      simp [Rn]
  have hΦ₁ : i₁.appTop Φ' = Φ₁ := by
    simp only [Φ', Φ₁, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hc i₁ p, hi₁p]
    simp [i₁, h']
  -- the component isomorphisms
  obtain ⟨eDqp⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) q p
  obtain ⟨eDi₁p⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i₁ p
  obtain ⟨eDp₁j₀⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) p₁ j₀
  obtain ⟨eDi'j₀⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) i' j₀
  obtain ⟨eAdd⟩ := nonempty_iso_tensorLisse_artinSchreierOf_add (l := l) ψ (q.appTop Φ') A
  obtain ⟨eΦ⟩ := nonempty_iso_tensorLisse_of_iso (eqToIso (congrArg (artinSchreierOf ψ) hΦ))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eTq⟩ := nonempty_iso_tensorLisse_comp_upperStar q (artinSchreierOf ψ Φ')
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨aq⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) q ψ Φ'
  obtain ⟨eaq⟩ := nonempty_iso_tensorLisse_of_iso aq
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ Φ'))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eTi₁⟩ := nonempty_iso_tensorLisse_comp_upperStar i₁ (artinSchreierOf ψ Φ')
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨ai₁⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) i₁ ψ Φ'
  obtain ⟨eai₁⟩ := nonempty_iso_tensorLisse_of_iso (ai₁ ≪≫ eqToIso (congrArg _ hΦ₁))
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ Φ'))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨etwp₁⟩ := nonempty_iso_tateTwist_comp_derivedLowerShriek (k₀ := k₀) (l := l) p₁ (-1)
  obtain ⟨etwi'⟩ := nonempty_iso_tateTwist_comp_derivedLowerShriek (k₀ := k₀) (l := l) i' (-1)
  have ha : -(Fintype.card m : ℤ) + -1 = -(Fintype.card (Option m) : ℤ) := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    ring
  have hb : -(2 * (Fintype.card m : ℤ)) + -2 = -(2 * (Fintype.card (Option m) : ℤ)) := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    ring
  rw [← ha, ← hb]
  exact nonempty_iso_of_optionStep (upperStarCongrIso hqp.symm ≪≫ upperStarCompIso q p)
    (derivedLowerShriekIsoOfEq hqp.symm ≪≫ eDqp) (eΦ ≪≫ eAdd.symm)
    (eTq ≪≫ Functor.isoWhiskerLeft _ eaq) e₁ (eTi₁ ≪≫ Functor.isoWhiskerLeft _ eai₁)
    ((upperStarCompIso i₁ p).symm ≪≫ upperStarCongrIso hi₁p ≪≫ upperStarCompIso p₁ j₀)
    (eDi₁p.symm ≪≫ derivedLowerShriekIsoOfEq hi₁p ≪≫ eDp₁j₀)
    ((derivedLowerShriek k₀ l p₁).commShiftIso (-2 : ℤ)) etwp₁ e₂ etwi'
    ((derivedLowerShriek k₀ l i').commShiftIso (-2 : ℤ))
    ((tateTwist k₀ l Z (-1)).commShiftIso _) (tateTwistCompTateTwistAddIso _ _)
    (shiftFunctorAdd _ _ _).symm
    ((upperStarCompIso i' j₀).symm ≪≫ upperStarCongrIso hi'j)
    (eDi'j₀.symm ≪≫ derivedLowerShriekIsoOfEq hi'j)

/-- The delta kernel statement for the standard bundle, in every rank. -/
private theorem deltaClaim (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) (n : Type u)
    [Fintype n] : DeltaClaim k₀ l ψ n := by
  refine Fintype.induction_empty_option (P := fun n _ ↦ DeltaClaim k₀ l ψ n) ?_ ?_ ?_ n
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    convert deltaClaim_of_equiv ψ e ih
  · exact deltaClaim_pempty ψ
  · intro α _ ih
    convert deltaClaim_option ψ hψ α ih

/-- **The delta kernel on a trivial vector bundle.** Let `h : X ⟶ 𝔸ⁿ` be a family of functions
on a `k₀`-scheme `X` with zero locus `i : Z ⟶ X` (the base change of the zero section along `h`),
let `π : Y ⟶ X` be the trivial vector bundle of rank `n` with fibre coordinates `s : Y ⟶ 𝔸ⁿ`,
and let `ψ` be nontrivial. Then

`Rπ₀!(ℒ_ψ(∑ₖ hₖ sₖ) ⊗ π^* P) ≅ Ri₀!((i^* P)(-n)[-2n])`

naturally in the Weil complex `P` on `X`. -/
theorem nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_sum
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) (n : Type u) [Fintype n] {X Y Z : Scheme.{u}}
    [X.Over S₀] [Y.Over S₀] [Z.Over S₀] (h : X ⟶ 𝔸(n; S₀)) [h.IsOver S₀] (π : Y ⟶ X)
    (s : Y ⟶ 𝔸(n; S₀)) [π.IsOver S₀] (hπ : IsPullback π s (X ↘ S₀) (𝔸(n; S₀) ↘ S₀))
    (i : Z ⟶ X) [i.IsOver S₀] (hi : IsPullback (Z ↘ S₀) i (zeroSection n S₀) h)
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsClosedImmersion i]
    [IsSeparated (X ↘ S₀)] [LocallyOfFiniteType (X ↘ S₀)] [QuasiCompact (X ↘ S₀)]
    [LocallyOfFiniteType (Y ↘ S₀)] [LocallyOfFiniteType (Z ↘ S₀)] :
    Nonempty (upperStar π ⋙
        tensorLisse (artinSchreierOf ψ
          (∑ k, π.appTop (h.appTop (coord S₀ k)) * s.appTop (coord S₀ k)))
          (isLisse_artinSchreierOf ψ _) ⋙ derivedLowerShriek k₀ l π ≅
      upperStar i ⋙ tateTwist k₀ l Z (-(Fintype.card n : ℤ)) ⋙
        shiftFunctor _ (-(2 * (Fintype.card n : ℤ))) ⋙ derivedLowerShriek k₀ l i) := by
  let p := 𝔸(n; X) ↘ X
  let : (𝔸(n; X)).Over S₀ := ⟨p ≫ X ↘ S₀⟩
  have : p.IsOver S₀ := ⟨rfl⟩
  have : LocallyOfFiniteType (𝔸(n; X) ↘ S₀) := inferInstanceAs (LocallyOfFiniteType (p ≫ X ↘ S₀))
  have : QuasiCompact (Z ↘ S₀) := by rw [← comp_over i S₀]; infer_instance
  have : QuasiSeparated (Z ↘ S₀) := by rw [← comp_over i S₀]; infer_instance
  let sq := (isPullback_map (n := n) (X ↘ S₀)).flip
  let e : Y ≅ 𝔸(n; X) := hπ.isoIsPullback _ _ sq
  have he : e.hom ≫ p = π := hπ.isoIsPullback_hom_fst _ _ sq
  have he' : e.hom ≫ map n (X ↘ S₀) = s := hπ.isoIsPullback_hom_snd _ _ sq
  have : e.hom.IsOver S₀ := ⟨by
    change e.hom ≫ (p ≫ X ↘ S₀) = _
    rw [← Category.assoc, he, comp_over π]⟩
  obtain ⟨eT⟩ := nonempty_iso_upperStar_tensorLisse_derivedLowerShriek_of_isIso ψ π p e.hom he
    (∑ k, p.appTop (h.appTop (coord S₀ k)) * coord X k)
  have hΦ : e.hom.appTop (∑ k, p.appTop (h.appTop (coord S₀ k)) * coord X k) =
      ∑ k, π.appTop (h.appTop (coord S₀ k)) * s.appTop (coord S₀ k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he, ← he',
      ← map_appTop_coord (n := n) (X ↘ S₀), Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [hΦ] at eT
  obtain ⟨eC⟩ := deltaClaim ψ hψ n X Z h i hi
  exact ⟨eT.symm ≪≫ eC⟩

end AlgebraicGeometry.WeilComplex
