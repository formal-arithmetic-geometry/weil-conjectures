/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Invertibility of powers of ell on continuous rational derived coefficients

Source: Bhatt--Scholze, Section 6.8; blueprint rationalization comparison,
proof of thm-sfb-extend-scalars-localization, "F inverts W"
(blueprint: lem-sfb-rational-derived-scalar-invertible).
-/

@[expose] public section

set_option autoImplicit false

attribute [instance] CategoryTheory.Mod.isGrothendieckAbelian

universe u

open CategoryTheory MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem moduleScalarInverse
    {D : Type*} [Category D] [Preadditive D] [MonoidalCategory D]
    [MonoidalPreadditive D] (A : D) [MonObj A] (m : ℕ) (t : A ⟶ A)
    (ht : m • t = 𝟙 A) (M : Mod D A) :
    ∃ (_h : IsIso (m • 𝟙 M)),
      (inv (m • 𝟙 M)).hom =
        (λ_ M.X).inv ≫ ((η[A] ≫ t) ▷ M.X) ≫ ModObj.smul (M := A) (X := M.X) := by
  let b : M.X ⟶ M.X :=
    (λ_ M.X).inv ≫ ((η[A] ≫ t) ▷ M.X) ≫ ModObj.smul (M := A) (X := M.X)
  have hb : m • b = 𝟙 M.X := by
    dsimp only [b]
    rw [← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp]
    change (λ_ M.X).inv ≫ (m • (tensorRight M.X).map (η[A] ≫ t)) ≫ _ = _
    rw [← Functor.map_nsmul, ← Preadditive.comp_nsmul, ht]
    simp [tensorRight]
  have hi : IsIso (m • 𝟙 M.X) :=
    ⟨⟨b, by simpa only [Preadditive.nsmul_comp, Category.id_comp] using hb,
      by simpa only [Preadditive.comp_nsmul, Category.comp_id] using hb⟩⟩
  have hm : (m • 𝟙 M : M ⟶ M).hom = m • 𝟙 M.X := rfl
  have hf : IsIso ((Mod.forget A).map (m • 𝟙 M)) := by
    change IsIso (m • 𝟙 M.X)
    exact hi
  have hM : IsIso (m • 𝟙 M) := isIso_of_reflects_iso _ (Mod.forget A)
  refine ⟨hM, ?_⟩
  apply (cancel_mono (m • 𝟙 M.X)).1
  change (Mod.forget A).map (inv (m • 𝟙 M)) ≫ _ = _
  change (Mod.forget A).map (inv (m • 𝟙 M)) ≫
    (Mod.forget A).map (m • 𝟙 M) = b ≫ (m • 𝟙 M.X)
  rw [← Functor.map_comp, IsIso.inv_hom_id, (Mod.forget A).map_id]
  change 𝟙 M.X = b ≫ (m • 𝟙 M.X)
  rw [Preadditive.comp_nsmul, Category.comp_id, hb]

/-- Powers of ell act invertibly on the ordinary unbounded derived category of internal
modules over the actual continuous coefficient ring E_X. The witness t is multiplication
by ell^(-n) on continuous functions. Its value on the ring unit, transported to X, acts
on each degree of the representative C by the displayed unitor/action formula.
Source: Bhatt--Scholze, Section 6.8; blueprint thm-sfb-extend-scalars-localization,
"F inverts W" (blueprint: lem-sfb-rational-derived-scalar-invertible).

Proof: put a = ell^n and b = a^(-1) in E. Since E contains Q_ell, a is nonzero and
ab = ba = 1. Pointwise multiplication gives the corresponding constant sections of
underline E. Pull them back by the strong monoidal upperStarFromPoint X. This inverse
image is a left adjoint between abelian categories, hence preserves finite biproducts
and addition, so the first section is ell^n times the unit. The module action axioms
give m_s m_t = m_(st) and m_1 = id; commutativity makes these module morphisms, and
compatibility of all module maps makes their degreewise actions chain maps A and B.
Thus AB = BA = id and A = ell^n id. By lem-sfb-derived-localization-additive, choose
C and e : Q(C) isomorphic to K. The additive localization Q sends these identities
to inverse identities, with Q(A) = ell^n id. Conjugating Q(B) by e gives the displayed
two-sided inverse on K. This uses every integer degree and no boundedness assumption. -/
theorem rationalDerivedScalar_invertible
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))) (n : ℕ) :
    IsIso ((l ^ n) • 𝟙 K) ∧
    ∃ (t : Profinite.continuousCoefficientRingObj E ⟶
          Profinite.continuousCoefficientRingObj E)
      (C : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) ℤ)
      (e : DerivedCategory.Q.obj C ≅ K) (B : C ⟶ C),
      (∀ (S : Profinite.{u}) (f : ULift.{u + 1} C(S, E)) (s : S),
        (((t.hom.app (op S)) f).down) s = ((l : E) ^ n)⁻¹ * f.down s) ∧
      (∀ q : ℤ, (B.f q).hom =
        (λ_ (C.X q).X).inv ≫
          ((η[(condensedRingObj (Profinite.continuousCoefficientRingObj E) X)] ≫
            (upperStarFromPoint X).map t) ▷ (C.X q).X) ≫
          ModObj.smul (M := condensedRingObj (Profinite.continuousCoefficientRingObj E) X)
            (X := (C.X q).X)) ∧
      ((l ^ n) • 𝟙 K) ≫ (e.inv ≫ DerivedCategory.Q.map B ≫ e.hom) = 𝟙 K ∧
      (e.inv ≫ DerivedCategory.Q.map B ≫ e.hom) ≫ ((l ^ n) • 𝟙 K) = 𝟙 K := by
  let Λ := Profinite.continuousCoefficientRingObj E
  let t : Λ ⟶ Λ := ⟨{
    app S := AddCommGrpCat.ofHom {
      toFun f := ⟨⟨fun s ↦ ((l : E) ^ n)⁻¹ * f.down s,
        continuous_const.mul f.down.continuous⟩⟩
      map_zero' := by
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        simp
      map_add' f g := by
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        change ((l : E) ^ n)⁻¹ * (f.down s + g.down s) =
          ((l : E) ^ n)⁻¹ * f.down s + ((l : E) ^ n)⁻¹ * g.down s
        exact mul_add _ _ _ }
    naturality S T f := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro g
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      rfl }⟩
  have : CharZero E := Algebra.charZero_of_charZero ℚ_[l] E
  have hl : (l : E) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have ht : (l ^ n) • t = 𝟙 Λ := by
    apply (sheafToPresheaf _ _).map_injective
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change (l ^ n) • (((l : E) ^ n)⁻¹ * f.down s) = f.down s
    rw [nsmul_eq_mul, Nat.cast_pow, ← _root_.mul_assoc, mul_inv_cancel₀ hl, _root_.one_mul]
  let F := upperStarFromPoint X
  have : F.IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : Limits.PreservesBinaryBiproducts F :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have htX : (l ^ n) • F.map t = 𝟙 (F.obj Λ) := by
    rw [← Functor.map_nsmul, ht, F.map_id]
  let C := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj C ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hc (q : ℤ) := moduleScalarInverse (F.obj Λ) (l ^ n) (F.map t) htX (C.X q)
  have hq (q : ℤ) : IsIso (((l ^ n) • 𝟙 C).f q) := by
    change IsIso ((l ^ n) • 𝟙 (C.X q))
    exact (hc q).choose
  have hC : IsIso ((l ^ n) • 𝟙 C) := HomologicalComplex.Hom.isIso_of_components _
  let B : C ⟶ C := inv ((l ^ n) • 𝟙 C)
  have hB (q : ℤ) : (B.f q).hom =
      (λ_ (C.X q).X).inv ≫ ((η[F.obj Λ] ≫ F.map t) ▷ (C.X q).X) ≫
        ModObj.smul (M := F.obj Λ) (X := (C.X q).X) := by
    dsimp only [B]
    rw [HomologicalComplex.Hom.inv_f_apply]
    exact (hc q).choose_spec
  have hQ : DerivedCategory.Q.map ((l ^ n) • 𝟙 C) =
      (l ^ n) • 𝟙 (DerivedCategory.Q.obj C) := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  have hBK : ((l ^ n) • 𝟙 K) ≫
      (e.inv ≫ DerivedCategory.Q.map B ≫ e.hom) = 𝟙 K := by
    have he : ((l ^ n) • 𝟙 K) ≫ e.inv =
        e.inv ≫ DerivedCategory.Q.map ((l ^ n) • 𝟙 C) := by
      rw [hQ, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    rw [← Category.assoc, he]
    have hAB : DerivedCategory.Q.map ((l ^ n) • 𝟙 C) ≫ DerivedCategory.Q.map B =
        𝟙 (DerivedCategory.Q.obj C) := by
      rw [← DerivedCategory.Q.map_comp]
      change DerivedCategory.Q.map
        (((l ^ n) • 𝟙 C) ≫ inv ((l ^ n) • 𝟙 C)) = _
      rw [IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
    simpa only [Category.assoc, Category.id_comp, e.inv_hom_id] using
      congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) hAB
  have hKB : (e.inv ≫ DerivedCategory.Q.map B ≫ e.hom) ≫
      ((l ^ n) • 𝟙 K) = 𝟙 K := by
    have he : e.hom ≫ ((l ^ n) • 𝟙 K) =
        DerivedCategory.Q.map ((l ^ n) • 𝟙 C) ≫ e.hom := by
      rw [hQ, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    rw [Category.assoc, Category.assoc, he]
    have hBA : DerivedCategory.Q.map B ≫ DerivedCategory.Q.map ((l ^ n) • 𝟙 C) =
        𝟙 (DerivedCategory.Q.obj C) := by
      rw [← DerivedCategory.Q.map_comp]
      change DerivedCategory.Q.map
        (inv ((l ^ n) • 𝟙 C) ≫ ((l ^ n) • 𝟙 C)) = _
      rw [IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    simpa only [Category.assoc, Category.id_comp, e.inv_hom_id] using
      congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) hBA
  exact ⟨⟨⟨_, hBK, hKB⟩⟩, t, C, e, B, (by intros; rfl), hB, hBK, hKB⟩

end AlgebraicGeometry.ProEtale
