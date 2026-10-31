/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# A supported fibre represents the right adjoint

Source: the current Weil conjectures blueprint, `sec-smooth-purity`,
`sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md`, (2) and (3),
and Consequences (4) (blueprint: lem-sf-orthogonal-supported-fibre).
-/

@[expose] public section

universe uC uZ uU vC vZ vU

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated.Recollement

/-- A fully faithful exact embedding onto the kernel of a localization with fully faithful
right adjoint has a right adjoint represented by the fibre of the localization unit.
The counit and unit determine a unique distinguished triangle, natural with uniquely
specified outside components, for every choice of the closed adjunction.

Source: the current Weil conjectures blueprint, `sec-smooth-purity`,
`sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md`, (2) and (3),
and Consequences (4) (blueprint: lem-sf-orthogonal-supported-fibre).

Proof:
1. Use the proved upstream recollement fibre argument: shift orthogonality follows
   from the open adjunction and `JI = 0`; the fibre of the open unit lies in the
   essential image of `I`, and Hom exactness makes it represent the right adjoint.
   These give `isLeftAdjoint` and `subsingleton_hom_shift`.
2. For any supplied closed adjunction, the upstream
   `existsUnique_distTriang_counit_unit` gives the unique boundary.
   `exists_triangleHom` supplies the three specified components, and
   `triangleHom_ext` shows that its middle component determines it uniquely.
   These use shifted orthogonality and the exact Hom sequences (BBD 1.1.9–1.1.10).
3. Register full faithfulness of `I`. The standard adjunction theorem makes the
   closed unit invertible. The upstream `isZero_obj_obj` proves `H R = 0` by
   applying the adjunction to the vanishing Hom groups.
4. For an arbitrary supplied fibre and `e : I Q ≅ F`, use
   `representableByOfDistTriang`: Hom exactness and shifted orthogonality make
   `g ↦ I.map g ≫ e.hom ≫ a` a natural bijection.
5. Compare that representation with `closedAdj.representableBy K` using
   `RepresentableBy.uniqueUpToIso`. Its forward map is the closed adjunction
   bijection applied to the image of `𝟙 Q`. The inverse adjunction bijection
   therefore sends it to `e.hom ≫ a`, which is precisely the required counit
   compatibility. The representation's explicit formula proves the final clause. -/
theorem orthogonalSupportedFibre
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    {Z : Type uZ} [Category.{vZ} Z] [Preadditive Z] [HasZeroObject Z]
    [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive]
    [Pretriangulated Z] [IsTriangulated Z]
    {U : Type uU} [Category.{vU} U] [Preadditive U] [HasZeroObject U]
    [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive]
    [Pretriangulated U] [IsTriangulated U]
    (I : Z ⥤ C) [I.CommShift ℤ] [I.IsTriangulated]
    (J : C ⥤ U) [J.CommShift ℤ] [J.IsTriangulated]
    (R : U ⥤ C) (openAdj : J ⊣ R) [IsIso openAdj.counit]
    (hI : I.FullyFaithful)
    (hzero : ∀ Q : Z, IsZero (J.obj (I.obj Q)))
    (hker : ∀ F : C, IsZero (J.obj F) → I.essImage F) :
    I.IsLeftAdjoint ∧
    (∀ (Q : Z) (N : U) (m : ℤ), Subsingleton ((I.obj Q)⟦m⟧ ⟶ R.obj N)) ∧
    ∀ (H : C ⥤ Z) (closedAdj : I ⊣ H),
      (∀ K : C, ∃! δ : R.obj (J.obj K) ⟶ (I.obj (H.obj K))⟦(1 : ℤ)⟧,
        triangle openAdj closedAdj K δ ∈ distTriang C) ∧
      (∀ (K K' : C) (f : K ⟶ K')
        (δ : R.obj (J.obj K) ⟶ (I.obj (H.obj K))⟦(1 : ℤ)⟧)
        (δ' : R.obj (J.obj K') ⟶ (I.obj (H.obj K'))⟦(1 : ℤ)⟧),
        triangle openAdj closedAdj K δ ∈ distTriang C →
        triangle openAdj closedAdj K' δ' ∈ distTriang C →
        ∃ τ : triangle openAdj closedAdj K δ ⟶ triangle openAdj closedAdj K' δ',
          (τ.hom₁ = I.map (H.map f) ∧ τ.hom₂ = f ∧ τ.hom₃ = R.map (J.map f)) ∧
          ∀ τ' : triangle openAdj closedAdj K δ ⟶ triangle openAdj closedAdj K' δ',
            τ'.hom₂ = f → τ' = τ) ∧
      (∀ Q : Z, IsIso (closedAdj.unit.app Q)) ∧
      (∀ N : U, IsZero (H.obj (R.obj N))) ∧
      (∀ (K F : C) (a : F ⟶ K) (δ : R.obj (J.obj K) ⟶ F⟦(1 : ℤ)⟧),
        Triangle.mk a (openAdj.unit.app K) δ ∈ distTriang C →
        ∀ (Q : Z) (e : I.obj Q ≅ F),
          (∃ t : Q ≅ H.obj K, I.map t.hom ≫ closedAdj.counit.app K = e.hom ≫ a) ∧
          ∃ B : (I.op ⋙ yoneda.obj K).RepresentableBy Q,
            ∀ (P : Z) (g : P ⟶ Q), B.homEquiv g = I.map g ≫ e.hom ≫ a) := by
  refine ⟨isLeftAdjoint openAdj hI hzero hker,
    subsingleton_hom_shift I J openAdj hzero, ?_⟩
  intro H closedAdj
  refine ⟨existsUnique_distTriang_counit_unit openAdj closedAdj hI hzero hker,
    ?_, ?_, isZero_obj_obj openAdj closedAdj hzero, ?_⟩
  · intro K K' f δ δ' hδ hδ'
    obtain ⟨τ, hτ⟩ := exists_triangleHom openAdj closedAdj hzero f hδ hδ'
    refine ⟨τ, hτ, ?_⟩
    intro τ' hτ'
    exact triangleHom_ext openAdj closedAdj hzero hδ hδ' (hτ'.trans hτ.2.1.symm)
  · have : I.Full := hI.full
    have : I.Faithful := hI.faithful
    intro Q
    infer_instance
  · intro K F a δ hT Q e
    let B := representableByOfDistTriang hI hT
      (fun P m ↦ subsingleton_hom_shift I J openAdj hzero P (J.obj K) m) e
    refine ⟨?_, B, ?_⟩
    · let t : Q ≅ H.obj K := B.uniqueUpToIso (closedAdj.representableBy K)
      refine ⟨t, ?_⟩
      change (closedAdj.homEquiv Q K).symm t.hom = e.hom ≫ a
      change (closedAdj.homEquiv Q K).symm
        ((closedAdj.homEquiv Q K) (B.homEquiv (𝟙 Q))) = e.hom ≫ a
      rw [Equiv.symm_apply_apply]
      simp [B, representableByOfDistTriang]
    · intro P g
      rfl

end CategoryTheory.Pretriangulated.Recollement
