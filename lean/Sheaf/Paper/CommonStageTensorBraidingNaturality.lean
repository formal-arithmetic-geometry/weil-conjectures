/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Naturality of the common-stage tensor symmetry

Source: current blueprint coefficient conventions and the common-stage passage
in lem-fix-weil-operations.proof.md.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.StageSystem.PairCategory
namespace WeilConjectures

/-- Naturality of the prescribed common-stage braiding follows from naturality
at every rational coefficient field, including maps requiring a field enlargement.

Source: current blueprint, lem-fix-weil-operations.proof.md, tensor/Hom and
coefficient-passage paragraphs; the representative formulas of
lem-pur-derived-pullback-tensor-iso.

Proof: choose finite representatives of f and g. Enlarge their fields to one
finite compositum L containing the four object fields, both representative
fields, and the fields of the four tensor objects. Transport f and g to L;
mkHom_tr identifies their resulting classes with the original arrows. The
representative clause of commonStageDerivedTensor_existsUnique expresses both
tensor maps as the rational tensor maps conjugated by commonStageTensorComparison.
The representative clause of pullbackTensorCommonBraiding_existsUnique expresses
each braiding by the rational braiding with exactly the same comparisons.
Composition of representatives at L is represented by their composite. Cancel
the adjacent comparison inverses. The two representatives are now the two sides
of hn at L, between the four transported objects. Apply hn and take their common
morphism class. This proves the desired equality without injectivity of any
scalar-extension map. The construction works for identity and zero arrows, and
uses no Hom-pair or separatedness condition.
(blueprint: lem-pod-common-stage-tensor-braiding-naturality). -/
theorem commonStageTensorBraiding_naturality
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (hn : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (M M' N N' : sfRationalConstructibleCategory l E W)
      (f : M ⟶ M') (g : N ⟶ N'),
      (rationalDerivedTensor l E W).map (Prod.mkHom f g) ≫
          (pullbackTensorRationalBraiding l E W M' N').hom =
        (pullbackTensorRationalBraiding l E W M N).hom ≫
          (rationalDerivedTensor l E W).map (Prod.mkHom g f))
    (M M' N N' : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (f : M ⟶ M') (g : N ⟶ N') :
    (commonStageDerivedTensor l Ω W).map (Prod.mkHom f g) ≫
        (pullbackTensorCommonBraiding l Ω W M' N').hom =
      (pullbackTensorCommonBraiding l Ω W M N).hom ≫
        (commonStageDerivedTensor l Ω W).map (Prod.mkHom g f) := by
  let O := commonStageTensorObject l Ω W
  have ho := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1
  have hm := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.2
  obtain ⟨L₁, hM, hM', hf⟩ := exists_mkHom_eq f
  obtain ⟨L₂, hN, hN', hg⟩ := exists_mkHom_eq g
  obtain ⟨L₃, h₁, h₂⟩ := exists_ge_ge L₁ L₂
  obtain ⟨L₄, h₃, hMN⟩ := exists_ge_ge L₃ (O M N).stage
  obtain ⟨L₅, h₄, hMN'⟩ := exists_ge_ge L₄ (O M' N').stage
  obtain ⟨L₆, h₅, hNM⟩ := exists_ge_ge L₅ (O N M).stage
  obtain ⟨L, h₆, hNM'⟩ := exists_ge_ge L₆ (O N' M').stage
  have hMN := hMN.trans (h₄.trans (h₅.trans h₆))
  have hMN' := hMN'.trans (h₅.trans h₆)
  have hNM := hNM.trans h₆
  obtain ⟨a, ha⟩ := hf L (h₁.trans (h₃.trans (h₄.trans (h₅.trans h₆))))
  obtain ⟨b, hb⟩ := hg L (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))
  subst f
  subst g
  have ht := hm M N M' N' L hMN hMN' a b
  have ht' := hm N M N' M' L hNM hNM' b a
  have hβ := (pullbackTensorCommonBraiding_existsUnique l Ω W M N).exists.choose_spec
    L hMN hNM
  have hβ' := (pullbackTensorCommonBraiding_existsUnique l Ω W M' N').exists.choose_spec
    L hMN' hNM'
  have hl := heq_comp (ho M N) (ho M' N') (ho N' M') ht hβ'
  have hr := heq_comp (ho M N) (ho N M) (ho N' M') hβ ht'
  apply eq_of_heq
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  change ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _ =
    ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom]
  congr 1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ (commonStageTensorComparison l Ω W M N L hMN).hom ≫ z ≫
      (commonStageTensorComparison l Ω W N' M' L hNM').inv)
    (hn (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ _ a b)

end WeilConjectures
