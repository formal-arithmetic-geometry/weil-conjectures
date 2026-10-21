/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Unit normalization of internal tensor composition

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`,
`def-sfb-derived-extend-comp-iso.proof.md`, the sentence
"Extension of scalars is compatible with composition";
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, extension adjunction and
composition comparison (blueprint: lem-sfb-internal-tensor-composition-unit-normalization).

The two tensor formulas are equations after the actual coequalizer projections in the
ambient category. They require neither elements nor a concrete-category structure.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- Apply Mathlib's colimit-universe restriction pointwise to the left tensor functors.
Source: the tensor-preservation hypothesis in blueprint main-20261015,
`def-sfb-derived-extend-comp-iso.proof.md`, compatibility with composition
(blueprint: lem-sfb-internal-tensor-composition-unit-normalization). -/
instance internalTensorComposition_tensorLeft_preservesSmallestColimits
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [∀ X : C, PreservesColimits (tensorLeft X)] :
    ∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X)

/-- Apply Mathlib's colimit-universe restriction pointwise to the right tensor functors.
Source: the tensor-preservation hypothesis in blueprint main-20261015,
`def-sfb-derived-extend-comp-iso.proof.md`, compatibility with composition
(blueprint: lem-sfb-internal-tensor-composition-unit-normalization). -/
instance internalTensorComposition_tensorRight_preservesSmallestColimits
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [∀ X : C, PreservesColimits (tensorRight X)] :
    ∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X)

/-- Internal tensor multiplication is the specified unit-compatible composition comparison.

Source: blueprint main-20261015, `def-sfb-derived-extend-comp-iso.proof.md`, compatibility
with composition; `ExtendScalars.lean`, `extendHomEquiv` and `extendScalarsComp`
(blueprint: lem-sfb-internal-tensor-composition-unit-normalization).

Proof:
1. For M put P = Ext_phi M, Q = Ext_psi P, H = Ext_(phi psi) M, with projections
   q, p, r. Their units a, b, c insert the respective monoid units. Composing the
   two extension Hom bijections sends f to f b a. The restriction comparison has
   identity underlying maps, so the transported composite unit is b a.
2. The first-factor action and the monoid right-unit axiom give
   q = gamma_P (S tensor a), p = gamma_Q (T tensor b), r = gamma_H (T tensor c).
   This follows by expanding each unit, using associator naturality and the
   monoidal triangle identity; it is an equality of ambient morphisms.
3. Apply the unit-compatible adjoint uniqueness lemma to the composite and direct
   adjunctions with common right adjoint Res_(phi psi). It gives v : BA iso D
   with v_M b a = c. The three adjunctions use the stated commutativity,
   coequalizers and tensor preservation assumptions only.
4. The S-linear map h = v_M b satisfies h a = c. By step 2 and linearity,
   h q = gamma_H (psi tensor c) = r (psi tensor M); the last equality expands c
   and uses the monoid right-unit axiom with associator and unitor naturality.
5. T-linearity gives v_M p = gamma_H (T tensor h). Precompose with T tensor q
   and apply step 4 to obtain the multiplication formula below. Since p and
   T tensor q are coequalizer projections, the factor is unique, so v is m0.
6. Write w = v inverse. The equation w_M c = b a and T-linearity give
   w_M r = gamma_Q (T tensor (b a)) = p (T tensor a), the inverse formula.
   The direct coequalizer determines this factor uniquely; its inverse laws
   hold because w is the inverse of v in the module category.
7. Naturality follows from v. Its unit equation is the equation of step 3,
   now in the module category. Uniqueness identifies m0 with leftAdjointUniq
   for these specified adjunctions. The source comparison uses the adjunctions
   in the reverse order, so its inverse is the same specified isomorphism.
-/
theorem internal_tensor_composition_unit_normalization
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimits (tensorLeft X)]
    [∀ X : C, PreservesColimits (tensorRight X)]
    {R S T : C} [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ] :
    ∃ m₀ : extendScalars φ ⋙ extendScalars ψ ≅ extendScalars (φ ≫ ψ),
      (∀ M : Mod C R,
        T ◁ extendπ φ M ≫ extendπ ψ ((extendScalars φ).obj M) ≫
            (m₀.hom.app M).hom =
          (α_ T S M.X).inv ≫ (T ◁ ψ ≫ μ[T]) ▷ M.X ≫ extendπ (φ ≫ ψ) M) ∧
      (∀ M : Mod C R,
        extendπ (φ ≫ ψ) M ≫ (m₀.inv.app M).hom =
          T ◁ ((λ_ M.X).inv ≫ η[S] ▷ M.X ≫ extendπ φ M) ≫
            extendπ ψ ((extendScalars φ).obj M)) ∧
      (∀ M : Mod C R,
        ((((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
          (comapComp φ ψ).symm).unit.app M) ≫
            (comap (φ ≫ ψ)).map (m₀.hom.app M) =
          (extendRestrictAdjunction (φ ≫ ψ)).unit.app M) ∧
      m₀ = (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
        (comapComp φ ψ).symm).leftAdjointUniq (extendRestrictAdjunction (φ ≫ ψ)) ∧
      m₀ = (extendScalarsComp φ ψ).symm := by
  let adj := ((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
    (comapComp φ ψ).symm
  let m := adj.leftAdjointUniq (extendRestrictAdjunction (φ ≫ ψ))
  have hu (M : Mod C R) :=
    Adjunction.unit_leftAdjointUniq_hom_app adj (extendRestrictAdjunction (φ ≫ ψ)) M
  have unit_hom {A B : C} [MonObj A] [MonObj B] [IsCommMonObj A]
      (f : A ⟶ B) [IsMonHom f] (M : Mod C A) :
      ((extendRestrictAdjunction f).unit.app M).hom = extendUnitHom f M := by
    change extendUnitHom f M ≫ 𝟙 _ = _
    exact Category.comp_id _
  have composite_unit_hom (M : Mod C R) : (adj.unit.app M).hom =
      extendUnitHom φ M ≫ extendUnitHom ψ ((extendScalars φ).obj M) := by
    change (((extendRestrictAdjunction φ).comp
      (extendRestrictAdjunction ψ)).unit.app M).hom ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_unit_app, comp_hom', comap_map_hom,
      unit_hom, unit_hom]
  have hu' (M : Mod C R) :
      extendUnitHom φ M ≫ extendUnitHom ψ ((extendScalars φ).obj M) ≫
        (m.hom.app M).hom = extendUnitHom (φ ≫ ψ) M := by
    have h := congrArg (fun f ↦ f.hom) (hu M)
    change (adj.unit.app M).hom ≫ (m.hom.app M).hom =
      ((extendRestrictAdjunction (φ ≫ ψ)).unit.app M).hom at h
    rw [composite_unit_hom, unit_hom, Category.assoc] at h
    exact h
  refine ⟨m, ?_, ?_, hu, rfl, ?_⟩
  · intro M
    let h := extendUnit ψ ((extendScalars φ).obj M) ≫ (comap ψ).map (m.hom.app M)
    have hh : extendπ φ M ≫ h.hom = ψ ▷ M.X ≫ extendπ (φ ≫ ψ) M := by
      rw [← whiskerLeft_extendUnitHom_smul' φ M, Category.assoc, act_hom h]
      change S ◁ extendUnitHom φ M ≫ S ◁ h.hom ≫
        ψ ▷ _ ≫ γ[T,((extendScalars (φ ≫ ψ)).obj M).X] = _
      rw [← whiskerLeft_comp_assoc]
      change S ◁ (extendUnitHom φ M ≫ extendUnitHom ψ ((extendScalars φ).obj M) ≫
        (m.hom.app M).hom) ≫ ψ ▷ _ ≫ _ = _
      rw [hu']
      change S ◁ extendUnitHom (φ ≫ ψ) M ≫
        ψ ▷ (extendScalarsObj (φ ≫ ψ) M).X ≫ γ[T,(extendScalarsObj (φ ≫ ψ) M).X] = _
      rw [whisker_exchange_assoc, whiskerLeft_extendUnitHom_smul']
    change T ◁ extendπ φ M ≫ extendπ ψ (extendScalarsObj φ M) ≫
      (m.hom.app M).hom = _
    rw [← whiskerLeft_extendUnitHom_smul' ψ (extendScalarsObj φ M),
      Category.assoc, act_hom (m.hom.app M),
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
    rw [Category.assoc]
    change T ◁ (extendπ φ M ≫ h.hom) ≫ _ = _
    rw [hh, whiskerLeft_comp_assoc, whiskerLeft_extendπ_smul,
      associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
  · intro M
    have hi : extendUnitHom (φ ≫ ψ) M ≫ (m.inv.app M).hom =
        extendUnitHom φ M ≫ extendUnitHom ψ ((extendScalars φ).obj M) := by
      rw [← hu', Category.assoc, Category.assoc]
      have hm : (m.hom.app M).hom ≫ (m.inv.app M).hom = 𝟙 _ := by
        exact congrArg (fun f ↦ f.hom) (m.hom_inv_id_app M)
      rw [hm]
      exact congrArg (extendUnitHom φ M ≫ ·) (Category.comp_id _)
    change extendπ (φ ≫ ψ) M ≫ (m.inv.app M).hom =
      T ◁ extendUnitHom φ M ≫ extendπ ψ ((extendScalars φ).obj M)
    rw [← whiskerLeft_extendUnitHom_smul' (φ ≫ ψ) M, Category.assoc,
      act_hom (m.inv.app M), ← whiskerLeft_comp_assoc, hi,
      whiskerLeft_comp_assoc, whiskerLeft_extendUnitHom_smul']
  · apply Iso.ext
    ext M
    rfl

end CategoryTheory.Mod
