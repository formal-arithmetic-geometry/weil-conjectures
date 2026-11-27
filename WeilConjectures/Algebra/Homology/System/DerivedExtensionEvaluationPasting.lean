/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose

/-! # Pasting evaluation squares of normalized derived extensions

Representative-level tools for comparing normalized derived left extensions along exact
functors: invertibility of the derived evaluation mate on a common resolving class, the
cochain representatives and adjunction transposes of its inverse, and a pasting lemma
reducing compatibilities of derived evaluation squares to the underlying ordinary squares.

## Implementation details

The pasting lemmas are stated for arbitrary categories and functors, so that rewriting in
their proofs never unfolds the concrete functors to which they are applied.

## References

* Stacks Project, Tags 06YT, 0FND
-/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace SheafOfModules

section General

universe a av b bv c cv d dv da db dc dd

variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  {A' : Type c} [Category.{cv} A'] [Abelian A'] [HasDerivedCategory.{dc} A']
  {B' : Type d} [Category.{dv} B'] [Abelian B'] [HasDerivedCategory.{dd} B']
  {R₁ : B ⥤ A} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  {R₂ : B' ⥤ A'} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  {p₁ : CochainComplex A ℤ → Prop} {p₂ : CochainComplex A' ℤ → Prop}
  (d₁ : SystemDerivedLeftExtension R₁ p₁) (d₂ : SystemDerivedLeftExtension R₂ p₂)
  (G : A ⥤ A') [G.Additive]
  (H : B ⥤ B') [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (GD : DerivedCategory A ⥤ DerivedCategory A')
  (γ : (DerivedCategory.Q (C := A)) ⋙ GD ≅
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (τD : R₁.mapDerivedCategory ⋙ GD ⟶ H.mapDerivedCategory ⋙ R₂.mapDerivedCategory)

/-- The derived evaluation mate is invertible as soon as both normalized models compute
on a common class of complexes resolving every complex. -/
theorem derivedExtensionMate_isIso_of_resolving
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hτ : ∀ K : CochainComplex B ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          R₂.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
          γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (ι : G ⋙ d₂.ordinary ≅ d₁.ordinary ⋙ H)
    (hι : ∀ P, d₂.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      G.map (d₁.ordinaryAdj.unit.app P) ≫ τ.app (d₁.ordinary.obj P))
    (q : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), q P ∧ QuasiIso f)
    (h₁ : ∀ P, q P → p₁ P)
    (h₂ : ∀ P, q P → p₂ ((G.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (derivedExtensionMate d₁ d₂ H GD τD) :=
  derivedExtensionMate_isIso { d₁ with computes := fun P hP ↦ d₁.computes P (h₁ P hP) }
    d₂ G H GD γ τD τ hτ ι hι res h₂

/-- Any isomorphism whose inverse is the derived evaluation mate has the prescribed
cochain representative. -/
theorem derivedExtensionMate_iso_rep
    (e : d₁.derived ⋙ H.mapDerivedCategory ≅ GD ⋙ d₂.derived)
    (he : e.inv = derivedExtensionMate d₁ d₂ H GD τD)
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hτ : ∀ K : CochainComplex B ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          R₂.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
          γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (ι : G ⋙ d₂.ordinary ≅ d₁.ordinary ⋙ H)
    (hι : ∀ P, d₂.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      G.map (d₁.ordinaryAdj.unit.app P) ≫ τ.app (d₁.ordinary.obj P))
    (P : CochainComplex A ℤ) :
    e.hom.app (DerivedCategory.Q.obj P) ≫ d₂.derived.map (γ.hom.app P) ≫
        d₂.comparison.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategory.map (d₁.comparison.app P) ≫
        H.mapDerivedCategoryFactors.hom.app
          ((d₁.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ι (.up ℤ)).inv.app P) := by
  rw [← cancel_epi (e.inv.app (DerivedCategory.Q.obj P)), Iso.inv_hom_id_app_assoc, he,
    reassoc_of% (derivedExtensionMate_rep d₁ d₂ G H GD γ τD τ hτ ι hι P),
    ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Any isomorphism whose inverse is the derived evaluation mate intertwines the two
derived adjunction transposes. -/
theorem derivedExtensionMate_iso_transpose
    (e : d₁.derived ⋙ H.mapDerivedCategory ≅ GD ⋙ d₂.derived)
    (he : e.inv = derivedExtensionMate d₁ d₂ H GD τD)
    (P : DerivedCategory A) (M : DerivedCategory B) (f : d₁.derived.obj P ⟶ M) :
    d₂.adjunction.homEquiv (GD.obj P) (H.mapDerivedCategory.obj M)
      (e.inv.app P ≫ H.mapDerivedCategory.map f) =
    GD.map (d₁.adjunction.homEquiv P M f) ≫ τD.app M := by
  rw [he]
  exact adjunctionMate_transpose d₁.adjunction d₂.adjunction (TwoSquare.mk _ _ _ _ τD) P M f

/-- Transposed form of a pasting of derived evaluation squares: if an evaluated derived
comparison is the inverse of the derived evaluation mate, then the transposes of two
below-level identifications are intertwined by the comparisons. -/
theorem derivedExtensionMate_iso_lower
    {Aₘ : Type*} [Category Aₘ] [Abelian Aₘ] [HasDerivedCategory Aₘ]
    {Aₘ' : Type*} [Category Aₘ'] [Abelian Aₘ'] [HasDerivedCategory Aₘ']
    (e : d₁.derived ⋙ H.mapDerivedCategory ≅ GD ⋙ d₂.derived)
    (dE : H.mapDerivedCategory ⋙ R₂.mapDerivedCategory ≅ R₁.mapDerivedCategory ⋙ GD)
    (he : e.inv = derivedExtensionMate d₁ d₂ H GD dE.inv)
    (L₁D : DerivedCategory Aₘ ⥤ DerivedCategory B)
    (L₂D : DerivedCategory Aₘ' ⥤ DerivedCategory B')
    (GₘD : DerivedCategory Aₘ ⥤ DerivedCategory Aₘ')
    (T₁ : DerivedCategory Aₘ ⥤ DerivedCategory A)
    (T₂ : DerivedCategory Aₘ' ⥤ DerivedCategory A')
    (β₁ : L₁D ⋙ R₁.mapDerivedCategory ≅ T₁)
    (β₂ : L₂D ⋙ R₂.mapDerivedCategory ≅ T₂)
    (σ : T₁ ⋙ GD ≅ GₘD ⋙ T₂) (comp : L₁D ⋙ H.mapDerivedCategory ≅ GₘD ⋙ L₂D)
    (h : ∀ P, R₂.mapDerivedCategory.map (comp.hom.app P) ≫ β₂.hom.app (GₘD.obj P) =
      dE.hom.app (L₁D.obj P) ≫ GD.map (β₁.hom.app P) ≫ σ.hom.app P)
    (P : DerivedCategory Aₘ) :
    H.mapDerivedCategory.map ((d₁.adjunction.homEquiv _ _).symm (β₁.inv.app P)) ≫
        comp.hom.app P =
      e.hom.app (T₁.obj P) ≫ d₂.derived.map (σ.hom.app P) ≫
        (d₂.adjunction.homEquiv _ _).symm (β₂.inv.app (GₘD.obj P)) := by
  rw [← cancel_epi (e.inv.app (T₁.obj P)), Iso.inv_hom_id_app_assoc, ← Category.assoc]
  apply (d₂.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    derivedExtensionMate_iso_transpose d₁ d₂ H GD dE.inv e he, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_left]
  erw [Equiv.apply_symm_apply]
  rw [← cancel_mono (β₂.hom.app (GₘD.obj P)), Category.assoc, Category.assoc, h P]
  simp

end General

/-- Two natural transformations out of a derived category agree as soon as they agree on
a class of complexes resolving every complex. -/
theorem derivedCategory_natTrans_ext_of_resolving {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {E : Type*} [Category E] {Φ Ψ : DerivedCategory A ⥤ E}
    (α β : Φ ⟶ Ψ) (q : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), q P ∧ QuasiIso f)
    (h : ∀ P, q P → α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) :
    α = β := by
  ext X
  obtain ⟨P, f, hP, hf⟩ := res (DerivedCategory.Q.objPreimage X)
  have := hf
  let e : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  rw [← cancel_epi (Φ.map e.hom), α.naturality, β.naturality, h P hP]

section Pasting

variable {A A₀ A' A₀' B B' : Type*} [Category A] [Category A₀] [Category A'] [Category A₀']
  [Category B] [Category B'] [Abelian A] [Abelian A₀] [Abelian A'] [Abelian A₀'] [Abelian B]
  [Abelian B'] [HasDerivedCategory A] [HasDerivedCategory A₀] [HasDerivedCategory A']
  [HasDerivedCategory A₀'] [HasDerivedCategory B] [HasDerivedCategory B']
  {L₁ : A ⥤ B} {L₂ : A' ⥤ B'} [L₁.Additive] [L₂.Additive]
  {E₁ : A ⥤ A₀} {E₂ : A' ⥤ A₀'} [E₁.Additive] [E₂.Additive]
  {R₁ : B ⥤ A₀} {R₂ : B' ⥤ A₀'} [R₁.Additive] [R₂.Additive]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  {G : A ⥤ A'} {G₀ : A₀ ⥤ A₀'} {H : B ⥤ B'} [G.Additive] [G₀.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- Pasting of derived evaluation squares: a derived comparison of left extensions is
compatible with given evaluations of the two extensions, provided all the squares are
computed by ordinary squares on a resolving class and the ordinary squares paste. -/
theorem derivedEvaluation_pasting
    (L₁D : DerivedCategory A ⥤ DerivedCategory B)
    (L₂D : DerivedCategory A' ⥤ DerivedCategory B')
    (c₁ : DerivedCategory.Q ⋙ L₁D ⟶
      L₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c₂ : DerivedCategory.Q ⋙ L₂D ⟶
      L₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (T₁ : DerivedCategory A ⥤ DerivedCategory A₀)
    (T₂ : DerivedCategory A' ⥤ DerivedCategory A₀')
    (ε₁ : DerivedCategory.Q ⋙ T₁ ⟶
      E₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε₂ : DerivedCategory.Q ⋙ T₂ ⟶
      E₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β₁ : L₁D ⋙ R₁.mapDerivedCategory ≅ T₁)
    (β₂ : L₂D ⋙ R₂.mapDerivedCategory ≅ T₂)
    (b₁ : L₁ ⋙ R₁ ≅ E₁) (b₂ : L₂ ⋙ R₂ ≅ E₂)
    (comp : L₁D ⋙ H.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ L₂D)
    (o : L₁ ⋙ H ≅ G ⋙ L₂)
    (dE : H.mapDerivedCategory ⋙ R₂.mapDerivedCategory ≅
      R₁.mapDerivedCategory ⋙ G₀.mapDerivedCategory) (ev : H ⋙ R₂ ≅ R₁ ⋙ G₀)
    (σ : T₁ ⋙ G₀.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ T₂)
    (t : E₁ ⋙ G₀ ≅ G ⋙ E₂)
    (q : CochainComplex A ℤ → Prop) (q₂ : CochainComplex A' ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), q P ∧ QuasiIso f)
    (hq : ∀ K, q K → q₂ ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (hε : ∀ K, q K → IsIso (ε₂.app ((G.mapHomologicalComplex (.up ℤ)).obj K)))
    (hcomp : ∀ K, q K → comp.hom.app (DerivedCategory.Q.obj K) ≫
        L₂D.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        c₂.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (c₁.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app K))
    (hβ₁ : ∀ K, q K → β₁.hom.app (DerivedCategory.Q.obj K) ≫ ε₁.app K =
      R₁.mapDerivedCategory.map (c₁.app K) ≫
        R₁.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₁ (.up ℤ)).hom.app K))
    (hβ₂ : ∀ K, q₂ K → β₂.hom.app (DerivedCategory.Q.obj K) ≫ ε₂.app K =
      R₂.mapDerivedCategory.map (c₂.app K) ≫
        R₂.mapDerivedCategoryFactors.hom.app ((L₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₂ (.up ℤ)).hom.app K))
    (hσ : ∀ K, q K → σ.hom.app (DerivedCategory.Q.obj K) ≫
        T₂.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        ε₂.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      G₀.mapDerivedCategory.map (ε₁.app K) ≫
        G₀.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app K))
    (hdE : ∀ M : CochainComplex B ℤ, dE.hom.app (DerivedCategory.Q.obj M) ≫
        G₀.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.hom.app M) ≫
        G₀.mapDerivedCategoryFactors.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj M) =
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app M) ≫
        R₂.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ev.hom (.up ℤ)).app M))
    (hord : ∀ X : A, ev.hom.app (L₁.obj X) ≫ G₀.map (b₁.hom.app X) ≫ t.hom.app X =
      R₂.map (o.hom.app X) ≫ b₂.hom.app (G.obj X))
    (P : DerivedCategory A) :
    R₂.mapDerivedCategory.map (comp.hom.app P) ≫ β₂.hom.app (G.mapDerivedCategory.obj P) =
      dE.hom.app (L₁D.obj P) ≫ G₀.mapDerivedCategory.map (β₁.hom.app P) ≫ σ.hom.app P := by
  let α : L₁D ⋙ H.mapDerivedCategory ⋙ R₂.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ T₂ :=
    whiskerRight comp.hom R₂.mapDerivedCategory ≫ whiskerLeft G.mapDerivedCategory β₂.hom
  let α' : L₁D ⋙ H.mapDerivedCategory ⋙ R₂.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ T₂ :=
    whiskerLeft L₁D dE.hom ≫ whiskerRight β₁.hom G₀.mapDerivedCategory ≫ σ.hom
  have key : α = α' := by
    refine derivedCategory_natTrans_ext_of_resolving α α' q res (fun K hK ↦ ?_)
    have := hε K hK
    dsimp only [α, α', NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [← cancel_mono (T₂.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      ε₂.app ((G.mapHomologicalComplex (.up ℤ)).obj K)), Category.assoc, Category.assoc,
      Category.assoc, hσ K hK, ← β₂.hom.naturality_assoc]
    dsimp only [Functor.comp_map, Functor.comp_obj]
    rw [hβ₂ _ (hq K hK)]
    have hc := congrArg R₂.mapDerivedCategory.map (hcomp K hK)
    simp only [Functor.map_comp] at hc
    rw [reassoc_of% hc, ← G₀.mapDerivedCategory.map_comp_assoc, hβ₁ K hK]
    simp only [Functor.map_comp, Category.assoc]
    erw [R₂.mapDerivedCategoryFactors.hom.naturality_assoc,
      G₀.mapDerivedCategoryFactors.hom.naturality_assoc,
      ← dE.hom.naturality_assoc (c₁.app K)]
    dsimp only [Functor.comp_map, Functor.comp_obj]
    rw [reassoc_of% (hdE ((L₁.mapHomologicalComplex (.up ℤ)).obj K))]
    have hQ : DerivedCategory.Q.map ((R₂.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app K)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₂ (.up ℤ)).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj K)) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ev.hom (.up ℤ)).app
          ((L₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        DerivedCategory.Q.map ((G₀.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex b₁ (.up ℤ)).hom.app K)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app K) := by
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
        ← DerivedCategory.Q.map_comp]
      congr 1
      ext i
      exact (hord (K.X i)).symm
    rw [hQ]
  exact congr_app key P

/-- The case of `derivedEvaluation_pasting` in which both evaluations are identifications
with the identity functor. -/
theorem derivedEvaluation_pasting_id {R₁ : B ⥤ A} {R₂ : B' ⥤ A'}
    [R₁.Additive] [R₂.Additive]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (L₁D : DerivedCategory A ⥤ DerivedCategory B)
    (L₂D : DerivedCategory A' ⥤ DerivedCategory B')
    (c₁ : DerivedCategory.Q ⋙ L₁D ⟶
      L₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c₂ : DerivedCategory.Q ⋙ L₂D ⟶
      L₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β₁ : L₁D ⋙ R₁.mapDerivedCategory ≅ 𝟭 _)
    (β₂ : L₂D ⋙ R₂.mapDerivedCategory ≅ 𝟭 _)
    (b₁ : L₁ ⋙ R₁ ≅ 𝟭 A) (b₂ : L₂ ⋙ R₂ ≅ 𝟭 A')
    (comp : L₁D ⋙ H.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ L₂D)
    (o : L₁ ⋙ H ≅ G ⋙ L₂)
    (dE : H.mapDerivedCategory ⋙ R₂.mapDerivedCategory ≅
      R₁.mapDerivedCategory ⋙ G.mapDerivedCategory) (ev : H ⋙ R₂ ≅ R₁ ⋙ G)
    (q : CochainComplex A ℤ → Prop) (q₂ : CochainComplex A' ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), q P ∧ QuasiIso f)
    (hq : ∀ K, q K → q₂ ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (hcomp : ∀ K, q K → comp.hom.app (DerivedCategory.Q.obj K) ≫
        L₂D.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        c₂.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (c₁.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app K))
    (hβ₁ : ∀ K, q K → β₁.hom.app (DerivedCategory.Q.obj K) =
      R₁.mapDerivedCategory.map (c₁.app K) ≫
        R₁.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₁ (.up ℤ)).hom.app K))
    (hβ₂ : ∀ K, q₂ K → β₂.hom.app (DerivedCategory.Q.obj K) =
      R₂.mapDerivedCategory.map (c₂.app K) ≫
        R₂.mapDerivedCategoryFactors.hom.app ((L₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b₂ (.up ℤ)).hom.app K))
    (hdE : ∀ M : CochainComplex B ℤ, dE.hom.app (DerivedCategory.Q.obj M) ≫
        G.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.hom.app M) ≫
        G.mapDerivedCategoryFactors.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj M) =
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app M) ≫
        R₂.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ev.hom (.up ℤ)).app M))
    (hord : ∀ X : A, ev.hom.app (L₁.obj X) ≫ G.map (b₁.hom.app X) =
      R₂.map (o.hom.app X) ≫ b₂.hom.app (G.obj X))
    (P : DerivedCategory A) :
    R₂.mapDerivedCategory.map (comp.hom.app P) ≫ β₂.hom.app (G.mapDerivedCategory.obj P) =
      dE.hom.app (L₁D.obj P) ≫ G.mapDerivedCategory.map (β₁.hom.app P) := by
  have h := derivedEvaluation_pasting (E₁ := 𝟭 A) (E₂ := 𝟭 A') (G₀ := G) L₁D L₂D c₁ c₂
    (𝟭 _) (𝟭 _) (Iso.refl _).hom (Iso.refl _).hom β₁ β₂ b₁ b₂ comp o dE ev (Iso.refl _)
    (Iso.refl _) q q₂ res hq (fun K _ ↦ by dsimp; infer_instance) hcomp
    (fun K hK ↦ by simpa using hβ₁ K hK) (fun K hK ↦ by simpa using hβ₂ K hK)
    (fun K _ ↦ ?_) hdE (fun X ↦ by simpa using hord X) P
  · simpa using h
  · have e : (NatIso.mapHomologicalComplex (Iso.refl (𝟭 A ⋙ G)) (.up ℤ)).hom.app K = 𝟙 _ := by
      ext i
      simp
    rw [e]
    dsimp only [Iso.refl_hom, NatTrans.id_app, Functor.id_map]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

end Pasting

section ExactSquare

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The square isomorphism induced on derived categories is computed by the given
square on cochain complexes. -/
theorem mapDerivedCategorySquareIso_hom_model (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) =
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ P]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- The inverse square isomorphism induced on derived categories is computed by the
inverse square on cochain complexes. -/
theorem mapDerivedCategorySquareIso_inv_model (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).inv.app (DerivedCategory.Q.obj P) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) =
    G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P) := by
  rw [← cancel_epi ((Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P)),
    Iso.hom_inv_id_app_assoc, reassoc_of% (mapDerivedCategorySquareIso_hom_model e P),
    ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
    e.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end ExactSquare

end SheafOfModules
