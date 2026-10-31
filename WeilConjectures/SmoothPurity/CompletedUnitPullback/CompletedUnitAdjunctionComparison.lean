/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularLimitComparison
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Adjunction transport of the regular completed-unit comparison

Source: Stacks 0941 and the normalized reconstruction adjunction calculus.
The geometric limit comparison is transported through an arbitrary supplied
coefficient-derived-system calculus; this is the categorical part of the strict
comparison theorem.
(blueprint: lem-pur-completed-unit-adjunction-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

private theorem adjunct_projection
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (V : B ⥤ C) (L : A ⥤ C) (R : C ⥤ A) (a : L ⊣ R)
    (ρ : F ⋙ V ≅ L) (π : G ⟶ V ⋙ R)
    (hu : ∀ X, adj.unit.app X ≫ π.app (F.obj X) =
      a.unit.app X ≫ R.map (ρ.inv.app X))
    (X : A) (Y : B) (Z : C) (f : F.obj X ⟶ Y) (g : V.obj Y ⟶ Z) :
    adj.homEquiv X Y f ≫ π.app Y ≫ R.map g =
      a.homEquiv X Z (ρ.inv.app X ≫ V.map f ≫ g) := by
  rw [adj.homEquiv_unit, Category.assoc,
    ← Category.assoc (G.map f) (π.app Y), π.naturality f]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  rw [← Category.assoc (adj.unit.app X) (π.app (F.obj X)), hu]
  simp only [a.homEquiv_unit, Functor.map_comp, Category.assoc]

universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Transport a regular limit comparison through a supplied reduction adjunction.

Proof: transpose the comparison isomorphism through `S.adjunction`.  The
adjunction unit projection formula identifies each finite evaluation of the
transpose with the finite reduction map.  The normalized-system hypothesis on
the regular sequence and the reconstruction theorem make the relevant unit and
counit isomorphisms; the triangle identity then makes the transpose itself an
isomorphism.  Naturality of the finite projections and cancellation in the
finite adjunction give the displayed equation.  No characteristic or
invertibility assumption on `W` is used in this transport step.
(blueprint: lem-pur-completed-unit-adjunction-comparison). -/
theorem adjunctionComparison
    (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W)
    (b : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n))
    (_hb : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V),
      HEq ((b n).hom.val.app V x) x)
    (d : integralConstantCoefficientObject l E W ≅
      (coefficientSequenceLimit l E W).obj (systemObject l E W))
    (hd : IsNormalizedCoefficientSequence l E W (systemObject l E W) ∧
      IntegralOnSlice.IsComplete l E W none (integralConstantCoefficientObject l E W) ∧
      ∀ n : ℕ,
        d.hom ≫ (coefficientSequenceProjection l E W n).app (systemObject l E W) ≫
            (coefficientFiniteDerivedRestriction l E W n).map
              (evaluationSingle l E W n).hom ≫
                (coefficientFiniteDerivedRestriction l E W n).map
                  ((DerivedCategory.singleFunctor _ 0).map (b n).hom) =
          (coefficientFiniteAdjunction l E W n).unit.app
              (integralConstantCoefficientObject l E W) ≫
            (coefficientFiniteDerivedRestriction l E W n).map
              (constantCoefficientReductionMap l E W n)) :
    ∃ c : S.reduction.obj (integralConstantCoefficientObject l E W) ≅ systemObject l E W,
      ∀ n : ℕ,
        (coefficientSequenceDerivedEvaluation l E W n).map c.hom ≫
          (evaluationSingle l E W n).hom ≫
          (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).map
            (b n).hom =
        (S.reductionEvaluation n).hom.app (integralConstantCoefficientObject l E W) ≫
          constantCoefficientReductionMap l E W n := by
  let X := integralConstantCoefficientObject l E W
  let Y := systemObject l E W
  let f : S.reduction.obj X ⟶ Y := (S.adjunction.homEquiv X Y).symm d.hom
  have : IsIso (S.adjunction.counit.app Y) :=
    ((purNormalizedReconstructionOfScheme l E W S).1 Y hd.1).2
  have : IsIso f := by
    dsimp only [f]
    rw [S.adjunction.homEquiv_counit]
    infer_instance
  refine ⟨asIso f, ?_⟩
  intro n
  let V := coefficientSequenceDerivedEvaluation l E W n
  let L := coefficientFiniteDerivedExtension l E W n
  let R := coefficientFiniteDerivedRestriction l E W n
  let a := coefficientFiniteAdjunction l E W n
  let g := (evaluationSingle l E W n).hom ≫
    (DerivedCategory.singleFunctor _ 0).map (b n).hom
  have hp := adjunct_projection S.adjunction V L R a (S.reductionEvaluation n)
    (coefficientSequenceProjection l E W n) (fun P ↦ S.unit_projection P n)
    X Y _ f g
  have he : a.homEquiv X _
      ((S.reductionEvaluation n).inv.app X ≫ V.map f ≫ g) =
      a.homEquiv X _ (constantCoefficientReductionMap l E W n) := by
    rw [← hp]
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
    simpa only [g, Functor.map_comp, Category.assoc, Adjunction.homEquiv_unit]
      using hd.2.2 n
  have h := (a.homEquiv X _).injective he
  apply (cancel_epi ((S.reductionEvaluation n).inv.app X)).mp
  simpa only [asIso_hom, X, V, g, Category.assoc, Iso.inv_hom_id_app_assoc] using h

end WeilConjectures.CompletedUnitPullback
