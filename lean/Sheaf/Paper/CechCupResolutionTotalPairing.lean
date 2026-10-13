/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct
import Sheaf.Paper.CechCupResolutionBetaClassPairing

/-! # The two axis squares of the signed total Cech pairing

Source: Stacks Project, Tags 07MB and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The signed total Cech pairing preserves both axes: restriction of global
resolution cocycles and augmentation of coefficient Cech cocycles.
Source: Stacks Project, Tag 07MB (signed total map) and Tag 0FKV, proof, final diagram.
(blueprint: lem-sc-cech-cup-resolution-total-pairing)

Proof: take the unique bilinear sheaf cup product characterized by computing
resolution pairings. Precompose its two arguments with A.iso.inv and B.iso.inv,
and postcompose with C.iso.hom; linear-map composition constructs t explicitly.
For the alpha formula, alpha_class identifies each input with iso applied to
its resolution class. Cancel the input isomorphisms, apply the characterization
of the sheaf cup product to D and the given paired cocycle, then use C.alpha_class.
For the beta formula, apply cupCechResolution_beta_class_pairing to this same
characterized cup product, postcompose with C.iso.hom, and cancel C.iso.inv.
The beta theorem is the remaining signed Alexander--Whitney cochain obligation;
its separate docstring gives that calculation. The present proof uses the
computing comparisons, but never chooses an unconstrained total pairing. -/
theorem cupCechResolution_total_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap A.alpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.alpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.alpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c)) := by
  obtain ⟨cup, hcup, _⟩ := exists_unique_moduleCupProduct F G p q
  let t := (cup.compl₁₂ (A.iso p).inv.hom (B.iso q).inv.hom).compr₂
    (C.iso (p + q)).hom.hom
  refine ⟨t, ?_, ?_⟩
  · intro a b c hc
    change (C.iso (p + q)).hom
      (cup ((A.iso p).inv (HomologicalComplex.homologyMap A.alpha p
        (cupCycleClass _ p a)))
        ((B.iso q).inv (HomologicalComplex.homologyMap B.alpha q
          (cupCycleClass _ q b)))) = _
    rw [← A.alpha_class p a, ← B.alpha_class q b]
    simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
    rw [hcup D a b c hc]
    exact C.alpha_class (p + q) c
  · intro a b c hc
    change (C.iso (p + q)).hom
      (cup ((A.iso p).inv (HomologicalComplex.homologyMap A.beta p
        (cupCycleClass _ p a)))
        ((B.iso q).inv (HomologicalComplex.homologyMap B.beta q
          (cupCycleClass _ q b)))) = _
    rw [cupCechResolution_beta_class_pairing U D A B C p q cup hcup a b c hc]
    simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

end
end AlgebraicGeometry.Scheme.Modules
