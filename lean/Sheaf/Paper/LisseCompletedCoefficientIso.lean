/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module
public import Sheaf.SixFunctors.IntegralLisseReductionData
public import Sheaf.Paper.AdicLisseModule
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Residue-normalized identification of completed coefficients. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private def coefficientDiagramMap (c : IntegralLisseReductionEquivalence l E X) :
    adicLisseRingSystem X
      (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E))) ⟶ integralLisseFiniteDiagram l E X :=
  NatTrans.ofOpSequence (fun n ↦ (c.finiteConstant n).hom) (by
    intro n
    simp only [adicLisseRingSystem, integralLisseFiniteDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (integralLisseFiniteRing l E X n).property
    simp only [constantSheaf, Functor.comp_map]
    change (toSheafify _ _ ≫ sheafifyMap _ _ ≫ _) = _
    rw [← Category.assoc, ← toSheafify_naturality]
    ext U a
    change (c.finiteConstant n).hom.hom.app U
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))))).app U
        (Padic.coefficientExtensionTransition l E (n + 1) a)) =
      (integralLisseFiniteTransition l E X n).hom.app U
        ((c.finiteConstant (n + 1)).hom.hom.app U
          ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 2))))).app U a))
    rw [c.finiteConstant_sections, c.finiteConstant_sections]
    rfl)

private def coefficientDiagramIso (c : IntegralLisseReductionEquivalence l E X) :
    adicLisseRingSystem X
      (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E))) ≅ integralLisseFiniteDiagram l E X := by
  exact NatIso.ofComponents (fun n ↦ c.finiteConstant n.unop)
    (fun {_ _} f ↦ (coefficientDiagramMap l E X c).naturality f)

/-- The continuous integral coefficient sheaf is the completed constant coefficient ring,
with its prescribed residue projections.
Source: BS 6.8.2(1), 6.8.4(1)
(blueprint: lem-per-lisse-completed-coefficient-iso).

Proof: The supplied finite-constant isomorphisms intertwine successive reductions: check
this on constant sections before sheafification. They therefore form a natural isomorphism
of the two coefficient diagrams. The supplied coefficient cone is limiting and its legs
are the actual residue maps. Uniqueness of limits, followed by the limit of the diagram
isomorphism, gives the coefficient isomorphism and every projection equation. -/
theorem completed_coefficient_iso_exists (c : IntegralLisseReductionEquivalence l E X) :
    ∃ e : lisseIntegerSheafSized l E X ≅ adicLisseCompletedRing X
      (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E))),
      ∀ n : ℕ, e.hom ≫ limit.π _ (op n) = integralLisseReduction l E X n ≫
        (c.finiteConstant n).inv := by
  let α := coefficientDiagramIso l E X c
  let e := c.coefficientLimit.conePointUniqueUpToIso (limit.isLimit _)
  let β : lisseIntegerSheafSized l E X ≅ limit (integralLisseFiniteDiagram l E X) := e
  refine ⟨β ≪≫ (lim.mapIso α).symm, ?_⟩
  intro n
  change (β.hom ≫ lim.map α.inv) ≫ limit.π _ (op n) = _
  rw [Category.assoc]
  erw [limMap_π]
  rw [← Category.assoc]
  change (β.hom ≫ limit.π _ (op n)) ≫ (c.finiteConstant n).inv = _
  exact congrArg (fun f : lisseIntegerSheafSized l E X ⟶ integralLisseFiniteRing l E X n ↦
    f ≫ (c.finiteConstant n).inv)
      ((IsLimit.conePointUniqueUpToIso_hom_comp c.coefficientLimit
        (limit.isLimit _) (op n)).trans (c.coefficientCone_app n))
end AlgebraicGeometry.ProEtale
