/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Invertibility of the scalar transpose of reduced evaluation

Source: the finite-free argument and extension-restriction adjunction of
`lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The completed-ring transpose of scalar-reduced evaluation is invertible.
This is a scalar assertion with no chosen representatives and no signed chain map.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2;
Stacks Tags 07A4, 07A6, 08J7 and 08J9.
(blueprint: lem-sf-integral-hom-scalar-evaluation-invertible).

Proof: the restricted finite quotient is the cone of multiplication by the
(n+1)-st uniformizer power on the completed unit. Consequently restricted
reduction is tensoring with this two-term perfect coefficient object. Internal
Hom in its second argument is exact. Apply it to the same two-term coefficient
construction. On the two free terms, the natural coefficient action on Hom is
the unit identification, so its cone map is an isomorphism. The tensor comparison
and scalar adjunction identify that action with the map displayed here: use
m.normalization and the unit x maps to 1 tensor x on K-flat representatives,
then localization. The middle scalar counit is exactly the counit appearing
in this mate calculation. This only proves invertibility, not a prescribed
chain representative or an equality of two evaluation formulas. Transport
between tensor representatives and between choices of adjunction conjugates
the mate by isomorphisms, so invertibility holds for the supplied a and m.
No perfection hypothesis on K or L is used; perfection is only in the
coefficient quotient. The zero quotient and empty site are included. -/
theorem scalar_reduced_evaluation_transpose_isIso
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    let H := (hom.{t, u} Y R).obj (op K, L)
    let X := U.obj (F.obj H)
    IsIso ((a.adjunction K).homEquiv X (U.obj (F.obj L))
      (adj.homEquiv (a.tensor.obj (K, X)) (F.obj L)
        (m.mu.hom.app (K, X) ≫
          m.target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
          m.mu.inv.app (K, H) ≫ F.map ((a.adjunction K).counit.app L)))) := by sorry

end WeilConjectures.IntegralHom
