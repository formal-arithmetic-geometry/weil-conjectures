/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints

/-!
# Derivation coefficients on the dual-number diagonal

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, the square-zero
pushout calculation; blueprint `sk-d-tangent`, the dual-number description.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.GrpObj

/-- On the dual-number diagonal the first-order coefficient is the sum of the
first-order coefficients on the two axes, after identifying the common reduction.
Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, applied sectionwise.
(blueprint: lem-ag-dual-numbers-diagonal-coefficients)

Proof: Compose with the comparison from the iterated thickening S[epsilon][delta]
to the product. On sections the axis restrictions take a double dual number to
its first dual-number component, and apply the constant projection to both of
its components, respectively. The diagonal sends epsilon and delta to epsilon.
It kills their product, since epsilon squared is zero. Write a double dual
number as its constant, epsilon, delta, and epsilon-delta terms: the coefficient
of epsilon on the diagonal is the sum of its epsilon and delta coefficients.
The comparison composed with the diagonal is the categorical diagonal, because
both its projections are identities. Its restrictions to the two axes are the
categorical axes, by the corresponding projection identities. Apply the
coefficient calculation to the section map of f on each target open.
The three equations of reductions identify all inverse-image opens and the
pushforward module structures with those of g. Equality transport therefore
turns the coefficient identity into exactly the displayed derivation identity.
No finiteness or smoothness assumption is needed; the calculation holds for the
zero ring as well. -/
theorem infDerivation_diagonal_coefficients {S : Scheme.{u}} (X : Over S)
    (f : Scheme.dualNumbersOver S ⊗ Scheme.dualNumbersOver S ⟶ X)
    (g : S ⟶ X.left)
    (hd : S.dualNumbersι ≫
      (lift (𝟙 (Scheme.dualNumbersOver S)) (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = g)
    (h₁ : S.dualNumbersι ≫
      (lift (𝟙 (Scheme.dualNumbersOver S))
        (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S) ≫ f).left = g)
    (h₂ : S.dualNumbersι ≫
      (lift (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S)
        (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = g) :
    let D₀ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      X.hom.pullbackPresheafHom :=
      hd ▸ infDerivation X (lift (𝟙 _) (𝟙 _) ≫ f)
    let D₁ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      X.hom.pullbackPresheafHom :=
      h₁ ▸ infDerivation X (lift (𝟙 _) (toUnit _ ≫ Scheme.dualNumbersιOver S) ≫ f)
    let D₂ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      X.hom.pullbackPresheafHom :=
      h₂ ▸ infDerivation X (lift (toUnit _ ≫ Scheme.dualNumbersιOver S) (𝟙 _) ≫ f)
    ∀ {V : (TopologicalSpace.Opens X.left)ᵒᵖ} (a : Γ(X.left, V.unop)),
      D₀.d a = D₁.d a + D₂.d a := by sorry

end AlgebraicGeometry.GrpObj
