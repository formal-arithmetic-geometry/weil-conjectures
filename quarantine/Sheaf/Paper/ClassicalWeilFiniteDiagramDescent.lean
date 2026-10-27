/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.ClassicalFiniteWeilDiagramData

/-! # Simultaneous finite coefficient descent for classical Weil diagrams

Source: Weil II (1.1.1)b--d; BS 6.8.4(1),(4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u v w z
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor (IsoAlgebra)
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

variable [Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- Descend only the diagram and its equations to already supplied normalized stages.
Source: Weil II (1.1.1)b--d; Stanford Weil II seminar L19, Proposition 1.1.9;
Bhatt--Scholze 6.8.4(1),(4); finite Weil-diagram proof steps 2--3 and 7--8.
(blueprint: lem-zl-finite-weil-diagram-descent).

Proof: take the compositum of the finitely many vertex fields. Directed Hom colimits
represent the arrows, Weil isomorphisms and their inverses over a further finite field.
Only finitely many words and pullbacks occur. Equality of their geometric fibre maps
is equality of the classical sheaf maps; eventual equality in the directed Hom colimit
then puts the prescribed equations, inverse identities and equivariance squares over
one further finite field. Frobenius pullback retains that field and its actual source.
On each nonempty clopen connected component choose a geometric point. The classical
lisse dictionary and the profinite stable lattice theorem supply a finite free lattice
in each underlying geometric monodromy representation. Reduce these lattices and use
the finite lisse dictionary to obtain normalized free systems. Assemble them over the
finitely many clopen components. Transport the rational arrows and the Weil maps to
these systems, retaining the actual pullback operation of the supplied stage. Its
classical comparison identifies their sources; faithfulness of the classical model
functor proves the inverse and equivariance identities. The resulting IsoAlgebra
objects N, arrows b and classical identifications beta give the stated conclusion.
Faithfulness also reflects the finite additive equations to the raw rational Hom groups.
No chosen arrow is required to preserve a lattice. For an empty diagram take the base
field; rank zero and an empty base use zero systems. -/
theorem zl_finite_weil_diagram_descent
    (R : ZlClassicalRealization D l hl Ω Y₀)
    (P₀ : ∀ E : Padic.FiniteCoefficientFields l Ω, ZlDiagramStage D l hl Ω Y₀ R E)
    (I : Type v) [Finite I] (A : Type w) [Finite A] (s t : A → I)
    (J : Type z) [Finite J] (x y : J → I × ℕ)
    (e f : ∀ j : J, ZlWeilExpression s t (x j) (y j))
    (M : I → ZlClassicalWeil D l Ω Y₀) (a : ∀ j : A, M (s j) ⟶ M (t j))
    (heq : ∀ j : J, zlClassicalEquation D l Ω Y₀ M a (e j) (f j)) :
    ∃ E : Padic.FiniteCoefficientFields l Ω,
    let P := P₀ E
    ∃ N : I → P.Weil D l hl Ω Y₀,
    ∃ b : ∀ j : A, N (s j) ⟶ N (t j),
    ∃ β : ∀ i : I, (P.classicalWeil D l hl Ω Y₀).obj (N i) ≅ M i,
      (∀ j : A, (P.classicalWeil D l hl Ω Y₀).map (b j) ≫ (β (t j)).hom =
        (β (s j)).hom ≫ a j) ∧
      (∀ j : J,
        zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) (e j) =
          zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) (f j)) := by sorry

end WeilConjectures
