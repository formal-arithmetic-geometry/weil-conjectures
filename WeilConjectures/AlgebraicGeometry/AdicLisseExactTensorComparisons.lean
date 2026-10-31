/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicLisseCalculusData

/-! # Exact lisse tensor and its geometric fibres

Source: Bhatt--Scholze 6.8.4 and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar] (X : Scheme.{u})
  [IsNoetherian X] [X.IsSeparated]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]


/-- Tensor with a lisse realization commutes with standard cohomology and
its degree-zero geometric fibre is the ordinary coefficient tensor.
Source: Bhatt--Scholze 6.8.4(1),(4), Remark 6.8.15; the two tensor calculations
in the blueprint lisse tensor permanence proof.
(blueprint: lem-per-adic-lisse-exact-tensor-comparisons).

Proof: pass to a common finite coefficient field. On each of the finitely many
open connected components, the representation correspondence and the profinite
stable-lattice theorem replace the rational lisse sheaf by a finite-free integral
lattice. Its completed realization N is locally finite free over the completed
coefficient ring. Tensor with N is exact, since on a trivializing pro-etale slice
it is a finite direct sum of the identity; exactness descends by the sheaf axiom.
The cycles and boundaries sequences therefore give a natural cohomology comparison
for termwise tensor with N. This also proves that N in degree zero is K-flat.

Tensor with this bounded finite-free local model preserves derived sequential
limits. Apply Koszul reconstruction to the complete integral representative of K.
At each quotient the balanced map sends y tensor (x tensor a) to
(x tensor a) tensor the reduction of y. These maps and their inverses commute with
quotient transitions, so their limit identifies ordinary tensor with the specified
completed tensor. Stratified finite presentations put the result in the integral
constructible category, with the original cohomological bounds.

For the fibre comparison take completed geometric pullback and point sections,
then cohomology in degree zero. Exactness of pullback and sections at the point
and the same finite-free tensor calculation give the ordinary tensor of the two
fibres. Equivalently, reduce on a lisse stratum and take finite etale stalks:
the levelwise tensor-germ maps commute with all quotient maps; their inverse
limits are tensor with a finite-free module. Invert the uniformizer and extend
to Qbar. This does not commute an ordinary stalk with an infinite limit.

Both calculations are canonical on tensor generators, natural in K and the
lisse factor, and commute with coefficient extension. The integral scalar-operation
unit and tower equations descend the two isomorphisms to common-stage functors.
The prescribed normalizations of M identify their endpoints with those below.
The zero-rank case is tensor with zero and is included throughout. -/
theorem adic_lisse_exact_tensor_comparisons (M : AdicLisseCalculusModels l Qbar X) :
    Nonempty (∀ a : ℤ,
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod M.realization) ⋙
        adicCalculusTensor l Qbar X M.comparison ⋙ M.cohomology a ≅
      ((M.cohomology a).prod M.realization) ⋙ adicCalculusTensor l Qbar X M.comparison) ∧
    Nonempty (∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X),
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod M.realization) ⋙
        adicCalculusTensor l Qbar X M.comparison ⋙ M.fiber k x ≅
      ((M.fiber k x).prod (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
        MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar)) := by sorry

end AlgebraicGeometry.Scheme
