/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Natural associativity and the coefficient unit for common-stage tensor

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-line-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Fixed-right tensor associativity and its degree-zero regular coefficient unit.

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-line-coherence).

Proof: the integral tensor associator is the unique lift of the associator in
the coherent finite quotient system. Apply the faithful reduction functor to
its naturality square; tensor-reduction naturality reduces it to ordinary
associator naturality in that monoidal category. The same argument proves
naturality of the right unitor. The regular integral sheaf in degree zero has
the coefficient-unit quotient system, with its actual quotient transitions;
derived completeness identifies it with the reconstructed integral unit.
Localize these integral naturality equations. Every rational morphism is a
finite sum of pure coefficient tensors; bilinearity and integral naturality
give the rational associator and unitor squares on those generators and
hence on every morphism. In the pair category, represent all objects and maps
of each square over one finite common coefficient field. The canonical scalar
tensor comparisons conjugate the common-stage associator and unitor to those
rational maps. Their tower and unit equations cancel the conjugations, giving
exactly the rational naturality squares already proved. Eventual equality
therefore gives naturality in the common-stage category. The inverse maps are
the corresponding inverse associators and unitors, so their pointwise inverse
identities descend too. Assemble these components with NatIso.ofComponents.
The least-stage regular integral sheaf is sfQbarTwistingCoefficient at zero,
so the unit is the specified object rather than an arbitrary chosen unit. -/
theorem commonStageTensorLineCoherence
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    let C := generalAlgebraicallyClosedConstructibleCategory l Ω X
    let T := commonStageDerivedTensor l Ω X
    let right (L : C) := (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T
    (∀ (L M : C), Nonempty (right L ⋙ right M ≅ right (T.obj (L, M)))) ∧
      Nonempty (right (sfQbarTwistingCoefficient l X Ω 0) ≅ 𝟭 C) := by
  sorry

end WeilConjectures
