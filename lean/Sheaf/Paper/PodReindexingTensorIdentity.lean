/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Tensor normalization of the reindexing identity

Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI.
(blueprint: lem-pod-reindexing-tensor-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical site and localized tensor identity comparison.
Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI
(blueprint: lem-pod-reindexing-tensor-identity).

Proof: For a module M and an object U of the pro-etale site, use M.val.map ((siteId X).inv.app
U).op as the ordinary comparison. Its inverse is restriction along siteId.hom. Functoriality of M
and the site isomorphism identities prove the two inverse laws, while naturality of siteId proves
compatibility with restriction. The coefficient action is unchanged on finite-stage constants;
equality after every finite quotient proves the same assertion for completed coefficients. Hence
the section maps are linear and define the required natural ordinary module isomorphism, with
precisely the sections field of Identity.

On a cochain complex take these ordinary maps in every degree. Their naturality with respect to
the differentials gives a chain isomorphism; its degree field is the defining formula. The chain
isomorphisms are natural in P. Descend them through localization, since reindexing preserves
quasi-isomorphisms. Full faithfulness of whiskering with the localization determines the resulting
derived isomorphism, and its defining representative equation is exactly Identity.model with the
recorded podReindexingDerivedFactors. Thus every field is constructed by restriction or
localization.

For the tensor equation first use c.tensorChain_pure on the actual total tensor of complexes P,Q.
On a pure section x tensor y in the (p,q) summand, restriction along siteId.inv gives the tensor
of the two restricted sections. These are exactly the two routes in the proposed chain square. No
degree is permuted, so no sign occurs. Sheafification and total-summand extensionality give
equality of chain maps. Choose P,Q independently K-flat. Their reindexings are K-flat, since the
inverse exact reindexing equivalence transports the defining acyclic tensor tests. Substitute
c.tensor_model and the identity model equation into the localized chain square, and cancel the
K-flat comparison isomorphisms. This gives the desired square on their localized objects.
Independent K-flat resolutions and naturality of c.tensor and the identity comparison then give
the equation for arbitrary M,N. This argument proves only the tensor equation; the item derives
the Hom equation from evaluation.
-/
theorem tensor_identity_exists (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (S : Closed l E X s) (T : Models l E X s S)
    (c : Comparison l E (𝟙 X) s S S T T) :
    ∃ k : Identity l E X s,
      (∀ M N : podReindexingDerived l E X s,
        c.tensor.hom.app (M, N) ≫ S.tensor.map
          (Prod.mkHom (k.derived.hom.app M) (k.derived.hom.app N)) =
        k.derived.hom.app (S.tensor.obj (M, N))) := by
  sorry

end WeilConjectures.PodReindexingCoherence
