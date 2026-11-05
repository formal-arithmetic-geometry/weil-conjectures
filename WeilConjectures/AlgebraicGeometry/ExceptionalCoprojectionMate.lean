/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-! Canonical exceptional tensor extraction and its projection/counit coherence. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
/--
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md
Step 4(iii): composition compatibility and twists passing through the exceptional inverse image;
the co-projection Hom comparison of sk-lem-coprojection.

Proof:

Write F=Rf_!, G=Rf^!, and P=Lf*. The projection map is pi(A,B):F(A) tensor B -> F(A tensor
P(B)). Its inverse followed by epsilon(K) tensor id(L) is a morphism F(G(K) tensor P(L))->K
tensor L. The adjunction transpose of this morphism is the canonical tensor mate tau(K,L).

Expand the definition of the co-projection: it is the uniqueness comparison between the
composite adjunctions obtained by tensoring with the inverse object M before F, and by tensoring
with P(M) after G. Their left adjoints are identified by pi(-,M). The two tensor-equivalence
adjunctions use the displayed inverse evaluations e and e′, with the triangle identities built
into the equivalences.

Apply the counit characterization of the inverse right-adjoint comparison. Expand the composite
counits and the monoidal pullback of the evaluations. Projection naturality for e′, projection
associativity for L and M, and projection right unitality identify the two evaluation
composites. Cancel the invertible projection and evaluation maps. The resulting equality is F(u)
followed by epsilon(K tensor L) = pi(G(K),L) inverse followed by epsilon(K) tensor id(L), where
u is the inverse co-projection component.

The ordinary adjunction Hom equivalence is injective. The last equality is precisely the
defining transpose equation for tau(K,L), so u=tau(K,L). The argument used the triangle
identities for the equivalences rather than any compatibility assumed between the arbitrary e
and e′; hence it applies to all the inverse data in the statement.
(blueprint: lem-pur-exceptional-coprojection-mate)
-/
theorem exceptionalCoprojectionMate
    (K L M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).obj L ≅ constantComplex Λ Y)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj L).obj M ≅ constantComplex Λ Y) :
    (derivedTensorRightCompRightDerivedUpperShriekIso Λ f L M e e').inv.app K =
      lowerShriekRightAdjointTensorMap (rightDerivedUpperShriekAdjunction Λ f) K L := by
  sorry
end AlgebraicGeometry.Etale
