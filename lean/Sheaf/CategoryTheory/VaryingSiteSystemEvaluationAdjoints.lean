/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.CategoryTheory.VaryingSiteSystem

/-!
# Evaluation adjoints for specified inverse-image coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, and spaces-simplicial.tex,
Tags 09WG and 09WH. The free and cofree constructions use the coherence of the
inverse images directly, without requiring coherence lifted from site functors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Evaluation has a monomorphism-preserving left adjoint and a right adjoint.
This uses the specified inverse-image coherence, which need not have been supplied
as a site-level pseudofunctor.

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, arrow-indexed product;
spaces-simplicial.tex, Tags 09WG (5)-(7) and 09WH, free evaluation argument
(blueprint: lem-per-varying-site-system-evaluation-adjoints).

Proof: At vertex j define the free system on A at i to be the coproduct of
(D.pull a).obj A over arrows a:j→i. The transition for c:k→j maps the pulled-back
a-summand to the (c ≫ a)-summand using e.comp c a. Inverse image preserves
coproducts because it is the sheaf inverse-image left adjoint. The unit and
associativity axioms of e prove the identity and cocycle laws by testing on every
summand. A morphism A→F_i extends on the a-summand by its inverse image followed
by F.transition a. Restriction to the identity summand, transported by e.unit,
is its inverse; compatibility with a determines every summand, proving the
adjunction and naturality. This left adjoint preserves monomorphisms: each
inverse image does so by D.exact_limits; arbitrary coproducts of monomorphisms
of abelian sheaves are monic, since they are filtered colimits of finite subsums
and filtered colimits are exact. A componentwise monomorphism of systems is
monic by cancellation in compatible families.

For the cofree system set its j-component equal to the product, over a:i→j,
of the direct image of A along a. Give the direct images the unit and composition
comparisons obtained as mates of e.unit and e.comp under the actual sheaf
adjunctions. The mate identities obey coherence. For c:k→j, its transition to
the b:i→k factor is inverse image of the (b ≫ c)-projection, transported by
the direct-image compositor and followed by the counit. After transposition,
product projections and coherence prove the identity and cocycle equations.
Given F_i→A, the a-projection of the corresponding system map is the adjunct
of F.transition a followed by this map. Its inverse is projection to the
identity factor, with the unit comparison. Compatibility recovers each other
projection and product uniqueness gives the inverse identity and naturality.
Empty Hom sets give zero sheaves; empty I gives no evaluation to construct. -/
theorem varyingSiteSystem_evaluation_adjoints
    {I : Type u} [SmallCategory I] (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) (i : I) :
    (∃ L : D.Ab i ⥤ VaryingSiteSystem D e,
      Nonempty (L ⊣ VaryingSiteSystem.evaluation D e i) ∧ L.PreservesMonomorphisms) ∧
    (∃ R : D.Ab i ⥤ VaryingSiteSystem D e,
      Nonempty (VaryingSiteSystem.evaluation D e i ⊣ R)) := by
  sorry

end CategoryTheory
