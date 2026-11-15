/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# An open section of a separated morphism is clopen

Source: blueprint, chap-Smooth-purity, sk-def-sf-operations,
proposition-construction-independence-rf-shriek--7; Stacks Project, Tag 01KT,
lemma-section-immersion (blueprint: proposition-construction-independence-rf-shriek--7).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An open section of a separated morphism has clopen image, and the source together
with the complementary open subscheme is a coproduct decomposition of the target.

Source: blueprint, chap-Smooth-purity, sk-def-sf-operations,
proposition-construction-independence-rf-shriek--7; Stacks Project, Tag 01KT,
lemma-section-immersion.

Proof: The identity of `S` is a closed immersion. Since `s ≫ p` is that identity and
`p` is separated, `IsClosedImmersion.of_comp`
(corollary-extension-proper-target--1) makes `s` a closed immersion.
Its image is therefore closed, and is open by the open immersion hypothesis
(def-weil-closed-immersion, def-weil-open-immersion, def-weil-proper-morphism).
The complement is open. These two open subschemes are disjoint and cover `V`.
The sheaf axiom on this disjoint cover identifies sections with the product of
sections on the two pieces, compatibly with restrictions. Thus the two inclusions
exhibit `V` as their scheme coproduct.
(blueprint: proposition-construction-independence-rf-shriek--7) -/
theorem open_section_clopen {V S : Scheme.{u}} (p : V ⟶ S) (s : S ⟶ V)
    [IsSeparated p] [IsOpenImmersion s] (hs : s ≫ p = 𝟙 S) :
    IsClopen (Set.range s) ∧
      ∃ W : V.Opens, (W : Set V) = (Set.range s)ᶜ ∧
        Nonempty (IsColimit (BinaryCofan.mk s W.ι)) := by
  have : IsClosedImmersion (s ≫ p) := hs ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s p
  have hcl : IsClopen (Set.range s) :=
    ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩
  let W : V.Opens := ⟨(Set.range s)ᶜ, hcl.isClosed.isOpen_compl⟩
  refine ⟨hcl, W, rfl, nonempty_isColimit_binaryCofanMk_of_isCompl s W.ι ?_⟩
  rw [Scheme.Opens.opensRange_ι]
  simp [isCompl_iff, disjoint_iff, codisjoint_iff, ← SetLike.coe_set_eq,
    Scheme.Hom.coe_opensRange, W]

end AlgebraicGeometry
