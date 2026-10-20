/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentTopos
import Sheaf.CategoryTheory.Sites.CoherentToposRepair

/-!
# Reflection of coherence by a coherent conservative inverse image

Source: Orgogozo, author draft, §8.1, printed p. 17
(blueprint: lem-trf-coherent-conservative-reflection).
The declaration below records the node statement verbatim; its proof remains postponed at stage 2.
-/

@[expose] public section

set_option autoImplicit false

universe w u u' v v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A coherent conservative geometric morphism reflects coherent objects: for
`u : E' → E` between coherent topoi, if `u⁻¹ A` is coherent then `A` is coherent.

Source: Orgogozo, author draft, §8.1, printed p. 17
(blueprint: lem-trf-coherent-conservative-reflection).
The declaration below records the node statement verbatim; its proof remains postponed at stage 2.
The notions are those of `def-trf-coherent-topos`; write `F = u⁻¹`. The proof
(agent-written; the source states the assertion without proof) postponed here:

Step 1. In a small-site presentation, the sheaf coproduct of a small family
`(T_i)` is the sheafification of the presheaf coproduct `P(U) = ∐ T_i(U)`;
since the unit `P → P^#` becomes an isomorphism after sheafification, every
section of the coproduct locally comes from one summand (Stacks 00WH, 00WI,
00WK). This includes the empty family.

Step 2. Hence `(T_i → T)` has epimorphic coproduct map iff every section of
`T` locally lifts to some `T_i` (Stacks 00WN). This criterion is stable under
base change, since fibre products are computed sectionwise (Stacks 00W2), and
under composition of covering families, by the transitivity of coverings.

Step 3. `F` is a left adjoint preserving finite limits, so it preserves small
coproducts and coequalizers (Stacks 0038 (1)). An epimorphism is the
coequalizer of its kernel pair (Stacks 086K), so `F` preserves epimorphisms,
and with the coproduct comparison it preserves covering families.

Step 4. `F` is faithful: if `F a = F b`, then `F` sends an equalizer `e` of
`a, b` to an isomorphism, conservativity makes `e` invertible, and `a = b`.
So if `F p` is epi and `p ≫ a = p ≫ b`, then `F a = F b` and `a = b`; `F` reflects
epimorphisms and, by Step 3, covering families.

Step 5. If `F T` is quasi-compact then `T` is: a covering `(T_i → T)` maps to
a covering of `F T` (Step 3), a finite subfamily covers `F T`, and by Step 4
the same finite subfamily covers `T`.

Step 6. In either topos, a finite covering family `(Q_j → Q)` by
quasi-compact objects has quasi-compact target: pull a covering of `Q` back to
each `Q_j` (Step 2), take finite index sets `I_j`, and their union covers `Q`
(the empty `J` uses the empty cover).

Step 7. `F` preserves quasi-compact objects: a quasi-compact `B` has a finite
covering by coherent generators `G_i`; its image covers `F B` (Step 3), each
`F G_i` is coherent by coherence of `u`, so `F B` is quasi-compact by Step 6.

Step 8. If `F A` is coherent, Step 5 makes `A` quasi-compact. For
quasi-compact `B → A`, `C → A`, Step 7 makes `F B`, `F C` quasi-compact, so
`F B ×_{F A} F C ≅ F (B ×_A C)` is quasi-compact by quasi-separatedness of
`F A` and finite-limit preservation; Step 5 makes `B ×_A C` quasi-compact.
Thus `A` is quasi-separated, hence coherent.
-/
theorem isCoherentObject_of_inverse_coherent
    {E : Type u} {E' : Type u'} [Category.{v} E] [Category.{v'} E']
    [HasCoproducts.{w} E] [HasCoproducts.{w} E']
    [HasFiniteLimits E] [HasFiniteLimits E']
    (hE : IsCoherentTopos E) (hE' : IsCoherentTopos E')
    (u : GeometricMorphism E' E)
    (hu : IsCoherentGeometricMorphism hE' hE u)
    (hcon : IsConservativeGeometricMorphism hE' hE u)
    (A : E) :
    IsCoherentObject (u.inverse.obj A) → IsCoherentObject A := by
  sorry

end CategoryTheory
