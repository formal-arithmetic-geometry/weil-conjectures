/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Detecting isomorphisms of étale algebraic spaces on a thickening

Source: Stacks Project, spaces-more-morphisms.tex, Tag 05ZH
(theorem-topological-invariance), and Tag 05ZS (lemma-thickening-equivalence)
(blueprint: lem-sfb-space-etale-thickening-detects-iso).

Thickenings are representable closed immersions inducing homeomorphisms on the existing
field-valued point spaces with their atlas quotient topologies. No finite nilpotence bound
or representability assumption on the chartwise étale map is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale algebraic space over `W` which becomes `W₀` over a thickening `W₀ → W`
is already `W`.
Source: Stacks Project, Tag 05ZH (theorem-topological-invariance), reflection of
isomorphisms along a thickening; also Tag 05ZS (lemma-thickening-equivalence)
(blueprint: lem-sfb-space-etale-thickening-detects-iso).

Proof:
1. For an arbitrary scheme test `T → W`, put `E = V ×_W T` and `T₀ = W₀ ×_W T`.
   By lem-trf-space-fibre-products-etale-covers these are algebraic spaces; by
   lem-trf-space-chartwise-etale-permanence, `E → T` is chartwise étale.
   By lem-sfb-space-thickening-base-change, `T₀ → T` is a scheme thickening.
   Associativity of fibre products identifies `E ×_T T₀ → T₀` with the base change
   of the isomorphism in the hypothesis.
2. Every representable étale scheme chart of `E` is unramified over `T`
   (def-weil-etale-morphism). Apply lem-sfb-unramified-space-open-diagonal to
   conclude that the diagonal `E → E ×_T E` is a representable open immersion.
3. Test the diagonal on a scheme `H → E ×_T E`, obtaining an open `U ⊆ H`.
   Its pullback along the scheme thickening `H₀ = H ×_T T₀ → H` is an isomorphism,
   because the diagonal over `T₀` is an isomorphism. The thickening is surjective
   by lem-sfb-space-thickening-base-change, so its factorization through `U` gives
   `U = H` by def-weil-open-immersion. Thus the diagonal is an isomorphism.
4. Surjectivity of the diagonal on sections shows that `E → T` is a sheaf
   monomorphism. Apply lem-sfb-space-etale-monomorphism-open to conclude that
   `E → T` is a representable open immersion.
5. Testing on the identity of `T` identifies `E` with an open subscheme `O ⊆ T`.
   The isomorphism over `T₀` factors the surjective map `T₀ → T` through `O`;
   hence `O = T` by def-weil-open-immersion, so `E → T` is an isomorphism.
6. For any scheme `H` and section of `W(H)`, apply step 5 with this scheme test.
   There is a unique lift to `V(H)`. Uniqueness makes the inverse functions natural,
   and these form an inverse morphism by def-trf-algebraic-space.
The argument includes empty schemes, identity thickenings, nonseparated spaces,
and nil ideals without a uniform exponent. -/
theorem isIso_of_chartwiseEtale_of_thickening {B : Scheme.{u}}
    (V W W₀ : AlgebraicSpace B) (f : V ⟶ W) (i : W₀ ⟶ W)
    (hf : IsChartwiseEtale f)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom))
    (h₀ : IsIso (enlargedFibreProductFst i f)) : IsIso f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
