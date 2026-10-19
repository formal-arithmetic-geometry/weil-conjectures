/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Weakly étale universal homeomorphisms

Source: Stacks Project, More on Morphisms, Tag 0F6V
(blueprint: lem-trf-weakly-etale-homeomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- A weakly étale universal homeomorphism of schemes is an isomorphism.

Source: Stacks Project, More on Morphisms, Tag 0F6V, lemma
`lemma-weakly-etale-universal-homeomorphism`.
Proof (the reviewed DAG's seven steps):

1. Set `P = V ×_W V` and let `δ : V ⟶ P` be the diagonal. Weak etaleness gives
flatness of `f` and `δ` (`def-weil-weakly-etale-morphism`). Every base change of `f`
is a homeomorphism, hence injective, and the identity base change is surjective
(`def-weil-universal-homeomorphism`, `def-weil-radicial-morphism`,
`def-weil-surjective-morphism`). Thus `f` is universally injective and surjective.

2. Its underlying homeomorphism has closed image `W`, so `f` is affine
(`lem-trf-closed-embedding-affine`), hence separated and quasi-compact
(`lem-weil-pbc-affine-morphism-permanence`, clause 3). Consequently `δ` is a closed
immersion (`def-weil-proper-morphism`) and is surjective by universal injectivity
(`def-weil-radicial-morphism`, equivalence 2 with 4).

3. The closed immersion `δ` is affine and hence quasi-compact
(`lem-weil-pbc-closed-immersion-integral-separated-uc`, clause b;
`lem-weil-pbc-affine-morphism-permanence`, clause 3). It is therefore flat,
surjective and quasi-compact. It is monic since composing `δ a = δ b` with the
first projection gives `a = b` (`def-pc-fibre-product`).

4. For any monomorphism `g : A ⟶ B`, the projections `q₁,q₂ : A ×_B A ⟶ A` are
equal since `g q₁ = g q₂`. The diagonal `d` has `q₁ d = id` and `d q₁ = id`, the
second equality being checked after both projections. Hence `q₂` is an
isomorphism. This is the base change of `g` along itself (`def-pc-fibre-product`).

5. Apply step 4 to `δ`. Descend its invertible self-base-change along the flat,
surjective, quasi-compact cover `δ` using `lem-weil-pbc-fpqc-descend-isomorphism`.
Thus `δ` is an isomorphism.

6. If `f a = f b`, the pairing `c = (a,b)` to `P` equals `δ (δ⁻¹ c)`. Projecting to
both factors gives `a = δ⁻¹ c = b`. Thus `f` is monic (`def-pc-fibre-product`).

7. Step 4 now makes the self-base-change of `f` invertible. Steps 1 and 2 give
flatness, surjectivity and quasi-compactness. Apply
`lem-weil-pbc-fpqc-descend-isomorphism` with cover `f` to conclude that `f` is an
isomorphism.
(blueprint: lem-trf-weakly-etale-homeomorphism) -/
theorem isIso_of_weaklyEtale_of_universalHomeomorphism
    {V W : Scheme.{u}} (f : V ⟶ W) [WeaklyEtale f]
    (hf : (topologically IsHomeomorph).universally f) :
    IsIso f := by
  have hhomeo : IsHomeomorph f := hf _ _ _ .of_id_snd
  have : Surjective f := ⟨hhomeo.surjective⟩
  have : UniversallyInjective f :=
    ⟨fun _ _ _ _ _ h ↦ (hf _ _ _ h).injective⟩
  have : IsAffineHom f :=
    isAffineHom_of_isInducing f hhomeo.isInducing hhomeo.isClosedEmbedding.isClosed_range
  have : Surjective (pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp ‹_›
  -- The separated diagonal is a flat, surjective, quasi-compact monomorphism.
  have : IsIso (pullback.diagonal f) := by
    apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := pullback.diagonal f) (g := pullback.diagonal f)
    · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    · exact inferInstanceAs <| IsIso (pullback.fst (pullback.diagonal f) (pullback.diagonal f))
  -- An invertible diagonal makes f monic, so the same descent argument applies.
  have : Mono f := (pullback.isIso_diagonal_iff f).mp ‹_›
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact inferInstanceAs <| IsIso (pullback.fst f f)

end AlgebraicGeometry
