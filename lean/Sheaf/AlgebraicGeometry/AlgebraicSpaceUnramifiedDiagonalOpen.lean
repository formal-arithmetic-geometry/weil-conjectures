/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # The open diagonal of an unramified algebraic-space morphism

Source: Stacks Project, Morphisms of Spaces, Tag 05W1(1), and Spaces, Tag 02YU
(blueprint: lem-sfb-space-unramified-diagonal-open).

Unramifiedness is tested on all compatible representable étale scheme charts.
The diagonal is representable by open immersions and identifies its source with an
open subspace of the sheaf fibre product, without separation or finiteness assumptions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative diagonal of an unramified map of algebraic spaces is a representable
open immersion and identifies its source with an open subspace of its relative square.
Source: Stacks Project, Morphisms of Spaces, Tag 05W1(1), and Spaces, Tag 02YU
(blueprint: lem-sfb-space-unramified-diagonal-open).

Proof:
1. For any scheme test `T → X ×_Y X`, the diagonal pullback `W → T` is the equality
   locus of the two maps `T → X`. The representable absolute diagonal of `X` represents
   it by a scheme, and equality of sections on all tests makes `W → T` a monomorphism
   [def-trf-algebraic-space].
2. Choose compatible surjective étale scheme charts `U → X`, `V → Y`
   [lem-sfb-unramified-etale-compatible-charts]. Their map `h : U → V` is unramified,
   so its diagonal is an open immersion [def-weil-unramified-morphism], hence étale
   [lem-weil-pbc-etale-composition-cancellation].
3. Put `Q = U ×_Y U`, `R = V ×_Y V`. The map `Q → X ×_Y X` is a composite of base
   changes of `U → X`. The comparison `V → R` is étale. As `U ×_V U = Q ×_R V`,
   its map to `X ×_Y X` is étale [lem-trf-space-fibre-products-etale-covers,
   lem-trf-space-representable-etale-scheme-tests]. No surjectivity is needed here.
4. Pull back this diagram along `T`. Its further pullback along the scheme diagonal
   of `h` is `F = W ×_X U`, étale over `T`, and `F → W` is surjective étale.
   Thus `W → T` is étale [lem-trf-etale-descent-through-source-cover].
5. Étaleness gives flatness and local finite presentation [def-weil-etale-morphism].
   Together with the monomorphism from step 1, this makes `W → T` an open immersion
   [lem-pe-flat-lfp-monomorphism-open]. This proves the scheme-test conclusion.
6. The sheaf relative square is an algebraic space
   [lem-trf-space-fibre-products-etale-covers]. Let `J` be the image subfunctor of the
   diagonal. Sending `x` to `(x,x)` identifies `X` with `J`, with inverse either
   projection, on every scheme test. Its scheme pullbacks are precisely the opens
   `W` from step 5, so it is an `OpenSubspace` [def-a1-space-open-subspace]. -/
theorem diagonal_isRepresentableOpenImmersion_of_unramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : X ⟶ Y)
    (hg : MapIsLocally (@IsUnramified) g) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
      (pullback.diagonal g.hom).hom ∧
    ∃ (hP : IsAlgebraicSpace (Limits.pullback g.hom g.hom))
      (J : OpenSubspace ⟨Limits.pullback g.hom g.hom, hP⟩)
      (e : X.obj.obj ≅ J.val.toFunctor),
      e.hom ≫ J.val.ι = (pullback.diagonal g.hom).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
