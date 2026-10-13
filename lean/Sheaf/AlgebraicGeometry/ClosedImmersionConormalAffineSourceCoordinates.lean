/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Cotangent

/-! # Normalized affine coordinates for conormal sections

Source: Stacks Project, Morphisms, Lemma 0473 and Schemes, Lemma 01JU (1).
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine source coordinate for the iterated tensor pullback, normalized on
scalar multiples of the successive adjunction units of ideal sections.
No conormal morphism or target coordinate occurs in this statement.

Source: Stacks Project, Morphisms, Lemma 0473, affine reduction; Schemes,
Lemma 01JU (1); Morphisms, Lemma 01R3 (2).
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates).

Proof:
1. Write A = Gamma(X', U'), B = Gamma(X, U), J = i'.ker.ideal U'. The preimages
V' = i' inverse image U' and V = i inverse image U are affine, because both immersions
are affine. Their section maps from A and B are surjective. The canonical isomorphism
from the given limit cone to the chosen pullback, kernel invariance under isomorphism,
and ker_fst_of_isClosedImmersion give i.ker = i'.ker.comap g. The affine ideal-comap
formula identifies i.ker.ideal U with JB. The first isomorphism theorem identifies
the chart rings with A/J and B/JB; the square equality makes these identifications
compatible with f and g. No restriction of a fibre-product square is needed.
2. Affine conormal sections identify the conormal on V' with J/J^2 as an A/J-module.
The normalized equivalence sends a mod J^2 to the adjunction unit of any ideal section
representing a. Affine pullback sections for f identify the source on V with
(B/JB) tensor over A/J with J/J^2, sending a pure tensor to the restricted f-unit,
multiplied by the scalar in B/JB.
3. J annihilates J/J^2. The tensor-over-quotient equivalence, followed by tensor
cancellation and a tensor swap, identifies this source with B tensor over A with J/J^2.
Its inverse sends b tensor class(a) to the restriction of the successive units of a,
multiplied by the image of b under i.app. The pushforward composition isomorphism
identifies successive units with the composite adjunction unit. Transport along the
square equality h supplies pushforwardCongr h.symm. Naturality under restriction gives
exactly the displayed normalization. All maps are additive isomorphisms. -/
theorem closedImmersion_conormal_affine_source_coordinates
    {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    let S := (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules)
    ∃ eS : Γ(S, i ⁻¹ᵁ U.1) ≃+ Γ(X, U.1) ⊗[Γ(X', U'.1)]
        (i'.ker.ideal U').Cotangent,
      (∀ (b : Γ(X, U.1)) (a : i'.ker.ideal U') (s' : Γ(i'.ker.toModules, U'.1)),
        i'.ker.toModulesι.app U'.1 s' = (a : Γ(X', U'.1)) →
        eS.symm (b ⊗ₜ[Γ(X', U'.1)] (i'.ker.ideal U').toCotangent a) =
          i.app U.1 b • S.val.map (homOfLE (i.preimage_mono H)).op
            ((((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
                i'.ker.toModules) ≫
              (pushforward i').map
                (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
                  ((tensorPullback i').obj i'.ker.toModules))) ≫
              (pushforwardComp f i').hom.app S ≫
              (pushforwardCongr h.symm).hom.app S).app U'.1 s')) := by sorry

end AlgebraicGeometry.Scheme.Modules
