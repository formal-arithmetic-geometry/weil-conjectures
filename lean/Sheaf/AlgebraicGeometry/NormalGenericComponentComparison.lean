/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism

/-!
# Basis clopens and connected components of an affine generic fibre

Source: Stacks Project, `topology.tex`, Tag 0906 (lemma-spectral-pi0), with the
agent basis-gluing and affine generic-fibre argument in the DAG node
(blueprint: lem-sfb-normal-generic-component-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Clopen inverse-image bijections on an affine open basis glue to a global bijection,
and the canonical generic-fibre projection induces a homeomorphism on component quotients.
Here `X.fromSpecStalk (genericPoint X)` is the canonical generic inclusion from
`Spec X.functionField`. The local domain is the inverse-image open with its subspace
topology, canonically the underlying space of the corresponding open generic fibre.

Source: Stacks Project, `topology.tex`, Tag 0906 (lemma-spectral-pi0), and the agent
local-to-global expansion in the DAG node
(blueprint: lem-sfb-normal-generic-component-comparison).

Proof for stage 3:
1. The spectrum of the function field is a singleton mapping to the generic point.
Its inverse image of any affine open of X is empty or the whole spectrum, hence affine.
Thus the generic inclusion is affine, by pqf-def-affine-morphism.
2. Base change makes the projection affine; its target U is affine, so its source is
also affine (lem-weil-pbc-affine-morphism-permanence). Both are qcqs
(lem-weil-pbc-affine-scheme-qcqs), hence spectral (lem-weil-pbc-qcqs-scheme-spectral).
3. Given a clopen D of the generic fibre, on every basis open W take its unique clopen
extension C_W. On W intersect V refine by basis opens B. The two restrictions to B
have the same generic inverse image, so local injectivity makes them equal. This
proves overlap agreement without assuming the intersections affine.
4. The union C of all C_W restricts to C_W on W. Both C and its complement are open,
the complement being the union of W minus C_W. Its inverse image is D because the
basis and its inverse images cover. This gives global surjectivity on clopens.
5. Two clopens with equal inverse images agree on every W by local injectivity, so
they agree globally. Inverse image preserves clopens by continuity.
6. Apply lem-sfb-spectral-clopen-component-homeomorphism to this projection and the
global bijection. It gives the canonical component map, its homeomorphism property,
and its normalization by the quotient maps. All unions and covers permit empty U
and the empty basis. -/
theorem normal_generic_component_comparison
    {X U : Scheme.{u}} [IsIntegral X] [IsAffine U] (u : U ⟶ X)
    (B : Set U.Opens) (hBaffine : ∀ W ∈ B, IsAffineOpen W)
    (hBbasis : ∀ (O : U.Opens) (x : U), x ∈ O → ∃ W ∈ B, x ∈ W ∧ W ≤ O)
    (hBclopen : ∀ W ∈ B, Function.Bijective
      (fun C : Clopens W ↦
        (⟨(W : Set U).restrictPreimage
            (pullback.fst u (X.fromSpecStalk (genericPoint X))) ⁻¹' (C : Set W),
          C.isClopen.preimage
            (pullback.fst u (X.fromSpecStalk (genericPoint X))).continuous.restrictPreimage⟩ :
          Clopens (pullback.fst u (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ W)))) :
    IsAffineHom (X.fromSpecStalk (genericPoint X)) ∧
    IsAffineHom (pullback.fst u (X.fromSpecStalk (genericPoint X))) ∧
    IsAffine (pullback u (X.fromSpecStalk (genericPoint X))) ∧
    SpectralSpace U ∧
    SpectralSpace (pullback u (X.fromSpecStalk (genericPoint X)) : Scheme.{u}) ∧
    Function.Bijective (fun C : Clopens U ↦
      (⟨(pullback.fst u (X.fromSpecStalk (genericPoint X))) ⁻¹' (C : Set U),
        C.isClopen.preimage (pullback.fst u (X.fromSpecStalk (genericPoint X))).continuous⟩ :
        Clopens (pullback u (X.fromSpecStalk (genericPoint X)) : Scheme.{u}))) ∧
    IsHomeomorph
      (pullback.fst u (X.fromSpecStalk (genericPoint X))).continuous.connectedComponentsMap ∧
    (pullback.fst u (X.fromSpecStalk (genericPoint X))).continuous.connectedComponentsMap ∘
        (ConnectedComponents.mk : (pullback u (X.fromSpecStalk (genericPoint X)) : Scheme.{u}) →
          ConnectedComponents (pullback u (X.fromSpecStalk (genericPoint X)) : Scheme.{u})) =
      (ConnectedComponents.mk : U → ConnectedComponents U) ∘
        (pullback.fst u (X.fromSpecStalk (genericPoint X))) := by
  sorry

end AlgebraicGeometry
