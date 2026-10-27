/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.RelativeAssassin
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.LocallyQuasicoherentAffinePullbackSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.RingTheory.WeaklyAssociatedEtale
import Sheaf.RingTheory.AnnihilatorEqIffMinimalPrimeOfFG
import Sheaf.AlgebraicGeometry.AffineAssociatedPointsPrimes

/-! # Associated points under etale tensor pullback

Source: Stacks Project, More on Flatness, Tag 05FP
(`lemma-etale-weak-assassin-up-down`), and Divisors, Tag 05AR
(`lemma-ass-weakly-ass`), last sentence
(blueprint: lem-sfb-scheme-etale-assassin-invariance).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Etale tensor pullback preserves and reflects associated points of an arbitrary
quasi-coherent module on locally Noetherian schemes. Associated points use the
maximal-ideal element-annihilator condition on the stalk module. No finite generation
of the module, surjectivity, or quasi-compactness of the morphism is assumed.

Source: Stacks Project, More on Flatness, Tag 05FP, combined with Divisors, Tag 05AR
(blueprint: lem-sfb-scheme-etale-assassin-invariance).

Proof:
1. Fix v and choose affine neighbourhoods U₀ of h(v) and V₀ of v contained in
   h⁻¹(U₀). The restricted morphism is etale by lem-a1-etale-open-restriction.
   Their section rings A and B are Noetherian by pqf-lem-affine-open-locnoeth.
   By def-weil-affine-spectrum, the prime p of h(v) is the contraction of the
   prime q of v along the induced ring map A → B.
2. Restrict G to U₀. Restriction preserves quasi-coherence by
   lem-weil-pbc-module-restriction-open-immersion-colimits and agrees with tensor
   pullback along the inclusion by uniqueness of left adjoints. The composition
   comparison of lem-pc-module-pullback-identity-composition identifies the
   restriction of h*G to V₀ with the restricted morphism's pullback of G|U₀.
   The restricted morphism is affine by lem-weil-pbc-morphism-affine-schemes-affine.
   Apply new-p4-locally-quasicoherent-affine-pullback-sections to identify its
   sections with B ⊗[A] M, where M is the section module on U₀. Pullback preserves
   quasi-coherence by lem-weil-pbc-module-pullback-quasi-coherent (transported
   from the abstract pullback along the tensor-pullback adjunction comparison).
3. By lem-trf-etale-weakass-invariance, q is weakly associated to M ⊗[A] B
   exactly when p is weakly associated to M. The tensor flip identifies this
   module with B ⊗[A] M, and a linear isomorphism preserves element annihilators.
4. Noetherianity makes p and q finitely generated. Thus
   lem-sc-ass-weakass-fg-prime changes weak association to element-annihilator
   association on both sides. Apply lem-sfb-affine-associated-points-primes on
   U₀ and V₀ to identify these conditions with the two associated-point
   conditions in the conclusion. The module inputs allow arbitrary modules,
   and the local neighbourhood choices require no surjectivity or quasi-compactness. -/
theorem associatedPoints_tensorPullback_iff_of_etale
    {V U : Scheme.{u}} (h : V ⟶ U) [Etale h]
    [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (G : U.Modules) (hG : G.IsQuasicoherent) (v : V) :
    v ∈ associatedPoints ((tensorPullback h).obj G) ↔ h v ∈ associatedPoints G := by
  sorry

end AlgebraicGeometry.Scheme.Modules
