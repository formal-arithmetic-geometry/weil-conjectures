/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.FiniteTorDimension

/-! # Pseudo-coherent complexes of finite Tor dimension are perfect

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.5, Tag 08CQ
(blueprint: lem-pc-pseudo-coherent-finite-tor-perfect).
-/

@[expose] public section

universe uP wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A pseudo-coherent derived object of finite Tor dimension is perfect.
Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.5 (08CQ)
(blueprint: lem-pc-pseudo-coherent-finite-tor-perfect).

Proof:
1. Choose global Tor bounds `[a,b]`. Perfectness is local (`def-pc-perfect-complex`).
   Pseudo-coherence (`def-pur-pseudo-coherent-complex`) gives local bounded-above
   finite free representatives; refine to affine opens. Restriction of derived tensor
   (`lem-pc-affine-derived-pullback-tensor-tilde`, part 1), testing with the pushforward
   of any module on an open, preserves the same Tor bounds.
2. On an affine open `Spec R`, sections of the structure sheaf are `R`
   (`lem-weil-pbc-spec-module-tilde-sections`). The finite free terms and their matrix
   differentials therefore come from a bounded-above finite free R-module complex P.
   The tilde functor is exact and faithful by its localization description and recovery
   of modules by global sections. The tensor comparison
   (`lem-pc-affine-derived-pullback-tensor-tilde`, part 3) transfers the Tor bounds to P.
   The ring criterion (`lem-pc-ring-pseudo-coherent-finite-tor-perfect`) gives a bounded
   finite projective complex isomorphic to P in D(R).
3. Exact tilde carries the quasi-isomorphisms in this derived isomorphism to
   quasi-isomorphisms of sheaf complexes. Finite projective terms sheafify to direct
   summands of finite free sheaves. Thus the resulting complex is strictly perfect,
   and the local characterization (`def-pc-perfect-complex`) proves perfectness. -/
theorem isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension (S : Scheme.{uP})
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPseudoCoherent S K)
    (hTor : HasFiniteTorDimension S K) : IsPerfect S K := by
  sorry

end AlgebraicGeometry.Scheme
