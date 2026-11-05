/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace

/-!
# Möbius decompositions of the infinite level of a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `K` a complex
of `Λ_X`-module objects such that, at every term, `g_{∞*} g_∞^* Kⁿ` is the colimit of the finite
levels. A *Möbius decomposition* of `g_{∞*} g_∞^* K`
(`AlgebraicGeometry.ProEtale.GaloisTower.MoebiusDecomposition`) is a family of endomorphisms
`e_i` of complexes, indexed by a type `ι`, such that

* on the image of every finite level `j`, only the `e_i` with `i` in a finite set `F j` are
  nonzero, and their sum is the identity (so that `∑ᵢ e_i = 𝟙` is a locally finite sum);
* a distinguished `e_{i₀}` is the idempotent `τ ≫ u` of the normalized trace `τ` and the unit `u`
  (the projector onto the invariant part);
* every other `e_i` is killed by the sum of the actions of finitely many automorphisms `σ i a` of
  `Y_∞` over `X`, whose number is invertible: `e_i` has image in the part on which the average of
  these actions vanishes.

For the tower of a Galois extension `Ω/L` the `e_i` are the Möbius combinations
`e_k = ∑_{m ≤ k} μ(m, k) π_m` of the projectors `π_m` onto the invariants of `Gal(Ω/m)`, indexed
by the finite Galois subextensions `k`. A Möbius decomposition makes Galois invariant maps out of
`g_{∞*} g_∞^* K` in the derived category factor through the invariant part: there are no phantom
maps.
-/

@[expose] public section

universe u

-- several declarations do not need all the instances of the section variables
set_option linter.unusedSectionVars false

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))
  (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
  (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n)))

attribute [instance] MoebiusDecomposition.fintype

end AlgebraicGeometry.ProEtale.GaloisTower
