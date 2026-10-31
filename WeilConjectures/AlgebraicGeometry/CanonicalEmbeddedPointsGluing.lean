/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.RingTheory.Support
import WeilConjectures.RingTheory.LocalizationEmbeddedPoints
import WeilConjectures.Topology.GlueSheavesOfModulesSupplement
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Gluing the canonical affine embedded-point submodules

Source: Stacks Project, Divisors, Tag 02OL, proof, using Algebra, Tag 02M7
(blueprint: lem-sc-canonical-embedded-points-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The maximal submodules with nowhere-dense support on every affine open glue to
a coherent subobject whose section ranges are exactly the prescribed submodules.

Source: Stacks Project, Divisors, Tag 02OL, proof, and Algebra, Tag 02M7
(blueprint: lem-sc-canonical-embedded-points-gluing).

Proof:
1. Coherence identifies F on an affine open V with the tilde of the finite module
M = F(V). The coordinate ring is Noetherian, so every submodule N(V) is finite.
The submodule with nowhere-dense support is unique: the sum of two such submodules
still has nowhere-dense support, since its support is their union. Thus maximality
makes either contain the other.
2. The localization theorem for embedded-point removal identifies the localized
quotient maps. Taking their kernels identifies N(V) localized at f with N(D(f)).
An intersection of two affine opens is covered by opens principal in both; the
local tilde subobjects therefore have equal section ranges on this basis, and hence
agree on the overlap as subsheaves of F.
3. Glue the local tilde modules and their inclusions using sheaf gluing. The inclusions
are monic locally and hence globally. Quasi-coherence and finite type are local, so
local Noetherianity gives a coherent subobject K. Its affine section ranges are N(V).
4. The tilde/global-sections equivalence identifies the section ranges of the inclusion
on every affine V with N(V). The zero module and empty scheme require no exception.
-/
theorem exists_coherent_subobject_of_affine_maxima
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (N : ∀ V : X.affineOpens, Submodule Γ(X, V.1) Γ(F, V.1))
    (hN : ∀ V : X.affineOpens, Maximal (fun L : Submodule Γ(X, V.1) Γ(F, V.1) ↦
      IsNowhereDense {p : Module.support Γ(X, V.1) Γ(F, V.1) |
        p.val ∈ Module.support Γ(X, V.1) L}) (N V)) :
    ∃ K : Subobject F, RingedSpace.IsCoherent X.toRingedSpace (K : X.Modules) ∧
      ∀ V : X.affineOpens, LinearMap.range (K.arrow.val.app (.op V.1)).hom = N V := by
  sorry

end AlgebraicGeometry.Scheme.Modules
