/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections

/-! # Unramified group schemes detected at the identity by dual numbers

Source: Stacks Project, groupoids.tex, Tag 047I; morphisms.tex, Tag 02G5;
varieties.tex, Tags 0B2C and 0B2D; moduli-curves.tex, Tag 0E6G, first proof paragraph
(blueprint: lem-sfb-group-scheme-identity-dual-unramified).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A finite-type group scheme over a field is unramified exactly when every dual-number
point reducing to its identity is the constant identity point. The identity is `η[G].left`;
the zero section `i` is induced by `TrivSqZeroExt.fstHom K K K`, and the projection `p`
is induced by `algebraMap K (DualNumber K)`. The first equation on `v` says it is over `K`.
No commutativity, smoothness, reducedness or characteristic hypothesis is needed.

Source: Stacks Project, Tags 047I, 02G5, 0B2C, 0B2D and 0E6G, first proof paragraph.
(blueprint: lem-sfb-group-scheme-identity-dual-unramified).

Proof:
1. Write `f = G.hom`, `e = η[G].left`, and `M = Γ(Spec K, e^*Ω¹_{G/K})`.
   The identity section satisfies `e ≫ f = 𝟙`, so its residue field is `K`.
   A module sheaf on the one-point scheme `Spec K` is zero exactly when its sections
   are zero. Thus `e^*Ω¹_{G/K} = 0` is equivalent to `M = 0`.
2. The dual-number points over `K` reducing to `e` are precisely the tangent space
   at `e` (def-sc-scheme-tangent-space). Its zero is `p ≫ e`, since scalar zero
   precomposes with the dual-number map sending epsilon to zero. By
   lem-sfb-rational-tangent-differential-fibre-duality this tangent space is
   `Hom_K(M,K)`. Hence the condition in the statement says `Hom_K(M,K) = 0`.
3. Apply lem-sc-dual-map-injective-iff-surjective to the map from the zero vector
   space to `M`. Its dual is injective exactly when `Hom_K(M,K) = 0`, so dual
   separation makes `M = 0`. Conversely the dual of zero is zero; no dimension
   assumption is used.
4. By lem-sfb-group-scheme-differentials-from-identity, `Ω¹_{G/K} ≅ f^*e^*Ω¹_{G/K}`.
   Pullback of a zero module is zero by the tensor formula (def-pc-module-pullback).
   Consequently `M = 0` is equivalent to `Ω¹_{G/K} = 0` on all of `G`.
5. Finite type implies locally finite type. On affine charts the differential-sections
   comparison (lem-sc-relative-differentials-affine-sections) identifies the sections
   with `Ω_{A/K}`. Tag 02G5, equivalently the affine criterion in
   def-weil-unramified-morphism, says that the vanishing of these differentials is
   equivalent to unramifiedness. Combine steps 1--4 to obtain both implications. -/
theorem isUnramified_iff_identityDualNumberPoints {K : Type u} [Field K]
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsUnramified G.hom ↔
      ∀ v : Spec (.of (DualNumber K)) ⟶ G.left,
        v ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ v =
          η[G].left →
        v = Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ η[G].left := by
  sorry

end AlgebraicGeometry
