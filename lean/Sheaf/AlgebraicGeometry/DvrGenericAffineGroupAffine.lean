/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.AffinePrincipalAffinizationIsomorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTarget
import Sheaf.AlgebraicGeometry.FpqcAffineDescent

/-! # Affineness of a flat group over a discrete valuation ring

Source: Prasad--Yu, On quasi-reductive group schemes, Section 3, Proposition 3.1,
printed page 5, Raynaud's affineness theorem
(blueprint: lem-sfb-dvr-generic-affine-group-affine).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A separated flat group scheme of finite type over a DVR is affine if its generic
fibre is affine. No smoothness, connectedness or residue-field condition is required.

Source: Prasad--Yu, On quasi-reductive group schemes, Proposition 3.1, printed page 5
(blueprint: lem-sfb-dvr-generic-affine-group-affine).

Proof (the six steps of the accepted DAG split):
1. By lem-sfb-trait-group-finite-smooth-cover, pass to a faithfully flat local DVR
   extension with algebraically closed residue field and a finite surjective smooth
   covering group N. Its generic fibre is affine by affine base change and finite
   morphism permanence (lem-weil-pbc-affine-morphism-permanence and
   lem-weil-pbc-finite-morphism-permanence).
2. N is flat by lem-pc-smooth-flat. By lem-sfb-flat-trait-group-affinization, the
   canonical u : N → Spec Γ(N, O) is a group homomorphism. Finite type and separatedness
   imply qcqs by lem-weil-pbc-qcqs-over-affine; no finite generation of Γ(N, O) is used.
3. The finite principal affine cover of lem-sfb-smooth-trait-principal-translate-cover
   and lem-a1-affine-principal-affinization-isomorphism identify each chart with its
   distinguished open in Spec Γ(N, O). Glue the inverse maps to make u an open immersion.
   It is quasi-compact by lemma-nagata-open-immersion-qc-over-separated-target, since
   N is quasi-compact over the base and its affine target is quasi-separated over it.
4. By lem-weil-pbc-open-immersion-base-change, the special fibre of u is an open
   immersion of groups. Apply lem-sfb-field-groupoid-open-image-closed to its open
   image. Its image is closed in the special fibre, hence in Spec Γ(N, O).
5. Apply lem-sfb-immersion-principal-affineness to u and the uniformizer: the generic
   principal inverse image is affine by step 1 and the special-fibre image is closed
   by step 4. Thus N is affine.
6. Descend affineness first across the finite surjection by
   lem-weil-pbc-finite-surjective-affine-target, then across the singleton fpqc cover
   by lem-weil-pbc-fpqc-descend-affine. Affine-morphism permanence over the affine base
   gives affineness of G. -/
theorem isAffine_of_affine_genericFiber_of_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Flat G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hgeneric : IsAffine
      (pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    IsAffine G.left := by
  sorry

end AlgebraicGeometry
