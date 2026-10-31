/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.AmpleFiniteSetAffine

/-! # Affine neighbourhoods of finite sets in a Néron lft-model

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, 10.1, proof of Proposition 4,
printed p.291; 10.1 p.290 and 6.4 Theorem 1
(blueprint: lem-sfb-neron-lft-finite-set-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Every finite set of points of a Néron lft-model over an affine Dedekind base lies in
one affine open. The generic-fibre identification is a group isomorphism: its underlying
isomorphism `e` is multiplicative for the canonical base-changed group structure. The
hypothesis `hN` is bijectivity of the canonical restriction map on all smooth test schemes.

Source: BLR, Néron Models, 10.1, proof of Proposition 4, printed p.291; 6.4 Theorem 1
(blueprint: lem-sfb-neron-lft-finite-set-affine).

Proof:
1. By `lem-sfb-neron-lft-neutral-affine-product-chart`, the fibrewise identity subgroup
   `H = N⁰` is open. Its local affine product charts surject onto it, hence make it
   quasi-compact over each affine base neighbourhood. Finitely many such neighbourhoods
   cover the affine base, so `H` is quasi-compact and therefore of finite type. Smoothness
   restricts to this open by `lem-weil-pbc-smooth-restrict-open-subschemes`; separatedness
   restricts by the closed diagonal, and the geometric fibres of `H` are connected.
2. A finite union `W` of affine neighbourhoods of the points of `P` is quasi-compact
   (take the empty open when `P` is empty). Apply
   `lem-sfb-neutral-action-finite-type-saturation` to obtain a smooth separated finite-type
   open `X` containing `P`, stable under `H`, with geometric fibre components single `H`-orbits.
3. By `lem-sfb-dedekind-smooth-fibre-dense-affine`, choose an affine open `A` in `X`,
   dense in every geometric fibre, with effective Cartier complement `E`.
4. Each nonempty geometric fibre component meets `A`. Transitivity on each such component
   implies that the action `H × A → X` is surjective on points. Apply
   `lem-sfb-dedekind-action-boundary-ampleness` to obtain the absolutely ample line bundle
   `O_X(E)`.
5. Apply `lem-sc-ample-finite-set-affine` on `X` to obtain an affine open containing `P`.
   Its composite open immersion into `N` gives the asserted affine open of `N`.
-/
theorem exists_affineOpen_of_neronLft
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (hdim : ringKrullDim D = 1)
    (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (V : Over (Spec (CommRingCat.of K))) [GrpObj V] [IsCommMonObj V]
    [Smooth V.hom] [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (N : Over (Spec (CommRingCat.of D))) [GrpObj N] [IsCommMonObj N]
    [Smooth N.hom] [IsSeparated N.hom]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D K)))).obj N ≅ V)
    [IsMonHom e.hom]
    (hN : ∀ Y : Over (Spec (CommRingCat.of D)), Smooth Y.hom →
      Function.Bijective (fun f : Y ⟶ N ↦
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D K)))).map f ≫ e.hom))
    (P : Set N.left) (hP : P.Finite) :
    ∃ U : N.left.Opens, IsAffineOpen U ∧ P ⊆ (U : Set N.left) := by
  sorry

end AlgebraicGeometry
