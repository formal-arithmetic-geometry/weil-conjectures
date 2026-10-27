/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.NeronLftModel
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange

/-!
# Finite flat descent of Néron lft-model existence

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, §10.1, Proposition 4, pp. 290–291
(blueprint: lem-sfb-finite-flat-neron-lft-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable section

/-- Existence of a Néron lft-model descends to every smooth closed subgroup.
Source: BLR §10.1, Proposition 4 (blueprint: lem-sfb-finite-flat-neron-lft-descent).

Proof plan:
1. The closed subgroup H of the finite-type G is finite type. Let M' be the given model.
   By lem-sfb-neron-lft-weil-restriction-geometry its Weil restriction W is a smooth
   separated commutative S-group, with finite-type generic fibre and neutral component.
2. The adjunction map H → W_E is a monomorphism: after the faithfully flat extension
   E'/E this follows from the closed inclusion H_E' → G_E'; equality descends by
   lem-a1-algebraic-space-fpqc-sheaf and def-trf-scheme-algebraic-space. Closedness after
   base change uses lem-weil-pbc-closed-immersion-base-change. The homomorphism theorem
   lem-sfb-algebraic-group-homomorphism-factorization makes H → W_E a closed immersion.
3. For arbitrary smooth X/S, smooth-flat (lem-pc-smooth-flat) and base-change smoothness
   (lem-sfb-scheme-lfp-smooth-flat-base-change), Weil adjunction and the mapping property
   of M' identify Hom_S(X,W) with Hom_E(X_E,W_E). All maps are generic restriction.
   Here D' tensored with E is E', since the resulting finite E-algebra is a domain.
4. Apply lem-sfb-dedekind-lft-generic-subgroup-closure to H in W_E. Its closure C is flat,
   separated, commutative and lft, with C_E = H. The group smoothening from
   lem-sfb-lft-closed-subgroup-group-smoothening gives N → C, smooth separated
   commutative lft, generically an isomorphism, universal for smooth test schemes.
5. Extend X_E → H uniquely to X → W by step 3, factor through C by flatness of X and
   the closure property, and lift uniquely to N by smoothening. The generic map is the
   original one since H → W_E is monic. Uniqueness follows successively in W, C, N.
   This proves the Néron mapping property; the identity inclusion H = G is allowed. -/
theorem exists_neronLftModel_of_finite_faithfullyFlat
    (D D' : Type u) [CommRing D] [CommRing D']
    [IsDedekindDomain D] [IsDedekindDomain D']
    (hD : ringKrullDim D = 1) (hD' : ringKrullDim D' = 1)
    [Algebra D D'] [Module.Finite D D'] [Module.FaithfullyFlat D D']
    (hinj : Function.Injective (algebraMap D D'))
    (G H : Grp (Over (Spec (.of (FractionRing D)))))
    [IsCommMonObj G.X] [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth H.X.hom] (i : H ⟶ G) [IsClosedImmersion i.hom.hom.left]
    (hmodel : ∃ (N' : Grp (Over (Spec (.of D'))))
      (e' : (Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap D' (FractionRing D'))))).mapGrp.obj N' ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom
          (IsFractionRing.map (K := FractionRing D) (L := FractionRing D') hinj)))).mapGrp.obj G),
      IsNeronLftModel N'
        ((Over.pullback (Spec.map (CommRingCat.ofHom
          (IsFractionRing.map (K := FractionRing D) (L := FractionRing D') hinj)))).mapGrp.obj G)
        e') :
    ∃ (N : Grp (Over (Spec (.of D))))
      (e : (Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap D (FractionRing D))))).mapGrp.obj N ≅ H),
      IsNeronLftModel N H e ∧ IsCommMonObj N.X := by
  sorry

end

end AlgebraicGeometry
