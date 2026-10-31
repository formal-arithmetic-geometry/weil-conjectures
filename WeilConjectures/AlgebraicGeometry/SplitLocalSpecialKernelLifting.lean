/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Filtration

/-! # Lifting the special kernel of a split torus homomorphism

Source: Conrad, Reductive group schemes, Remark B.1.2 and Corollary B.2.7, printed pp.280, 287;
Milne, Algebraic Groups (2017), Theorem 12.9(c), pp.233--234; Stacks Project, Tag 00IQ
(blueprint: lem-sfb-split-local-special-kernel-lifting).

The closed-fibre equality is expressed by the cartesian square defining the kernel, including
its immersion into the split torus. The lattice uses ULift only to share the ring's universe.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A special-fibre kernel in a split torus has a diagonalizable lift killed by the map.
Source: Conrad, Remark B.1.2 and Corollary B.2.7, printed pp.280, 287, combined with
Milne, Theorem 12.9(c), pp.233--234 and Stacks Project, Tag 00IQ
(blueprint: lem-sfb-split-local-special-kernel-lifting).

Proof:
1. The kernel of u on the residue field is closed: it is the pullback of the closed diagonal
   of the separated target. It is affine since the torus is affine.
2. Give its coordinate ring the Hopf structure of lem-sfb-affine-group-coordinate-hopf.
   Images of monomials are group-like. Let L be the kernel of the homomorphism from the
   character lattice to these units. The distinct images indexed by the quotient span the
   coordinate ring and are linearly independent by lem-sfb-coalgebra-group-like-independent.
   Thus this ring, compatibly with its quotient map, is k[Z^r/L]. This uses arbitrary residue
   fields and retains nonreduced kernels.
3. The quotient group-algebra map over R defines j. It is surjective, so Spec gives a closed
   immersion. Its Hopf compatibility follows on each basis element. Coefficient base change
   identifies its closed fibre with the kernel, compatibly with its inclusion into P_k.
4. Apply lem-sfb-diagonalizable-nilpotent-triviality over R/m^n with nilpotent ideal m/m^n.
   The quotient lattice is finitely generated, and u composed with j is trivial modulo m;
   hence it is trivial modulo every m^n. No smoothness or flatness of G is needed.
5. The equalizer of this composite and the identity-valued map is a closed subscheme of
   Spec R[Z^r/L], defined by an ideal I. Each coefficient of each element of I belongs to
   every m^n. Apply lem-weil-pbc-krull-intersection-jacobson to the finite module R, not to
   its possibly infinite-rank group algebra. All coefficients vanish, so I=0 and u j is
   identity-valued over R. -/
theorem splitLocalSpecialKernelLifting (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (r : ℕ) (G : Over (Spec (.of R))) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]
    [QuasiSeparated G.hom]
    (f : (ringDiagonalizableGroup R (Fin r → ULift.{u} ℤ)).X ⟶ G) [IsMonHom f] :
    ∃ L : AddSubgroup (Fin r → ULift.{u} ℤ),
      IsClosedImmersion (ringDiagonalizableGroupMap R (QuotientAddGroup.mk' L)).hom.hom.left ∧
      IsPullback
        (((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
          (ringDiagonalizableGroupMap R (QuotientAddGroup.mk' L)).hom.hom).left)
        (((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
          (toUnit (ringDiagonalizableGroup R ((Fin r → ULift.{u} ℤ) ⧸ L)).X)).left)
        (((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f).left)
        (((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map η[G]).left) ∧
      (ringDiagonalizableGroupMap R (QuotientAddGroup.mk' L)).hom.hom ≫ f =
        toUnit (ringDiagonalizableGroup R ((Fin r → ULift.{u} ℤ) ⧸ L)).X ≫ η[G] := by
  sorry

end AlgebraicGeometry
