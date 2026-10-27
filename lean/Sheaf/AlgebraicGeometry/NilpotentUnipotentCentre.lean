/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Nilpotent groups with unipotent centre

Source: Milne, Algebraic Groups (2017), Lemma 16.46, pp.340--341;
Theorem 14.5 and Corollary 14.9, pp.281--282
(blueprint: lem-sfb-nilpotent-unipotent-centre).

Unipotence is written as a closed faithful representation satisfying the unitriangular
coordinate equations over every commutative algebra. This includes nonsmooth group schemes.
The finite central series and the represented centre likewise retain all algebra-valued points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A connected nilpotent affine algebraic group with unipotent scheme-theoretic centre
is unipotent. The closed subgroup Z is the centre by its universal centralizer subfunctor.
Neither smoothness nor perfectness is required, for G, Z, or the supplied central series.
A closed embedding in GL_n with all the displayed equations factors as a closed embedding
in U_n, since the latter is the closed subgroup cut out by precisely those equations.

Source: Milne, Algebraic Groups (2017), Lemma 16.46, pp.340--341;
Theorem 14.5 and Corollary 14.9, pp.281--282
(blueprint: lem-sfb-nilpotent-unipotent-centre).

Proof plan:
1. By lem-sfb-unipotence-field-extension pass to an algebraic closure. The given series
   base changes, and lem-sfb-affine-group-centre-base-change identifies the centre.
   The identity section and lem-sbc-connected-rational-point-geometrically-connected
   preserve connectedness. Induct on the central-series length s. Length zero is the
   trivial group, embedded in U_1; at length one the group equals its unipotent centre.
2. For s at least two form H = G/Z by lem-sfb-affine-normal-quotient-geometry.
   It is connected. The last nontrivial series term is central; the images of the other
   terms, supplied by lem-sfb-algebraic-group-homomorphism-factorization, give a series
   for H of length at most s-1. Commutators descend by fppf local lifting. By
   lem-sfb-commutative-multiplicative-part choose D, the largest multiplicative-type
   subgroup of Z(H). Its inverse image N is normal in G and N/Z is D.
3. Commutators in N lie in central Z and descend by the fppf quotient property to a
   separately homomorphic pairing D times D to Z. Each partial homomorphism vanishes
   over every base algebra by lem-sfb-multiplicative-unipotent-base-algebra-vanishing.
   Hence the pairing is trivial on all algebra-valued points and N is commutative.
4. By lem-sfb-commutative-diagonalizable-unipotent-product write N = U times T.
   The maps U to D and Z to T vanish by lem-sfb-unipotent-to-multiplicative-trivial.
   Fppf lifting then makes T to D an isomorphism and U = Z. Every automorphism of N
   preserves T, since its component T to Z vanishes over every base algebra by
   lem-sfb-multiplicative-unipotent-base-algebra-vanishing. Thus T is normal in G.
   Apply lem-sfb-normal-multiplicative-layers-central with the trivial lower subgroup:
   T lies in Z(G) = Z, so the direct-product intersection forces T = 1 and D = 1.
5. The quotient clause of lem-sfb-commutative-multiplicative-part makes Z(H) unipotent.
   Apply induction to H. The fppf exact sequence with unipotent kernel Z and quotient H
   makes G unipotent by lem-sfb-unipotent-extension-arbitrary. Finally descend along
   the algebraic closure by lem-sfb-unipotence-field-extension. -/
theorem unipotent_of_nilpotent_of_unipotent_centre
    {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    (hG : IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom)
    (hconn : ConnectedSpace G.X.left)
    (hseries : ∃ (s : ℕ) (H : Fin (s + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (s + 1), H j ⟶ G),
      (∀ j : Fin (s + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsNormalSubgroupScheme (i j).hom.hom) ∧
      IsIso (i 0) ∧ Nonempty (H (Fin.last s) ≅ Grp.trivial _) ∧
      (∀ j : Fin s, ∃ l : H j.succ ⟶ H j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
      ∀ (j : Fin s) (A : Type u) [CommRing A] [Algebra k A]
        (g : StandardGroupSchemes.affine k A ⟶ G.X)
        (h : StandardGroupSchemes.affine k A ⟶ (H j.castSucc).X),
        ∃ z : StandardGroupSchemes.affine k A ⟶ (H j.succ).X,
          z ≫ (i j.succ).hom.hom =
            g * (h ≫ (i j.castSucc).hom.hom) * g⁻¹ *
              (h ≫ (i j.castSucc).hom.hom)⁻¹)
    (Z : Grp (Over (Spec (.of k)))) (iZ : Z ⟶ G)
    (hiZ : IsClosedSubgroupScheme iZ.hom.hom)
    (hZ : ∀ (A : Type u) [CommRing A] [Algebra k A],
      ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A =
        Set.range (fun z : StandardGroupSchemes.affine k A ⟶ Z.X ↦ z ≫ iZ.hom.hom))
    (hunitriangular : ∃ n : ℕ, 0 < n ∧
      ∃ r : Z.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A]
          (z : (Spec (.of A)).asOver (Spec (.of k)) ⟶ Z.X),
          (∀ a : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (z ≫ r)).val
              (ULift.up a) (ULift.up a) = 1) ∧
          ∀ a b : Fin n, b < a →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (z ≫ r)).val
              (ULift.up a) (ULift.up b) = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
      IsClosedSubgroupScheme r ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.X),
        (∀ a : Fin n,
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (g ≫ r)).val
            (ULift.up a) (ULift.up a) = 1) ∧
        ∀ a b : Fin n, b < a →
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (g ≫ r)).val
            (ULift.up a) (ULift.up b) = 0 := by
  sorry

end AlgebraicGeometry
