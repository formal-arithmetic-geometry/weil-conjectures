/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Semisimple
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
import WeilConjectures.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import WeilConjectures.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import WeilConjectures.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup

/-!
# Maximal tori in Borels and conjugacy of maximal tori

Source: Milne, Algebraic Groups (2017), Theorem 17.10 and the paragraph after
Definition 17.12, printed pp.354--355; Theorem 16.33(d), printed pp.336--337.
(blueprint: lem-sfb-borel-maximal-torus-conjugacy)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every Borel contains an ambient maximal torus, and any two ambient maximal tori
are conjugate by a rational point. The displayed equivalence tests equality of the
conjugate closed subgroups on every commutative algebra, including nonreduced ones.
Over the algebraically closed base the recorded torus predicate is equivalent to being
isomorphic to a finite product of G_m; its empty product permits rank zero.

Source: Milne, Theorem 17.10, paragraph after Definition 17.12, printed pp.354--355,
and Theorem 16.33(d), printed pp.336--337.
(blueprint: lem-sfb-borel-maximal-torus-conjugacy)

Proof, following the five steps of the node:
1. By lem-sfb-multiplicative-type-largest-subtorus, tori are smooth and connected.
   They are commutative and hence solvable. Starting with the rank-zero torus,
   choose containing tori of greatest dimension. The dimension bound and strict
   increase in lem-sfb-solvable-normal-subgroup-products give maximal tori. Applying
   the same argument to smooth connected solvable subgroups gives containing Borels.
2. For Borels B and C form G/B by lem-sfb-homogeneous-orbit-quotient-geometry, with
   the left translation action and its identity coset. The quotient is faithfully
   flat and finitely presented, has the coset-fibre property, and admits fppf local
   lifts, so lem-sfb-borel-quotient-proper-geometry makes it proper. Apply
   lem-sfb-solvable-proper-fixed-point to C. Lift its fixed rational point to g in
   G(F) by the homogeneous-quotient lemma. On every algebra, fixedness and the
   coset-fibre property give g⁻¹Cg contained in B. Borel maximality gives equality.
3. In a smooth connected solvable H, lem-sfb-smooth-connected-derived-subgroup
   makes every derived-series term smooth and connected; its successive quotients
   are commutative because the commutator factors through the next term. Apply
   lem-sfb-lie-kolchin-triangular-embedding and lem-sfb-triangular-diagonal-kernel
   to identify H with a subgroup J of upper triangular matrices, with unipotent
   kernel V and smooth connected diagonal quotient D. The latter is a torus by
   lem-sfb-multiplicative-type-largest-subtorus. By lem-sfb-solvable-torus-complements,
   each maximal torus maps isomorphically to D, giving two sections D to J.
   By lem-sfb-triangular-quotient-section-conjugacy the sections are conjugate by
   v in V(F); their images, the two maximal tori, are therefore conjugate on all
   algebras.
4. Put the given maximal tori in Borels B₁ and B₂ using step 1. Conjugate B₁ to B₂
   by step 2. The transported torus and the second torus are maximal in B₂, so
   step 3 conjugates them by b in B₂(F). The product bg is the desired conjugator;
   the conjugation calculation holds after every algebra extension.
5. Choose any ambient maximal torus and a Borel containing it by step 1. Conjugate
   that Borel to the prescribed one by step 2. The conjugate torus lies in that
   Borel and remains maximal in G by conjugating any larger torus back. -/
theorem borel_contains_maximal_torus_and_conjugacy {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    (∀ (B : Grp (Over (Spec (.of F)))) (iB : B ⟶ G),
      IsBorelGroupScheme iB.hom.hom →
      ∃ (T : Grp (Over (Spec (.of F)))) (iT : T ⟶ G),
        ReductiveTorusCentralizer.IsMaximalTorus iT ∧
        ∃ j : T ⟶ B, j ≫ iB = iT) ∧
    (∀ (T₁ T₂ : Grp (Over (Spec (.of F)))) (i₁ : T₁ ⟶ G) (i₂ : T₂ ⟶ G),
      ReductiveTorusCentralizer.IsMaximalTorus i₁ →
      ReductiveTorusCentralizer.IsMaximalTorus i₂ →
      ∃ g : 𝟙_ (Over (Spec (.of F))) ⟶ G.X,
        ∀ (A : Type u) [CommRing A] [Algebra F A]
          (z : StandardGroupSchemes.affine F A ⟶ G.X),
          (∃ t₂ : StandardGroupSchemes.affine F A ⟶ T₂.X, t₂ ≫ i₂.hom.hom = z) ↔
          ∃ t₁ : StandardGroupSchemes.affine F A ⟶ T₁.X,
            (toUnit (StandardGroupSchemes.affine F A) ≫ g) * (t₁ ≫ i₁.hom.hom) *
              (toUnit (StandardGroupSchemes.affine F A) ≫ g)⁻¹ = z) := by
  sorry

end AlgebraicGeometry
