/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SolvableGroupStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.RingTheory.SmoothAlgebraReduced

/-! # The projective variety of Borel subgroups

Source: Milne, Algebraic Groups (2017), Theorem 17.9, printed p.354; paragraph after
Definition 17.12, printed p.355; Theorem 17.48, printed p.367; Section 17f and
Lemma 17.52, printed pp.368--369. (blueprint: lem-sfb-general-borel-flag-variety)

Borels are subobjects, so distinct embeddings presenting the same subgroup are identified.
The group structure on a representative is only a witness in its Borel predicate.
The bundled internal module object supplies the scheme action and both action identities.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every smooth connected affine algebraic group has its smooth connected projective
variety of Borels. The equivalence labels all rational points by actual subgroup subobjects.
The conjugation clause describes the conjugate subgroup on every test algebra, independently
of a choice of presentation. The last clause characterizes scheme-theoretically torus-fixed
rational points by factorization of the torus inclusion through the Borel inclusion.

Source: Milne, Theorem 17.9, printed p.354; paragraph after Definition 17.12, printed p.355;
Theorem 17.48, printed p.367; Section 17f and Lemma 17.52, printed pp.368--369.
(blueprint: lem-sfb-general-borel-flag-variety)

Proof, following the eight steps of the node:
1. Choose a smooth connected solvable closed subgroup B₀ of greatest dimension, starting
   with the identity subgroup. The dimension bounds and strict increase for proper smooth
   connected inclusions in lem-sfb-solvable-normal-subgroup-products make it a Borel.
   A terminating derived series is equivalent to a finite subnormal series with commutative
   quotients, by placing successive commutators in the successive terms of such a series.
2. By lem-sfb-solvable-subgroup-flag-realization, realize B₀ as the full stabilizer of a
   complete flag in a faithful representation. Its orbit has minimum dimension by
   lem-sfb-smooth-group-orbit-geometry. A nonempty boundary would have a rational closed
   point by lem-sc-lft-over-field-jacobson-space and
   lem-weil-pbc-closed-point-residue-field-base, with a smaller orbit, a contradiction.
3. Give the closed orbit X its reduced structure. The orbit lemma gives smoothness and a
   faithfully flat surjection G → X; hence X is nonempty and connected. The flag-realization
   lemma gives properness and finite type. Compose its closed embedding with the flag
   scheme's projective embedding using lem-weil-pbc-closed-immersion-comp. The invariant
   closure clause restricts the action: G × X is reduced, by smoothness over reduced X and
   lem-sfb-smooth-algebra-over-reduced-ring, so the set-theoretic factorization through the
   reduced closed orbit is unique. The action identities restrict by uniqueness.
   Apply lem-sfb-homogeneous-orbit-quotient-geometry to identify X with G/B₀ and obtain
   separatedness and the rational-point quotient description.
4. For any Borel B, lem-sfb-solvable-proper-fixed-point gives a B-fixed rational point of X.
   Lift it to g ∈ G(k) using the homogeneous quotient lemma. Its full flag stabilizer gives
   B ⊆ gB₀g⁻¹ as subgroup schemes, hence equality by maximality. This proves conjugacy.
5. Label B = gB₀g⁻¹ by gF. The equality N_G(B₀) = B₀ from
   lem-sfb-borel-scheme-normalizer makes this independent of g and injective; the rational
   quotient description makes it surjective. Left multiplication proves equivariance and
   transitivity. Subobjects identify exactly the equivalent subgroup presentations.
6. On every commutative k-algebra A, u fixes gF precisely when g⁻¹ug fixes F, equivalently
   when g⁻¹ug ∈ B₀(A), equivalently u ∈ B(A), by the full flag stabilizer. This includes
   nonreduced A and gives the displayed stabilizer equivalence.
7. Every torus, including rank zero, is smooth connected and commutative: use the Laurent
   coordinates, smoothness and domain clause of lem-trf-split-lattice-torus-projection.
   Choose a greatest-dimensional smooth connected solvable overgroup; the strict dimension
   increase of lem-sfb-solvable-normal-subgroup-products makes it a Borel containing T.
8. The stabilizer calculation makes a Borel point fixed after every algebra extension by T
   precisely when T(A) ⊆ B(A) for every A. Apply this to the universal point of the affine
   torus to factor its inclusion through B; the converse is immediate from the stabilizer.
-/
theorem exists_general_borel_flag_variety {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) (hG : SolvableGroupStructure.IsAlgebraic G)
    [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    ∃ (X : Mod (Over (Spec (.of k))) G.X)
      (b : {B : Subobject G.X // ∃ h : GrpObj (B : Over (Spec (.of k))),
        @IsBorelGroupScheme k _ _ G.X (B : Over (Spec (.of k))) G.grp h B.arrow} ≃
          (𝟙_ (Over (Spec (.of k))) ⟶ X.X)),
      Nonempty X.X.left ∧ Smooth X.X.hom ∧ ConnectedSpace X.X.left ∧
      IsHProjective X.X.hom ∧ LocallyOfFiniteType X.X.hom ∧ QuasiCompact X.X.hom ∧
      IsProper X.X.hom ∧ IsSeparated X.X.hom ∧
      (∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ X.X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X, g • x = y) ∧
      (∀ B C, ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X,
        b C = g • b B ↔
          ∀ (A : Type u) [CommRing A] [Algebra k A]
            (z : StandardGroupSchemes.affine k A ⟶ G.X),
            (∃ c : StandardGroupSchemes.affine k A ⟶ (C.val : Over (Spec (.of k))),
              c ≫ C.val.arrow = z) ↔
            ∃ t : StandardGroupSchemes.affine k A ⟶ (B.val : Over (Spec (.of k))),
              t ≫ B.val.arrow =
                (toUnit (StandardGroupSchemes.affine k A) ≫ g)⁻¹ * z *
                  (toUnit (StandardGroupSchemes.affine k A) ≫ g)) ∧
      (∀ B, ∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : StandardGroupSchemes.affine k A ⟶ G.X),
        g • (toUnit (StandardGroupSchemes.affine k A) ≫ b B) =
            toUnit (StandardGroupSchemes.affine k A) ≫ b B ↔
          ∃ t : StandardGroupSchemes.affine k A ⟶ (B.val : Over (Spec (.of k))),
            t ≫ B.val.arrow = g) ∧
      (∀ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ G),
        IsClosedSubgroupScheme i.hom.hom → SolvableGroupStructure.IsTorus T →
          ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X.X,
            ∃ j : T.X ⟶ ((b.symm x).val : Over (Spec (.of k))),
              j ≫ (b.symm x).val.arrow = i.hom.hom) ∧
      (∀ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ G),
        IsClosedSubgroupScheme i.hom.hom → SolvableGroupStructure.IsTorus T → ∀ B,
          (∀ (A : Type u) [CommRing A] [Algebra k A]
            (t : StandardGroupSchemes.affine k A ⟶ T.X),
            (t ≫ i.hom.hom) • (toUnit (StandardGroupSchemes.affine k A) ≫ b B) =
              toUnit (StandardGroupSchemes.affine k A) ≫ b B) ↔
          ∃ j : T.X ⟶ (B.val : Over (Spec (.of k))), j ≫ B.val.arrow = i.hom.hom) := by
  sorry

end AlgebraicGeometry
