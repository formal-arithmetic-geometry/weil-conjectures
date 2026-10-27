/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Normalizer conjugacy of Borels containing a maximal torus

Source: Milne, Algebraic Groups (2017), Corollary 17.11, final assertion,
printed p.355, and Theorems 17.9(b) and 17.10, printed pp.354--355.
(blueprint: lem-sfb-torus-normalizer-borel-transitivity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Two Borels containing a maximal torus are conjugate by a rational point normalizing
that torus. Both equalities are tested on every commutative algebra, retaining the full
closed subgroup schemes. Scalar extension of the rational point is composition with
the unique map to the tensor unit. The recorded maximal-torus predicate uses finite
products of G_m after algebraic closure; over this algebraically closed field this is
equivalent to the split-torus definition in the node, including rank zero.

Source: Milne, Corollary 17.11, final assertion, printed p.355;
Theorems 17.9(b) and 17.10, printed pp.354--355.
(blueprint: lem-sfb-torus-normalizer-borel-transitivity)

Proof, following the five steps of the node:
1. By lem-sfb-algebraic-group-homogeneous-quotient, form G/B₁ with the coset-fibre
   criterion and fpqc local lifts. It is proper by lem-sfb-borel-quotient-proper-geometry
   and nonempty because of the identity coset. By lem-weil-pbc-fpqc-representable-descent,
   local lifts identify it with the represented fppf coset sheaf from
   lem-sfb-homogeneous-orbit-quotient-geometry, which supplies rational-point lifts.
   Left multiplication on local representatives glues to the left G-action: two lifts
   differ by right multiplication by a B₁-section, which leaves their cosets unchanged.
2. Restrict the action to B₂. By lem-sfb-solvable-proper-fixed-point, choose a
   scheme-theoretically B₂-fixed rational point and lift it to g in G(k). On every
   algebra, the coset criterion gives g⁻¹B₂g contained in B₁. Conjugation preserves
   smoothness, connectedness and solvability, so maximality gives gB₁g⁻¹ = B₂.
3. The tori S = gTg⁻¹ and T lie in B₂ and are maximal there: a larger torus would
   give a larger torus in G, after conjugating back for S, contradicting maximality.
4. Apply the maximal-torus conjugacy clause of lem-sfb-borel-maximal-torus-conjugacy
   to the smooth connected affine finite-type group B₂, obtaining h in B₂(k) with
   hSh⁻¹ = T as subgroup schemes. No reductivity is needed.
5. Put n = hg. Associativity on every algebra gives nTn⁻¹ = hSh⁻¹ = T and
   nB₁n⁻¹ = hB₂h⁻¹ = B₂, the last equality since h belongs to B₂. These are
   natural equalities of subfunctors on all algebras, hence of closed subgroup schemes. -/
theorem torus_normalizer_borel_transitivity {k : Type u} [Field k] [IsAlgClosed k]
    (G T B₁ B₂ : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (i₁ : B₁ ⟶ G) (hB₁ : IsBorelGroupScheme i₁.hom.hom)
    (i₂ : B₂ ⟶ G) (hB₂ : IsBorelGroupScheme i₂.hom.hom)
    (j₁ : T ⟶ B₁) (hj₁ : j₁ ≫ i₁ = iT)
    (j₂ : T ⟶ B₂) (hj₂ : j₂ ≫ i₂ = iT) :
    ∃ n : 𝟙_ (Over (Spec (.of k))) ⟶ G.X,
      ∀ (A : Type u) [CommRing A] [Algebra k A],
        Set.range (fun t : StandardGroupSchemes.affine k A ⟶ T.X ↦
          (toUnit (StandardGroupSchemes.affine k A) ≫ n) * (t ≫ iT.hom.hom) *
            (toUnit (StandardGroupSchemes.affine k A) ≫ n)⁻¹) =
          Set.range (fun t : StandardGroupSchemes.affine k A ⟶ T.X ↦ t ≫ iT.hom.hom) ∧
        Set.range (fun b : StandardGroupSchemes.affine k A ⟶ B₁.X ↦
          (toUnit (StandardGroupSchemes.affine k A) ≫ n) * (b ≫ i₁.hom.hom) *
            (toUnit (StandardGroupSchemes.affine k A) ≫ n)⁻¹) =
          Set.range (fun b : StandardGroupSchemes.affine k A ⟶ B₂.X ↦ b ≫ i₂.hom.hom) := by
  sorry

end AlgebraicGeometry
