/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import WeilConjectures.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Intersecting a Borel subgroup with a torus centralizer

Source: Milne, Algebraic Groups (2017), Theorem 17.46 and proof, printed pp.365--366;
restatement 17.72, p.376; Corollary 13.10 and Theorem 17.38.
(blueprint: lem-sfb-torus-centralizer-borel-intersection)

The centralizer is specified on every commutative test algebra, with commutation after
all further algebra extensions. The intersection is a pullback of schemes, retaining
its scheme structure. The torus is split of arbitrary finite rank, including zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The centralizer of a torus contained in a Borel is smooth and connected, and its
scheme-theoretic intersection with that Borel is a Borel of the centralizer.
Source: Milne, Theorem 17.46 and proof, pp.365--366; 17.72, p.376.
(blueprint: lem-sfb-torus-centralizer-borel-intersection)

Proof plan, following the node's eleven steps:
1. Apply lem-sfb-torus-centralizer-smooth-connected to G and B, using
   lem-weil-geometrically-connected-algebraic-closure. Obtain C = C_G(S) and
   H = C_B(S); the all-algebra identities and def-pc-fibre-product identify H with
   B ×_G C. By lem-sfb-smooth-connected-derived-subgroup, induction embeds each
   derived subgroup of H in that of B. Hence H is solvable, smooth and connected.
2. Use lem-sfb-homogeneous-orbit-quotient-geometry to form q : G → Q = G/B and
   its fpqc coset description. By lemma-nagata-finite-type-to-separated-target,
   lem-weil-pbc-finite-type-over-noetherian, pqf-lem-lft-fp-locnoeth and
   lem-weil-pbc-qcqs-morphism-permanence, q is finitely presented.
   Apply lem-sfb-borel-quotient-proper-geometry: Q is proper and q smooth. By
   lem-pc-smooth-flat and lem-weil-pbc-flat-lfp-open, q is an open surjection.
   The C-stabilizer of q(1) is H on every algebra. By
   lem-sfb-smooth-group-orbit-geometry, O = C·q(1) is smooth and locally closed;
   lem-sfb-homogeneous-orbit-quotient-geometry identifies O with C/H.
3. The derived series and lem-sfb-smooth-connected-derived-subgroup give a finite
   normal series with commutative quotients. The algebraically closed field is perfect,
   so lem-sfb-perfect-solvable-unipotent-torus gives U normal unipotent in B and
   φ : B → D = B/U a torus quotient. Choose a maximal torus T containing S by
   bounded dimension and strict growth, using lem-sfb-multiplicative-type-largest-subtorus
   and lem-sfb-solvable-normal-subgroup-products. By lem-sfb-solvable-torus-complements,
   φ restricted to T is an isomorphism. Every b in B(F) has a unique expression ut:
   choose t from its image under φ and set u = bt⁻¹. The quotient's fpqc local coset
   description and faithful flatness give ker φ = U as subgroup schemes.
4. Put M = q⁻¹(|O|), the topological image of C ×_F B by the quotient's geometric
   lifting criterion (lem-sfb-homogeneous-orbit-quotient-geometry). It is locally closed.
   Its reduced closure Z is connected: C is geometrically connected, so C ×_F B is
   connected by lem-weil-pbc-geometrically-connected-product-components, and images
   and closures preserve connectedness. By def-weil-pbc-scheme-reduction and
   def-weil-closed-immersion, Z is an affine finite-type reduced closed subscheme of G
   containing 1.
5. By lem-sc-group-scheme-separated-field and
   lem-sfb-constant-source-closed-factorization-locus, the locus L of y for which
   conjugation y⁻¹Sy factors through B is closed. Multiplication C × B → G factors
   through L on every algebra, so |Z| lies in |L|. By
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme, Z factors through L.
   Its universal property gives the actual morphism Z × S → B, (y,s) ↦ y⁻¹sy.
6. Compose with φ. By lem-sfb-diagonalizable-group-geometric-criteria, S and D are
   diagonalizable. Apply lem-sfb-diagonalizable-hom-family-rigidity to the connected
   affine finite-type parameter Z and its point 1: φ(y⁻¹sy) = φ(s) as morphisms,
   thus after every test algebra extension, including nonreduced algebras.
7. Right translation by b in B(F) preserves M and hence its reduced closure Z.
   Therefore y in Z(F) implies yb in Z(F).
8. For y in Z(F), choose a maximal torus T_y of B containing y⁻¹Sy using the
   dimension argument of step 3. By lem-sfb-borel-maximal-torus-conjugacy inside B,
   choose b with b⁻¹T_y b = T. Write b = ut as in step 3. Since t lies in T,
   conjugating the inclusion t⁻¹u⁻¹y⁻¹Syu t ⊆ T by t gives u⁻¹y⁻¹Syu ⊆ T
   as subgroup schemes.
9. We have yu in Z(F). The rigidity identity at yu and injectivity of φ on T imply
   (yu)⁻¹s(yu) = s after every algebra extension. Thus yu lies in C(F), and
   y = (yu)u⁻¹ lies in M. Hence Z(F) is contained in M.
10. M is open dense in |Z|. A nonempty closed complement would have a closed point
    by lem-sc-lft-over-field-jacobson-space and then an F-point by
    lem-weil-pbc-closed-point-residue-field-base, contradicting step 9. Thus M is closed
    in G. Since q is an open surjection, |O| is closed in Q; its locally closed
    immersion is a closed immersion. By lem-weil-pbc-closed-immersion-proper, O is proper.
11. For any smooth connected solvable H ⊆ J ⊆ C, apply
    lem-sfb-solvable-proper-fixed-point to J acting on nonempty proper O = C/H.
    Lift the fixed F-point to c in C(F) using
    lem-sfb-homogeneous-orbit-quotient-geometry. Scheme-theoretic fixedness says
    c⁻¹Jc ⊆ H on every algebra. By lem-sfb-solvable-normal-subgroup-products,
    dim J ≤ dim H, while H strictly contained in J would give dim H < dim J.
    Thus J = H, establishing Borel maximality. -/
theorem exists_torusCentralizer_borel_intersection
    {F : Type u} [Field F] [IsAlgClosed F]
    (G B S : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (iS : S ⟶ B) (hS : IsClosedSubgroupScheme iS.hom.hom)
    (hT : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)) :
    ∃ (C : Grp (Over (Spec (.of F)))) (iC : C ⟶ G),
      IsClosedSubgroupScheme iC.hom.hom ∧ Smooth C.X.hom ∧ ConnectedSpace C.X.left ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A],
        ReductiveTorusCentralizer.centralizerPoints (iS ≫ iB) A =
          Set.range (fun c : StandardGroupSchemes.affine F A ⟶ C.X ↦ c ≫ iC.hom.hom)) ∧
      ∃ (H : Grp (Over (Spec (.of F)))) (jB : H ⟶ B) (jC : H ⟶ C),
        IsPullback jB.hom.hom.left jC.hom.hom.left iB.hom.hom.left iC.hom.hom.left ∧
          IsBorelGroupScheme jC.hom.hom := by
  sorry

end AlgebraicGeometry
