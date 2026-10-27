/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q131 and Q28
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-! # Geometric coroots in the split Borel-pair root datum

Source: Milne, Algebraic Groups (2017), Theorem 21.11(d)--(e), pp.428--430;
Sections 21.29--21.35, pp.433--435, and the Borel-pair sources of
`reductive_borel_pair_structure`.
(blueprint: lem-sfb-reductive-borel-pair-structure)

This interface specifies the coroots by the actual normalizer action in addition
to the abstract root-datum axioms. The semisimple-group clause is the existing
`semisimpleGroupScheme_isReductive` imported from the original module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A reductive group has a split maximal torus contained in a Borel. Every such
pair has a proper finite-type flag quotient with its right-multiplication torsor,
a unipotent radical split off by the given torus, and the reduced integral root
datum with the positive base determined by that Borel.

Source: Milne, Definition 17.6 and Theorem 17.9, pp.353--355; Theorem 16.33(d),
pp.335--336; Definition 19.22, p.402; Theorem 21.11 and Corollary 21.12;
21.29--21.35, pp.433--435; Section 18c, p.390.
(blueprint: lem-sfb-reductive-borel-pair-structure)

Proof plan:
1. Choose a smooth connected solvable subgroup of maximum dimension, using
   lem-sfb-solvable-normal-subgroup-products for strict dimension growth.
   By lem-sfb-solvable-subgroup-flag-realization it is a full flag stabilizer.
   The orbit has minimum dimension by lem-sfb-smooth-group-orbit-geometry;
   a nonempty boundary would contain a smaller orbit. Thus it is closed and proper,
   and lem-sfb-homogeneous-orbit-quotient-geometry identifies it with G/B₀.
2. Apply lem-sfb-solvable-proper-fixed-point to any Borel acting on G/B₀.
   The homogeneous quotient description gives conjugacy to B₀, hence properness
   for every Borel and exactly the faithfully flat right torsor kernel pair.
3. Choose a torus of maximum dimension and then a smooth connected solvable
   subgroup of maximum dimension containing it. Strict dimension growth gives
   maximality; algebraic closedness makes the torus split.
4. For a given pair, the commutator series gives a solvable normal series.
   Apply lem-sfb-perfect-solvable-unipotent-torus to B. Its maximal unipotent
   kernel is Rᵤ(B). By lem-sfb-solvable-torus-complements the restriction of
   B → B/Rᵤ(B) to T is an isomorphism.
5. Compose the quotient with that restriction's inverse to define p. Then
   p restricts to the identity and has kernel U. Multiplication U × T → B
   has inverse b ↦ (b p(b)⁻¹, p(b)); normality supplies the semidirect law.
6. In split coordinates the group-like basis lemma
   lem-sfb-group-algebra-group-like-basis identifies characters and cocharacters
   with integer exponent vectors. Composition is their perfect dot product.
   Apply lem-sfb-reductive-rank-one-reflections for the finite nonzero Lie weights,
   coroots, their pairing 2 and reflection formulas. Reducedness excludes every
   rational multiple other than the two signs. Central torus directions remain.
7. If two coroots agree, iterating their two reflections gives
   α + 2n(β - α) in the finite root set, so torsion freeness gives α = β.
   Normalizer equivariance and duality identify simultaneous coroot reflections.
8. By lem-sfb-regular-cocharacter-borel-description the given B is P(λ) for
   an integral regular cocharacter. Its Lie weights are exactly the positive
   weights. Apply lem-sfb-crystallographic-positive-base to the roots not
   decomposable into two positive roots to obtain integral independence.
9. Induct on the positive integer pairing with λ to express every positive
   root as a nonnegative integral sum of these simple roots. Negative roots
   are their negatives. Independence gives uniqueness and rational independence;
   for an empty root family the base is empty. This supplies the stated Base.
The characteristic is unrestricted: all weights are characters on tangent vectors,
not differentials of characters.
The coroot reflection is the actual normalizer action supplied by
lem-sfb-reductive-rank-one-reflections (Milne, Theorem 21.11(d)--(e)); its displayed
conjugation formula specifies that action on every algebra. -/
theorem reductive_borel_pair_structure_with_geometric_coroots {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : ReductiveTorusCentralizer.IsReductive G) :
    (∃ (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G),
      ReductiveTorusCentralizer.IsMaximalTorus iT ∧
      (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) ∧
      IsBorelGroupScheme iB.hom.hom ∧ ∃ j : T ⟶ B, j ≫ iB = iT) ∧
    ∀ (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G),
      ReductiveTorusCentralizer.IsMaximalTorus iT →
      (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) →
      IsBorelGroupScheme iB.hom.hom → ∀ j : T ⟶ B, j ≫ iB = iT →
      (∃ (Q : Over (Spec (.of F))) (π : G.X ⟶ Q),
        IsProper Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
        Flat π.left ∧ Surjective π.left ∧
        (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π ∧
        IsPullback (fst G.X B.X)
          (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π) ∧
      (∃ (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B) (p : B ⟶ T),
        IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
        Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
        (∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
          IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
          Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
          ∃ f : N ⟶ U, f ≫ iU = iN) ∧
        j ≫ p = 𝟙 T ∧
        IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X] ∧
        IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom))) ∧
      ∃ (_ : IsCommMonObj T.X) (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
        (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
        (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
        (P : RootDatum Φ
          (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
        (b : P.Base),
        Module.Finite ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
        Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)) ∧
        P.IsReduced ∧
        aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X ∧
        aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ CategoryTheory.GrpObj.conj B.X ∧
        (∀ α : Φ, P.root α = α.val) ∧
        (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
          ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
            (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν)) ∧
        (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥) ∧
        (∀ α : Φ,
          b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥) ∧
        ∀ α : Φ,
          ∃ (n : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) (s : T ≅ T),
            (∀ (A : CommAlgCat.{u} F) (t : StandardGroupSchemes.affine F A ⟶ T.X),
              t ≫ s.hom.hom.hom ≫ iT.hom.hom =
                (toUnit (StandardGroupSchemes.affine F A) ≫ n) * (t ≫ iT.hom.hom) *
                  (toUnit (StandardGroupSchemes.affine F A) ≫ n)⁻¹) ∧
            ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
              Additive.ofMul (s.hom ≫ χ.toMul) =
                χ - (P.toLinearMap χ (P.coroot α)) • α.val := by
  sorry

end AlgebraicGeometry
