/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.TorusCharacterTangentWeights
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-! # Split Borel pairs, root data, and proper flag quotients

Source: Milne, Algebraic Groups (2017), Definition 17.6, Theorems 17.9 and 16.33(d),
Definition 19.22, Theorem 21.11, Corollary 21.12, Sections 21.29--21.35 and 18c.
(blueprint: lem-sfb-reductive-borel-pair-structure)

The character and cocharacter lattices are the actual group-scheme Hom groups,
written additively. The pairing is pinned by composition with the integer power map.
The conjugation actions used for weights are pinned by their actual morphisms.
No spanning hypothesis on the roots is imposed: central torus directions and the
empty root system are included. The two existential commutativity witnesses expose
the commutative group structures on these Hom groups; they are conclusions.
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
not differentials of characters. -/
theorem reductive_borel_pair_structure {F : Type u} [Field F] [IsAlgClosed F]
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
          b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥) := by
  sorry

/-- Semisimple groups are reductive, with semisimplicity defined by the absence of
nontrivial smooth connected solvable normal closed subgroup schemes.
Source: Milne, Sections 19a--19b and Proposition 14.21, pp.284--285.
(blueprint: lem-sfb-reductive-borel-pair-structure)

Proof plan (step 10): a smooth connected normal unipotent subgroup has a finite
subnormal series with commutative quotients, by lem-sfb-smooth-unipotent-solvable.
The derived subgroup of each term is contained in the next term, so induction
places its ith derived subgroup in the ith term. Its commutator series therefore
terminates. Semisimplicity makes this solvable normal subgroup trivial. Smoothness,
connectedness, affineness and finite type are already part of semisimplicity.
Over the algebraically closed base this is also the recorded geometric reductivity
predicate, since scalar extension to its algebraic closure is an equivalence. -/
theorem semisimpleGroupScheme_isReductive {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X) :
    ReductiveTorusCentralizer.IsReductive G := by
  sorry

end AlgebraicGeometry
