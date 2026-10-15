/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.SmoothCurvePointsDecomposition
import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.Paper.FiniteCoproductCohomologyAssembly

/-!
# Betti cardinalities of smooth projective curve families

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1610
(blueprint: lem-fin-projective-curve-betti-cardinalities).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Betti cardinalities and their constructibility in a smooth projective curve family.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1610
(blueprint: lem-fin-projective-curve-betti-cardinalities).

The function `b r s` names the cardinality in degree `r`. Equality with `Cardinal.mk`
asserts actual finiteness, including for the empty fibre. The component count is
`Nat.card (ConnectedComponents _)`. On a disconnected smooth proper curve, `genus`
is the dimension of global differential forms, hence the sum of the component genera.
Constructibility is written as finite range and constructible level sets.

Proof plan from the node:
1. Projectivity implies properness (lem-pc-projective-proper). Base change preserves
   properness and smoothness (lem-pc-proper-base-change), giving smooth proper fibres.
2. Use lem-sbc-smooth-curve-points-decomposition. Purity excludes the point summands;
   the remaining connected clopen curves are proper by
   lem-weil-pbc-closed-immersion-proper. Empty fibres give an empty decomposition.
3. Resolve the structure module by injectives using
   lem-sc-ringed-space-module-sheaves-enough-injectives and restrict using
   lem-sc-ringed-space-restrict-injective-resolution. Sections over the finite clopen
   decomposition are products degreewise, so cohomology is the sum of the component
   cohomologies (def-sc-ringed-space-module-cohomology).
4. By lem-sc-global-functions and def-sc-genus, coherent h0 is the component count and
   coherent h1 is the sum of genera; finite sums include the empty sum.
5. Finite type over the Noetherian base makes X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). The rank-one structure module is coherent
   by pqf-lem-coherent-ft-locnoeth and flat over the base by lem-pc-smooth-flat.
6. Apply lem-fin-projective-flat-coherent-ranks to the structure module to obtain
   constructibility of the component count and sum of genera.
7. Choose a primitive root by lem-sc-primitive-root. Apply thm-sc-proper-cohomology to
   each connected proper component, giving ranks 1, 2g, 1 and zero above degree two.
8. Restrict coefficients via lemma-constructible-pullback-constant and assemble with
   lem-weil-pbc-finite-coproduct-cohomology-assembly. Taking cardinalities gives the
   displayed powers of the prime; the empty product has cardinality one.
9. Refine the finite constructible partitions for the component count and genus sum.
   The displayed powers are constant on every refined piece; above degree two the
   cardinality is constantly one (def-weil-constructible-subset). -/
theorem projective_curve_betti_cardinalities
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] [IsProjective f]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hinv : ∀ s : S, (ℓ : S.residueField s) ≠ 0) :
    ∃ b : ℕ → S → ℕ,
      (∀ (r : ℕ) (s : S),
        Cardinal.mk ((Etale.cohomology AddCommGrpCat.{u + 1}
          (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) (r : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)).constantZMod ℓ))) = b r s) ∧
      (∀ (r : ℕ) (s : S), b r s =
        if r = 0 ∨ r = 2 then ℓ ^ Nat.card (ConnectedComponents
          ↥(pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))
        else if r = 1 then ℓ ^ (2 * (pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)).genus)
        else 1) ∧
      ∀ r : ℕ, (Set.range (b r)).Finite ∧
        ∀ n : ℕ, Topology.IsConstructible {s : S | b r s = n} := by
  sorry

end AlgebraicGeometry
