module

public import Sheaf.RingTheory.EppWeakSolution
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! # A finite coefficient extension eliminating ramification in a DVR triple

Source: Stacks Project, More on Algebra, Tag 09F8 (lemma-special-case), with
Tags 09EM, 09EN and 09F9 for normalized branches, weak solutions and the
prescribed uniformizer-root compositum.
(blueprint: lem-sfb-epp-finite-coefficient-triple)
-/

@[expose] public section

set_option autoImplicit false

universe u v w f g j

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- Finite coefficient extension for a complete weakly unramified bottom pair
with algebraically closed lower residue equal to the perfect core of the upper
residue. In equal characteristic p it can be chosen with the prescribed
uniformizer-root compositum form. No persistence under further extensions is asserted.

Source: Stacks Project, More on Algebra, Tag 09F8 (lemma-special-case),
and Tag 09F9 (the compositum observation over k((t))).
(blueprint: lem-sfb-epp-finite-coefficient-triple)

Proof:
1. By lem-per-complete-dvr-finite-normalization, W is the complete integral
   closure of V in J. Use lem-sfb-epp-normal-ramification-filtration to embed
   J in a finite normal extension with a tower of four types; solutions descend
   by lem-sfb-epp-weak-solution-descent. Allow identity steps and separable
   residue extensions in the cyclic prime-to-p case to preserve the tower under base change.
2. Induct on tower length. The empty tower is solved by F itself since the
   original lower map has index one.
3. The uniformizer-root algebra from lem-sbc-dvr-uniformizer-root-algebra has
   the monic power basis of lem-weil-pbc-monic-quotient-free. It is integrally
   closed by lem-weil-pbc-pid-noetherian-normal, hence is the integral closure,
   with unchanged residue field, degree n and ramification index n. For p not
   dividing n, the derivative proves separability. Include n = 1.
4. An unramified step needs no extension. For a prime-to-p cyclic step of index
   e, adjoin t^(1/e). Apply lem-sfb-epp-totally-ramified-base-change to the
   bottom pair and lem-sfb-abhyankar-arbitrary-dvr-branches above it.
5. Apply lem-sfb-epp-purely-inseparable-degree-p. Its first and third alternatives
   give solutions. In its root alternative, adjoin t^(1/p); the reduced upper
   tensor is J and the two normalization uniformizers agree by step 3.
6. For a degree-p Galois step in equal characteristic, apply
   lem-sfb-epp-artin-schreier-degree-p, without requiring perfect upper residue.
7. In mixed characteristic use lem-sfb-epp-mixed-finite-level-preparation and
   lem-sfb-epp-mixed-level-lowering. The level lies in [0,p). Above p-1 its
   positive distance from p at least doubles; thereafter the level decreases
   by at least one until zero. Completeness and the residue hypotheses persist
   by finite normalization, totally ramified base change and
   lem-sfb-epp-complete-coefficient-field-arithmetic. Assemble the finitely many
   coefficient extensions by lem-sfb-epp-weak-solution-descent.
8. Solve the first step and enlarge the coefficient extension to a normal one
   separable over it using lem-sfb-epp-complete-coefficient-field-arithmetic.
   It is totally ramified and preserves the solved branches. The filtration
   lemma supplies a shorter tower over each new branch. By
   lem-per-finite-extension-perfect-core its residue perfect core is algebraic
   over k, hence equals k. Apply induction on a chosen branch.
9. Make the final coefficient field normal over F, separable over the constructed
   solution. Totally ramified base change and weak-solution descent preserve
   index one on a branch. By lem-sfb-epp-normal-base-branch-conjugacy all
   branches have the same index. Descent returns a weak solution for U -> W,
   including maximal contractions and the DVR assertions.
10. If char(F) = p, apply lem-sfb-epp-complete-coefficient-field-arithmetic to
    this same finite field and the specified uniformizer t. It is the compositum
    of its finite separable part and F[t^(1/p^r)]. The field and its weak-solution
    property do not change; arbitrary further extensions are not used.
-/
theorem exists_epp_finite_coefficient_triple
    (p : ℕ) (hp : p.Prime)
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    (V : Type v) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (W : Type w) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Algebra U V] [Algebra V W] [Algebra U W] [IsScalarTower U V W]
    [IsLocalHom (algebraMap U V)] [IsLocalHom (algebraMap V W)]
    (hinjUV : Function.Injective (algebraMap U V))
    (hinjVW : Function.Injective (algebraMap V W))
    (F : Type f) [Field F] [Algebra U F] [IsFractionRing U F]
    (G : Type g) [Field G] [Algebra V G] [IsFractionRing V G]
    (J : Type j) [Field J] [Algebra W J] [IsFractionRing W J]
    [Algebra F G] [Algebra G J] [Algebra F J] [IsScalarTower F G J]
    [Algebra U G] [IsScalarTower U V G] [IsScalarTower U F G]
    [Algebra V J] [IsScalarTower V W J] [IsScalarTower V G J]
    [Algebra U J] [IsScalarTower U V J] [IsScalarTower U W J]
    [IsScalarTower U F J]
    [IsAdicComplete (IsLocalRing.maximalIdeal U) U]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [IsAlgClosed (IsLocalRing.ResidueField U)] [CharP (IsLocalRing.ResidueField U) p]
    (hunram : Ideal.map (algebraMap U V) (IsLocalRing.maximalIdeal U) =
      IsLocalRing.maximalIdeal V)
    [Module.Finite G J]
    (hcore : Set.range (IsLocalRing.ResidueField.map (algebraMap U V)) =
      {x : IsLocalRing.ResidueField V | ∀ n : ℕ, ∃ y : IsLocalRing.ResidueField V,
        y ^ (p ^ n) = x}) :
    (∃ (H : Type (max u v w f g j)) (_ : Field H) (_ : Algebra F H)
        (_ : Algebra U H) (_ : IsScalarTower U F H),
      IsEppWeakSolution U W F J H) ∧
    (CharP F p → ∀ (t : U), Irreducible t →
      ∃ (H : Type (max u v w f g j)) (_ : Field H) (_ : Algebra F H)
          (_ : Algebra U H) (_ : IsScalarTower U F H),
        IsEppWeakSolution U W F J H ∧
        ∃ (S : IntermediateField F H), Module.Finite F S ∧ Algebra.IsSeparable F S ∧
          ∃ (r : ℕ) (a : H), a ^ (p ^ r) = algebraMap U H t ∧
            S ⊔ IntermediateField.adjoin F ({a} : Set H) = ⊤) := by
  sorry

end IsDiscreteValuationRing
