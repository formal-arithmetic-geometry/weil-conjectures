/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.SeparablyGeneratedSeparable
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced

/-!
# Epp solutions for essentially finite type traits

Source: Stacks Project, More on Algebra, Tags 09II and 0GLR; Algebra, Tag 030U
(blueprint: lem-sfb-epp-essentially-finite-type-traits).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z t

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The reduced generic tensor algebra, quotienting by every nilpotent element.
Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: lem-sfb-epp-essentially-finite-type-traits). -/
abbrev eppReducedTensor (F : Type v) (H : Type x) (M : Type y)
    [Field F] [Field H] [Field M] [Algebra F H] [Algebra F M] :=
  (H ⊗[F] M) ⧸ nilradical (H ⊗[F] M)

/-- The actual integral closure of T in the reduced generic tensor algebra.
Source: Stacks Project, More on Algebra, Tags 09EM and 09II
(blueprint: lem-sfb-epp-essentially-finite-type-traits). -/
abbrev eppUpperClosure (T : Type w) (F : Type v) (H : Type x) (M : Type y)
    [CommRing T] [Field F] [Field H] [Field M]
    [Algebra T H] [Algebra F H] [Algebra F M] :=
  integralClosure T (eppReducedTensor F H M)

/-- The canonical map between the lower and upper normalizations. It is the
restriction of m ↦ 1 tensor m followed by reduction: monic equations over D
remain monic equations over T.
Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: lem-sfb-epp-essentially-finite-type-traits). -/
noncomputable def eppNormalizationMap
    (D : Type u) (T : Type w) (F : Type v) (H : Type x) (M : Type y)
    [CommRing D] [CommRing T] [Field F] [Field H] [Field M]
    [Algebra D T] [Algebra D F] [Algebra D H] [Algebra T H] [Algebra F H]
    [IsScalarTower D T H] [IsScalarTower D F H]
    [Algebra F M] [Algebra D M] [IsScalarTower D F M] :
    integralClosure D M →+* eppUpperClosure T F H M :=
  (((Ideal.Quotient.mkₐ F (nilradical (H ⊗[F] M))).comp
    Algebra.TensorProduct.includeRight).restrictScalars D |>.comp
      (integralClosure D M).val).codRestrict
        ((integralClosure T (eppReducedTensor F H M)).restrictScalars D)
        (fun a ↦ (a.property.map
          (((Ideal.Quotient.mkₐ F (nilradical (H ⊗[F] M))).comp
            Algebra.TensorProduct.includeRight).restrictScalars D)).tower_top) |>.toRingHom

/-- Reducedness after every extension of the lower residue field, for the
canonical residue-field homomorphism induced by contraction. For maximal n,
n.ResidueField is canonically R/n; q.ResidueField is B_q/qB_q.
Source: Stacks Project, Algebra, Tag 030U; More on Algebra, Tag 09E7
(blueprint: lem-sfb-epp-essentially-finite-type-traits). -/
def eppResidueBaseChangeReduced
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (f : R →+* B) (n : Ideal R) [n.IsPrime] (q : Ideal B) [q.IsPrime]
    (hn : n = q.comap f) : Prop :=
  letI := (Ideal.ResidueField.map n q f hn).toAlgebra
  ∀ (Ω : Type (max u v z)) [Field Ω] [Algebra n.ResidueField Ω],
    IsReduced (q.ResidueField ⊗[n.ResidueField] Ω)

/-- Epp's finite extension for an essentially finite type local extension of
traits with complete lower trait, stable under every further finite extension.

Source: Stacks Project, More on Algebra, Tag 09II (existence), Tag 0GLR
(stability), Tag 09EM (normalizations), Tag 09E7 (residue separability), and
Algebra, Tag 030U (reduced residue tensors)
(blueprint: lem-sfb-epp-essentially-finite-type-traits).

Proof:
1. Call a finite extension strong if every normalized local pair has equal
   extended maximal ideals and separable residue extension (in the possibly
   transcendental sense of def-weil-pbc-separable-field-extension).
   By lem-sfb-dvr-algebraic-normalization-structure, case (b), essential finite
   type gives finitely many upper branches, local DVRs, maximal contractions
   and finitely generated residue extensions whenever the lower normalization
   is Noetherian. The presentation is essential finite type, not finite type of T.
2. In residue characteristic zero, lem-sfb-epp-weak-perfect-residue gives a
   weak solution. Lower residues remain characteristic zero by case (a) of
   the structure lemma; upper residues are finitely generated by case (b).
   Apply lem-weil-pbc-perfect-field-separating-basis and
   lem-weil-pbc-separably-generated-separable to make this a strong solution.
3. In positive residue characteristic, use
   lem-sfb-dvr-perfect-residue-algebraic-tower to obtain an algebraic extension
   P/F whose lower normalization is a DVR with perfect residue. Apply the
   structure lemma to its upper normalization and
   lem-sfb-epp-weak-perfect-residue to each of the finitely many local branches.
   Each weak solution is strong: lem-per-algebraic-extension-perfect preserves
   perfectness of lower residues; the structure lemma gives finite generation
   of upper residues; the separating-basis and separably-generated lemmas
   then give separability. This use of weak Epp needs no essential finite type
   over the new lower DVR.
4. Embed the finitely many solutions in a common field using
   lem-weil-common-extension-fields and take their compositum P1/P, finite by
   lem-weil-pbc-compositum-degree-bound and products of finite spanning sets.
   Apply lem-sfb-dvr-index-one-separable-base-change on each branch.
   Reduced tensor associativity, lem-weil-pbc-integral-transitive and
   lem-weil-pbc-integral-closure-commutes-localization identify its normalized
   local pairs with the branches over P1; they are strong.
5. The finite case of the structure lemma applied over the perfect-residue
   DVR makes the lower normalization in P1 Noetherian with finitely many
   maximal ideals. Its algebraic case for D to T gives the upper conditions.
   Localizing identifies the local pairs with those of step 4. Apply
   lem-sfb-dvr-normalized-finite-stage-descent to descend a strong solution
   to a finite F1/F. In characteristic zero use the solution of step 2.
6. For every further finite M/F1, including inseparable extensions, contract
   a normalized M-branch to F1 and apply
   lem-sfb-dvr-index-one-separable-base-change. The structure lemma gives the
   local DVRs and maximal contractions. The reduced tensor, integral
   transitivity and localization identifications of step 4 give exactly the
   chosen M-branch. Its maximal ideals agree and its residue extension is separable.
7. The structure lemma makes the residue extension finitely generated.
   Clause (2) of def-weil-pbc-separable-field-extension makes the whole residue
   extension separably generated. For every field Omega over the lower residue,
   lem-weil-pbc-separably-generated-tensor-reduced gives the final reduced tensor.
-/
theorem exists_epp_essentially_finite_type_traits
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (F : Type v) [Field F] [Algebra D F] [IsFractionRing D F]
    (T : Type w) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra D T] [IsLocalHom (algebraMap D T)]
    (hinj : Function.Injective (algebraMap D T))
    (H : Type x) [Field H] [Algebra T H] [IsFractionRing T H]
    [Algebra D H] [Algebra F H] [IsScalarTower D T H] [IsScalarTower D F H]
    (hfinite : ∃ (A : Type (max u w)) (_ : CommRing A) (_ : Algebra D A)
      (p : Ideal A) (_ : p.IsPrime),
      RingHom.FiniteType (algebraMap D A) ∧ Nonempty (T ≃ₐ[D] Localization.AtPrime p)) :
    ∃ (F₁ : Type (max u v w x)) (_ : Field F₁) (_ : Algebra F F₁),
      Module.Finite F F₁ ∧
      ∀ (M : Type (max u v w x y)) [Field M] [Algebra F₁ M] [Module.Finite F₁ M]
        [Algebra F M] [IsScalarTower F F₁ M]
        [Algebra D M] [IsScalarTower D F M]
        (q : Ideal (eppUpperClosure T F H M)) [q.IsMaximal],
        (q.comap (eppNormalizationMap D T F H M)).IsMaximal ∧
        (∃ hdom : IsDomain (Localization.AtPrime q),
          @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
        Ideal.map ((algebraMap (eppUpperClosure T F H M) (Localization.AtPrime q)).comp
          (eppNormalizationMap D T F H M))
          (q.comap (eppNormalizationMap D T F H M)) =
            Ideal.map (algebraMap (eppUpperClosure T F H M) (Localization.AtPrime q)) q ∧
        eppResidueBaseChangeReduced.{_, _, max u v w x y z}
          (eppNormalizationMap D T F H M)
          (q.comap (eppNormalizationMap D T F H M)) q rfl := by
  sorry

end IsDiscreteValuationRing
