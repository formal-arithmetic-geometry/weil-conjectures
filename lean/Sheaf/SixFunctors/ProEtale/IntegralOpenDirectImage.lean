/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.IntegralModels
import Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion
import Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits
import Sheaf.SixFunctors.FiniteOpenDirectImageCtf

/-!
# Integral open direct image preserves constructibility

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic,
`sk-thm-sf-pf-adic-open.md` and its proof; Stacks Tags 099L, 09A6 and 09C1
(blueprint: det-thm-sf-pf-adic-open).

The residue comparison is specified by its adjunction equation, rather than by an
unconstrained isomorphism of objects. The coefficient-change pullback square used in that
equation is defined for the nonflat residue quotient. All derived categories below are
ordinary derived categories of internal modules over the continuous condensed coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralOpenDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- The canonical pullback/reduction transformation, obtained by transposing the inverse
of the exact restriction-of-scalars pullback square along the two derived scalar
adjunctions. No flatness of O_E -> F_E is assumed.
Source: blueprint open-direct-image proof, Reduction paragraph and the coefficient square
(blueprint: det-thm-sf-pf-adic-open). -/
def reductionPullbackMap :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
        AdicCompletion.derivedReduction l E U 0 ⟶
      AdicCompletion.derivedReduction l E X 0 ⋙
        (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X 0))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U 0))).symm
      (TwoSquare.mk _ _ _ _
        (CondensedRing.derivedComapUpperStarIso (DerivedNakayama.reductionRing l E 1) j).inv)
    ).natTrans

private theorem unique_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (R : C ⥤ C') (S : D ⥤ D')
    (χ : F ⋙ S ⟶ R ⋙ F') [IsIso χ] (K : D)
    (hc : IsIso ((adj'.homEquiv _ _)
      (inv (χ.app (G.obj K)) ≫ S.map (adj.counit.app K)))) :
    ∃! c : R.obj (G.obj K) ⟶ G'.obj (S.obj K),
      IsIso c ∧ χ.app (G.obj K) ≫ F'.map c ≫ adj'.counit.app (S.obj K) =
        S.map (adj.counit.app K) := by
  let a := inv (χ.app (G.obj K)) ≫ S.map (adj.counit.app K)
  let c := (adj'.homEquiv _ _) a
  have he : F'.map c ≫ adj'.counit.app (S.obj K) = a := by
    exact (adj'.homEquiv _ _).symm_apply_apply a
  refine ⟨c, ⟨hc, ?_⟩, ?_⟩
  · rw [he]
    simp only [a, IsIso.hom_inv_id_assoc]
  · intro b hb
    apply (adj'.homEquiv _ _).symm.injective
    change F'.map b ≫ adj'.counit.app (S.obj K) =
      F'.map c ≫ adj'.counit.app (S.obj K)
    apply (cancel_epi (χ.app (G.obj K))).1
    rw [hb.2, he]
    simp only [a, IsIso.hom_inv_id_assoc]

private theorem residue_killed : (l : Padic.coefficientExtensionRing l E 1) = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (l : Padic.coefficientExtensionIntegers l E) ∈
    Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
  rw [pow_one, hgen]
  apply (h.2.1 _).2
  have he := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
  change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
  rw [show (l : E) = algebraMap (Padic l) E (l : Padic l) by simp]
  change spectralNorm (Padic l) E (algebraMap (Padic l) E (l : Padic l)) < 1
  rw [he]
  exact Padic.norm_p_lt_one

private theorem residue_discrete :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E 1) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let I := Padic.coefficientExtensionIdeal l E 1
  apply QuotientAddGroup.discreteTopology (N := I.toAddSubgroup)
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hi : I = Padic.coefficientExtensionMaximalIdeal l E := by
    change Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1 = _
    rw [pow_one, hgen]
  have hs : (I.toAddSubgroup : Set (Padic.coefficientExtensionIntegers l E)) =
      {x : Padic.coefficientExtensionIntegers l E | ‖(x : E)‖ < 1} := by
    ext x
    change x ∈ I ↔ ‖(x : E)‖ < 1
    rw [hi]
    exact h.2.1 x
  rw [hs]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

private theorem residue_open_image
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.quotientRing l E 1) U)))
    (hK : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) U K)
    (hTor : DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E 1) j).obj K) ∧
    DerivedCategory.finiteTorAmplitude _
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E 1) j).obj K) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 le_rfl
  have := residue_discrete l E
  obtain ⟨a, b, ht⟩ := hTor
  have ht' := ht.mono (min_le_left a b) (le_max_left b a)
  have hp : 0 < ringChar k := (Fact.out : (ringChar k).Prime).pos
  have hne : ringChar k ≠ l := Fact.out
  obtain ⟨d, _, hd⟩ := CondensedRing.finiteOpenDirectImage_constantModel_torAmplitude
    l (ringChar k) k hp hne (Padic.coefficientExtensionRing l E 1)
    ⟨1, le_rfl, by simpa only [pow_one] using residue_killed l E⟩ j
  obtain ⟨hbc, hta⟩ := hd (min a b) (max b a) (by omega) K hK ht'
  exact ⟨hbc, min a b, max b a + d, hta⟩

set_option maxHeartbeats 800000 in
-- Normalize the two scalar adjunctions and the internal coefficient module categories.
/-- Integral open direct image is derived complete, commutes canonically with residue
reduction, and is bounded constructible; integral Dbc equals its finite-Tor subcategory.
The unique comparison is characterized by the usual pullback/reduction square and the
two geometric counits. This is the canonical coefficient-change (projection-formula) map.
Source: blueprint main-20261015, `sk-thm-sf-pf-adic-open.md` and its proof; Stacks
Tags 099L, 09A6, 09C1 (blueprint: det-thm-sf-pf-adic-open).

Proof:
1. Apply sk-lem-integral-models on U: K is complete and its residue reduction is bounded
   constructible of etale origin. The extension-integers DVR theorem gives a finite residue
   field of characteristic l, which is invertible in k.
2. det-pe-derived-nakayama-resolution identifies reduction with the uniformizer cone.
   The right derived module pushforward is triangulated and O_E-linear. The canonical
   finite-projection clause of prop-weil-pbc-direct-image-limits, with the finite perfect
   quotients of lem-weil-pbc-standard-quotients-perfect, identifies the residue comparison
   and all tower transitions. Its adjunction equation is the one displayed below.
3. Apply the direct-image/derived-limit comparison to K's reduction tower. The completion
   unit compatibility in that same node identifies the composite with the completion unit
   of Rj_*K, proving completeness (sk-def-pe-derived-completion).
4. Descend the residue reduction to the etale site by sk-thm-pe-constructible-comparison.
   cor-fin-deligne-open-finite-coefficients makes its etale open direct image bounded
   constructible, since the residue field is finite and killed by l.
5. An open immersion has identity diagonal, so quasi-compactness makes j qcqs.
6. prop-weil-pbc-comparison-direct-image identifies the residue pro-etale direct image
   with the pullback of the etale one; constructible comparison preserves its finiteness.
7. sk-prop-sfb-cartesian-coefficients and sk-def-sfb-coefficient-change give the compatible
   integral/residue ring square. lem-weil-pbc-ring-sheaf-change-adjunction compares the
   direct images after restriction, without imposing flatness on the residue quotient.
8. Exact scalar restriction (lem-weil-restriction-of-scalars-exact) identifies cohomology
   of these two residue complexes as integral modules.
9. The coefficient resolution makes O_E -> F_E an epimorphism. Lift residue scalars
   locally to integral scalars; integral linearity then gives residue linearity of the
   cohomology isomorphisms and their inverses. The actual reduction is bounded constructible.
10. Constructible comparison gives etale origin for that actual residue reduction.
11. Apply the residue criterion sk-lem-integral-models on X. It gives bounded
    constructibility and the equality of integral bounded constructible and finite-Tor
    subcategories. This proves all clauses, including the empty-open and identity cases. -/
theorem integral_open_direct_image
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K) :
    IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      (∃! c :
          (AdicCompletion.derivedReduction l E X 0).obj
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ⟶
            (CondensedRing.moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) j).obj
                ((AdicCompletion.derivedReduction l E U 0).obj K),
        IsIso c ∧
          (reductionPullbackMap l E j).app
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ≫
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory.map
              c ≫
            ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
                  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                    (DerivedNakayama.quotientRing l E 1) j)).counit.app
              ((AdicCompletion.derivedReduction l E U 0).obj K) =
            (AdicCompletion.derivedReduction l E U 0).map
              (((CondensedRing.derivedUpperStarLowerStarAdjunction
                  (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                      (DerivedNakayama.integerRing l E) j)).counit.app K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
        (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
          DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian
    (U ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace
    (U ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let : IsNoetherian U := ⟨⟩
  let : IsNoetherian X := ⟨⟩
  obtain ⟨hχ, hpush⟩ := internal_integral_direct_image_limits l E j
  change IsIso (reductionPullbackMap l E j) at hχ
  let := hχ
  let adj := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.integerRing l E) j)
  let adj' := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.quotientRing l E 1) j)
  obtain ⟨hcomplete, hmate⟩ := hpush K
  obtain ⟨hinput, _⟩ := internal_integral_residue_criterion l E U
  obtain ⟨houtput, htor'⟩ := internal_integral_residue_criterion l E X
  obtain ⟨hcK, hrK, htK⟩ := (hinput K).mp hK
  have hcomplete' := hcomplete hcK
  obtain ⟨c, hc, hunique⟩ := unique_mate adj adj'
    (AdicCompletion.derivedReduction l E X 0)
    (AdicCompletion.derivedReduction l E U 0) (reductionPullbackMap l E j) K hmate
  refine ⟨hcomplete', ⟨c, hc, hunique⟩, ?_, htor'⟩
  have hfinite := residue_open_image l E j k
    ((AdicCompletion.derivedReduction l E U 0).obj K) hrK htK
  have := hc.1
  have e := asIso c
  have hclosed := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.quotientRing l E 1) X).2.1
  let := hclosed
  exact (houtput _).mpr ⟨hcomplete',
    (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X).prop_of_iso
      e.symm hfinite.1,
    (DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hfinite.2⟩

end AlgebraicGeometry.ProEtale.IntegralOpenDirectImage
