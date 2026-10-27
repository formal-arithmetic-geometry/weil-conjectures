/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.FiniteClopenExceptionalRestriction

import Sheaf.Paper.ClopenExceptionalActionTransport
import Sheaf.CategoryTheory.ScalarLocalizationComponentIso
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # One exceptional system for all members of a finite clopen partition

Source: blueprint section-invariant, finite-clopen exceptional restriction, Step 3.
(blueprint: lem-pur-finite-clopen-common-exceptional).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

private theorem rationalSupport_additive
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (hl : IsUnit (P.coefficients.l : P.field.k)) (c : Compactification g) :
    (sfCompactSupportFiniteFunctor P.coefficients.l P.field.k hl c E).Additive := by
  exact ⟨fun {K L f h} ↦
    (sfCompactSupportFiniteHomMap P.coefficients.l P.field.k hl c E K L).map_add f h⟩

private theorem coefficient_rebase
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalCoefficientComparison P E X Y X g c (𝟙 X))
    (S : ClopenExceptionalCoefficientComparison P E X Y Xi g c j) :
    ∃ T : ClopenExceptionalCoefficientComparison P E X Y Xi g c j,
      T.integral = R.integral ∧ T.rational = R.rational := by
  classical
  let e : R.integral ≅ S.integral :=
    R.integralAdjunction.rightAdjointUniq S.integralAdjunction
  have : (sfCompactSupportFiniteFunctor P.coefficients.l P.field.k R.baseUnit c E).Additive :=
    rationalSupport_additive P X Y g E R.baseUnit c
  have : R.rational.Additive := R.rationalAdjunction.right_adjoint_additive
  have : S.rational.Additive := S.rationalAdjunction.right_adjoint_additive
  obtain ⟨q, hq, _⟩ := ScalarLocalization.existsUnique_iso_of_component_formulas
    (Padic.coefficientExtensionUniformizer P.coefficients.l E)
    (Padic.coefficientExtensionUniformizer P.coefficients.l E) id
    R.integral S.integral e R.rational S.rational
    R.coherence.2.2.2.1 S.coherence.2.2.2.1
    R.coherence.2.2.2.2.2.1 S.coherence.2.2.2.2.2.1
  let F := (sfIntegralConstructible P.coefficients.l E X.left).ι
  let Fi := (sfIntegralConstructible P.coefficients.l E Xi.left).ι
  let r := clopenIntegralRestriction P E j
  let rq := clopenRationalRestriction P E j
  let Qi := sfRationalConstructibleLocalization P.coefficients.l E Xi.left
  let D : ClopenExceptionalCoefficientComparisonData P E X Y Xi g c j := {
    S.toClopenExceptionalCoefficientComparisonData with
    integral := R.integral
    integralAdjunction := R.integralAdjunction
    integralFormula := isoWhiskerRight e F ≪≫ S.integralFormula
    limitRestriction := isoWhiskerRight (isoWhiskerRight e r) Fi ≪≫ S.limitRestriction
    integralComparison := isoWhiskerRight e r ≪≫ S.integralComparison
    rational := R.rational
    rationalAdjunction := R.rationalAdjunction
    rationalComparison := isoWhiskerRight q rq ≪≫ S.rationalComparison }
  have hlimit (L : sfIntegralConstructibleCategory P.coefficients.l E Y.left) :
      Fi.map (D.integralComparison.hom.app L) =
        D.limitRestriction.hom.app L ≫
          (coefficientSequenceLimit.{u, u} P.coefficients.l E Xi.left).map
            (D.system.hom.app L) ≫ D.integralFormulaI.inv.app L := by
    dsimp [D]
    rw [Fi.map_comp, S.coherence.2.2.1 L]
    simp only [Category.assoc]
  have hrq (L : sfIntegralConstructibleCategory P.coefficients.l E Y.left) :
      HEq (rq.map (q.hom.app
        ((sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L)))
        (Qi.map (r.map (e.hom.app L))) := by
    let K := (sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L
    have he := (conj_eqToHom_iff_heq _ _
      (R.coherence.2.2.2.1 K) (S.coherence.2.2.2.1 K)).mpr (hq K)
    rw [he, rq.map_comp, rq.map_comp, eqToHom_map, eqToHom_map]
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    let : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
      fun x ↦ (P.clopenResidue_isUnit X x).invertible
    let : ∀ x : Xi.left, Invertible (P.coefficients.l : Xi.left.residueField x) :=
      fun x ↦ (P.clopenResidue_isUnit Xi x).invertible
    exact (rationalDerivedPullback_existsUnique P.coefficients.l E j.left).exists.choose_spec
      |>.2.2 _ _ (e.hom.app L) 1
  have hrat (L : sfIntegralConstructibleCategory P.coefficients.l E Y.left) :
      HEq (D.rationalComparison.hom.app
        ((sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L))
        (Qi.map (D.integralComparison.hom.app L)) := by
    dsimp [D]
    rw [Qi.map_comp]
    let : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
      fun x ↦ (P.clopenResidue_isUnit X x).invertible
    let : ∀ x : Xi.left, Invertible (P.coefficients.l : Xi.left.residueField x) :=
      fun x ↦ (P.clopenResidue_isUnit Xi x).invertible
    have ho := (rationalDerivedPullback_existsUnique P.coefficients.l E j.left)
      |>.exists.choose_spec.2.1
    have hsource : rq.obj (R.rational.obj
        ((sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L)) =
        Qi.obj (r.obj (R.integral.obj L)) :=
      (congrArg rq.obj (R.coherence.2.2.2.1 _)).trans (ho _)
    have hmiddle : rq.obj (S.rational.obj
        ((sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L)) =
        Qi.obj (r.obj (S.integral.obj L)) :=
      (congrArg rq.obj (S.coherence.2.2.2.1 _)).trans (ho _)
    exact heq_comp hsource hmiddle (S.coherence.2.2.2.2.1 _) (hrq L)
      (S.coherence.2.2.2.2.2.2.2 L)
  refine ⟨{ toClopenExceptionalCoefficientComparisonData := D, coherence := ?_ }, rfl, rfl⟩
  exact ⟨S.coherence.1, S.coherence.2.1, hlimit, R.coherence.2.2.2.1,
    S.coherence.2.2.2.2.1, R.coherence.2.2.2.2.2.1, S.coherence.2.2.2.2.2.2.1, hrat⟩

/-- The component comparisons can share one global exceptional system. This asserts
neither smoothness nor invertibility and includes the empty partition.

Source: blueprint section-invariant, Step 3 of the finite-clopen inverse assembly;
finite-clopen exceptional restriction, construction of the strict adjoint square.
(blueprint: lem-pur-finite-clopen-common-exceptional).

Proof: first fix the compactification c and its global strict compact-support system.
Choose its exceptional right adjoint once, with its finite evaluation comparisons.
For each clopen inclusion, form the component compactification by precomposition.
Extension by zero identifies the sum of component supports with the global support.
Transpose the coordinate-insertion maps through these adjunctions. The resulting
strict restriction squares use the same global system and adjoint for every i.
Apply the normalized site realization and the same restriction-of-scalars/derived
limit to that global system, once. Use these functors as the global fields of every
component comparison. The identity inclusion gives R. Rationalize these same
functors and extend their maps linearly. At every finite coefficient field make
the same common choice, and use the counit mates of the fixed support scalar action
for the coefficient transitions. Their identity and composition equations follow
from mate pasting. Thus the resulting common-stage action is shared as well.
The component square, its evaluations and its limit map satisfy the coherence
fields by the same transposition and limit formulas as finite-clopen exceptional
restriction. The three equalities are reflexive for these simultaneous choices.
For an empty family only the identity comparison is required, and the construction
of the global exceptional system still applies. No arbitrary levelwise maps are
lifted, and no tensor inverse or relative-dimension assertion is used. -/
theorem finiteClopen_common_exceptional
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (.of P.field.k)))
    [∀ i, LocallyOfFiniteType ((Xi i).left ↘ Spec (.of P.field.k))]
    [∀ i, QuasiCompact ((Xi i).left ↘ Spec (.of P.field.k))]
    (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (c : Compactification g) :
    ∃ R : ClopenExceptionalAllCoefficients P X Y X g c (𝟙 X),
      ∃ Ri : ∀ i, ClopenExceptionalAllCoefficients P X Y (Xi i) g c (j i),
        ∀ i, (Ri i).base.integral = R.base.integral ∧
          (Ri i).base.rational = R.base.rational ∧
          (Ri i).action.functor = R.action.functor := by
  classical
  have hid : (⋃ _ : Unit, Set.range (𝟙 X : X ⟶ X).left) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), x, rfl⟩
  obtain ⟨R⟩ := (finiteClopenExceptionalRestriction P X Y g (fun _ : Unit ↦ X)
    (fun _ ↦ 𝟙 X) (fun i k h ↦ False.elim (h (Subsingleton.elim i k))) hid).2 c ()
  have hs := (finiteClopenExceptionalRestriction P X Y g Xi j hdisjoint hcover).2 c
  let S (i : I) := (hs i).some
  have ht (i : I) := clopenExceptional_action_transport P X Y g (Xi i) c (j i) R (S i)
  choose T hbase haction using ht
  have hb (i : I) := coefficient_rebase P X Y g P.extension (Xi i) c (j i)
    R.base (T i).base
  choose B hintegral hrational using hb
  let U (i : I) : ClopenExceptionalAllCoefficients P X Y (Xi i) g c (j i) :=
    { T i with base := B i }
  exact ⟨R, U, fun i ↦ ⟨hintegral i, hrational i, haction i⟩⟩

end WeilConjectures.PurityFiniteSetting
