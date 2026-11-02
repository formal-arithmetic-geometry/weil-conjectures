/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Direct condensed point fibres and finite reduction

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/def-weil-finite-coefficient-point.md, the four equivalences;
sec-six-functors-basics/sk-prop-qlbar-two-colimit/det-def-sf-operations.md; and
sec-smooth-purity/sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.proof.md, Step 2
(blueprint: def-weil-point-fibre-stage-constructions).

The point equivalences below restrict the actual derived final-section evaluation and
its scalar realization. Their scalar target is the ordinary derived category of the
section ring, including at Qbar. The publicly imported six operations are the direct
operations on modules over `condensedRingObj Λ T = p_T^* Λ`: `moduleObjectDerivedPullback`,
`derivedTensor`, `derivedHom`, `moduleObjectDerivedPushforward`,
`rightDerivedLowerShriekOfCompactification`, and `ctfExceptionalInverseImage`.
The last operation is the finite-Tor restriction of the localizing Brown right adjoint,
not an assumed ambient right adjoint. No integral or rational operation is defined here
by reduction or by a category of coefficient representatives.

The finite part uses the existing intrinsic constant-ring coordinates of
`PurityFiniteSetting`, exactly as do the recorded root-chart and comparison nodes.
`finiteTorReduction` restricts their actual derived extension along the quotient
O_E/(pi^n) -> O_E/(pi^m). The five canonical comparisons are publicly reexported unchanged:
`finiteReductionPullbackComparison`, `finiteReductionSourceComparison`,
`finiteReductionCompactSupportComparison`, `finiteReductionExceptionalComparison`,
and `finiteReductionUnitComparison`. Their normalization and invertibility
on the stated domains are supplied by their owning dependency module. The naturality
statements below package these fixed components as natural isomorphisms; no commutativity
of purity, orientation, trace, composition or base-change squares is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

end AlgebraicGeometry.ProEtale.CondensedGeometricPoint

namespace WeilConjectures.PurityFiniteSetting

section Comparisons

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Naturality of the specified scalar-adjunction pullback mate on the finite-Tor domain.
Source: finite-reduction-of-purity, Step 2, and finite-reduction-comparisons, pullback clause
(blueprint: def-weil-point-fibre-stage-constructions).
Proof: the coefficient square is the square of actual quotient homomorphisms.
Taking its scalar-adjunction mate is natural in the input. Conjugating this mate by
`finiteReductionRawPullbackModel`, a natural isomorphism, retains that naturality. -/
theorem pointReductionPullback_naturality
    {K L : finiteTorConstructibleCategory P.coefficients.l P.extension
      P.level P.level_pos Y} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn X).map ((P.finiteReductionPullback f).map a.hom) ≫
        (P.finiteReductionPullbackComparison m hm hmn f L.obj).hom =
      (P.finiteReductionPullbackComparison m hm hmn f K.obj).hom ≫
        ((P.finiteReductionSetting m hm).finiteReductionPullback f).map
          ((P.finiteReduction m hm hmn Y).map a.hom) := by
  let e := Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel f).symm
      (P.finiteReduction m hm hmn X) ≪≫
    (Scheme.proEtaleReductionPullbackIso f
      (Scheme.proEtaleConstantRing Y P.Ring)
      (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing X P.Ring)
      (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison f P.Ring)
      (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn f)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)
  simpa only [e, finiteReductionPullbackComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom, Iso.app_inv,
    Functor.comp_map, Functor.mapIso_hom, Functor.mapIso_inv] using e.hom.naturality a.hom

/-- The natural pullback comparison has precisely the canonical mate as its components.
Source: finite-reduction-of-purity, Step 2
(blueprint: def-weil-point-fibre-stage-constructions). -/
def pointReductionPullbackIso :
    (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y).ι ⋙
        P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y).ι ⋙
        P.finiteReduction m hm hmn Y ⋙
          (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  NatIso.ofComponents (fun K ↦ P.finiteReductionPullbackComparison m hm hmn f K.obj)
    (fun a ↦ P.pointReductionPullback_naturality m hm hmn f a)

/-- Naturality of the comparison on Lf* K(d)[2d], with the same primitive-root charts.
Source: finite-reduction-of-purity, Step 2, finite-reduction-comparisons, twist clause
(blueprint: def-weil-point-fibre-stage-constructions).
Proof: choose compatible primitive roots. Both root charts are natural in K because
they use tensor, pullback, and the canonical shift transformation. Between these
charts the comparison is the pullback mate followed by its shift comparison, both
natural. Conjugate by the charts and use the unique root-chart characterization.
No purity map, orientation, trace or coherence square is used. -/
theorem pointReductionTwistShift_naturality (d : ℕ)
    {K L : finiteTorConstructibleCategory P.coefficients.l P.extension
      P.level P.level_pos Y} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn X).map ((P.compositionShiftedPullback f d).map a.hom) ≫
        (P.finiteReductionSourceComparison m hm hmn f d L.obj).hom =
      (P.finiteReductionSourceComparison m hm hmn f d K.obj).hom ≫
        ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
          ((P.finiteReduction m hm hmn Y).map a.hom) := by
  have hl : (P.coefficients.l : P.field.k) ≠ 0 := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨by
    change ((P.coefficients.l ^ P.level : ℕ) : P.field.k) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let η := ζ ^ (P.coefficients.l ^ (P.level - m))
  have hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent := by
    apply hζ.pow (NeZero.pos P.diagonalExponent)
    change P.coefficients.l ^ P.level =
      P.coefficients.l ^ (P.level - m) * P.coefficients.l ^ m
    rw [← pow_add, Nat.sub_add_cancel hmn]
  let Q := P.finiteReductionSetting m hm
  let r := 2 * (d : ℤ)
  let χP : P.compositionShiftedPullback f d ≅
      P.finiteReductionPullback f ⋙ shiftFunctor _ r :=
    NatIso.ofComponents (P.finiteReductionSourceTrivialization f d ζ hζ)
      (fun b ↦ sourceChart_naturality P f d ζ hζ b)
  let χQ : Q.compositionShiftedPullback f d ≅
      Q.finiteReductionPullback f ⋙ shiftFunctor _ r :=
    NatIso.ofComponents (Q.finiteReductionSourceTrivialization f d η hη)
      (fun b ↦ sourceChart_naturality Q f d η hη b)
  let ι := (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y).ι
  let e := Functor.isoWhiskerLeft ι
      (Functor.isoWhiskerRight χP (P.finiteReduction m hm hmn X)) ≪≫
    Functor.isoWhiskerLeft (ι ⋙ P.finiteReductionPullback f)
      ((P.finiteReduction m hm hmn X).commShiftIso r) ≪≫
    Functor.isoWhiskerRight (P.pointReductionPullbackIso m hm hmn f) (shiftFunctor _ r) ≪≫
    Functor.isoWhiskerLeft (ι ⋙ P.finiteReduction m hm hmn Y) χQ.symm
  have he (M : finiteTorConstructibleCategory P.coefficients.l P.extension
      P.level P.level_pos Y) :
      e.hom.app M = (P.finiteReductionSourceComparison m hm hmn f d M.obj).hom := by
    apply (cancel_mono (Q.finiteReductionSourceTrivialization f d η hη
      ((P.finiteReduction m hm hmn Y).obj M.obj)).hom).1
    change ((P.finiteReduction m hm hmn X).map
        (P.finiteReductionSourceTrivialization f d ζ hζ M.obj).hom ≫
      ((P.finiteReduction m hm hmn X).commShiftIso r).hom.app
        ((P.finiteReductionPullback f).obj M.obj) ≫
      ((P.finiteReductionPullbackComparison m hm hmn f M.obj).hom)⟦r⟧' ≫
      (Q.finiteReductionSourceTrivialization f d η hη
        ((P.finiteReduction m hm hmn Y).obj M.obj)).inv) ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ((P.existsUnique_finiteReductionSourceComparison m hm hmn f d
      M.obj).choose_spec.1 ζ η hζ hη rfl).symm
  simpa only [Functor.comp_map, he, ι, Q, ObjectProperty.ι_map,
    Functor.comp_obj, ObjectProperty.ι_obj] using e.hom.naturality a

/-- Naturality of the specified compact-support scalar adjunct on finite-Tor inputs.
Source: finite-reduction-of-purity, Step 2, finite-reduction-comparisons, support clause
(blueprint: def-weil-point-fibre-stage-constructions).
Proof: the scalar unit and the proper/open restriction comparison are natural.
Apply compact support to the scalar unit and compose with that comparison.
Naturality of the scalar-adjunction Hom bijection gives the displayed equation. -/
theorem pointReductionCompactSupport_naturality
    {K L : finiteTorConstructibleCategory P.coefficients.l P.extension
      P.level P.level_pos X} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn Y).map ((P.smoothCompactSupport f).map a.hom) ≫
        P.finiteReductionCompactSupportComparison m hm hmn f L.obj =
      P.finiteReductionCompactSupportComparison m hm hmn f K.obj ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a.hom) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let adjX := P.finiteReductionAdjunction m hm hmn X
  let adjY := P.finiteReductionAdjunction m hm hmn Y
  let c := Scheme.sfCompactSupportRestriction (HasCompactification.compactification f)
    (P.finiteReductionRingHom m hm hmn)
  unfold finiteReductionCompactSupportComparison
  apply (adjY.homEquiv _ _).injective
  rw [adjY.homEquiv_naturality_left, adjY.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hu := adjX.unit.naturality a.hom
  simp only [Functor.id_map, Functor.comp_map] at hu
  erw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  exact congrArg (fun z ↦ (P.smoothCompactSupport f).map (adjX.unit.app K.obj) ≫ z)
    (c.hom.naturality ((P.finiteReduction m hm hmn X).map a.hom))

private theorem pointReductionCounit_naturality
    {K L : Scheme.proEtaleDerivedCategory Y P.Ring}
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y L)
    (a : K ⟶ L) :
    (P.smoothCompactSupport f).map ((P.compositionExceptional f).map a) ≫
        P.smoothExceptionalCounit f L = P.smoothExceptionalCounit f K ≫ a := by
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let E := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let H := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have hK' := (P.compositionInput_bounded K hK).plusEtaleOrigin.plus
  have hL' := (P.compositionInput_bounded L hL).plusEtaleOrigin.plus
  have hn := ProEtale.rightDerivedUpperShriekCounit_naturality f hK' hL'
    (H.inverse.map a)
  have hs := (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
    (HasCompactification.compactification f)).hom.naturality
      ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))
  change (P.smoothCompactSupport f).map
      (E.functor.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))) ≫ _ = _ at hs
  have hc := H.counitIso.hom.naturality a
  simp only [Functor.comp_map, Functor.id_map] at hc
  simp only [smoothExceptionalCounit, dif_pos hK', dif_pos hL']
  change (P.smoothCompactSupport f).map
      (E.functor.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, hs, Category.assoc, Category.assoc]
  simp only [Functor.comp_map]
  erw [← H.functor.map_comp_assoc, hn]
  rw [H.functor.map_comp, Category.assoc, Category.assoc, hc]
  simp only [Category.assoc]
  rfl

/-- Naturality of the unique counit-normalized exceptional coefficient arrow.
Source: finite-reduction-of-purity, Step 2, finite-reduction-comparisons, exceptional clause
(blueprint: def-weil-point-fibre-stage-constructions).
Proof: apply the compact-support Hom bijection to both composites. Naturality of
that bijection and of the counit, together with the preceding compact-support
naturality, identifies their transposes with the same reduced counit composite.
Injectivity of the Hom bijection proves equality. This uses the defining counit
normalization, not the commutativity of any purity square. -/
theorem pointReductionExceptional_naturality (d : ℕ) [SmoothOfRelativeDimension d f]
    {K L : finiteTorConstructibleCategory P.coefficients.l P.extension
      P.level P.level_pos Y} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn X).map ((P.compositionExceptional f).map a.hom) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d L.obj L.property =
      P.finiteReductionExceptionalComparison m hm hmn f d K.obj K.property ≫
        ((P.finiteReductionSetting m hm).compositionExceptional f).map
          ((P.finiteReduction m hm hmn Y).map a.hom) := by
  let Q := P.finiteReductionSetting m hm
  let RY := P.finiteReduction m hm hmn Y
  let RX := P.finiteReduction m hm hmn X
  let SK := (P.compositionExceptional f).obj K.obj
  let SL := (P.compositionExceptional f).obj L.obj
  have hSK := P.compositionExceptional_ctf f d K.obj K.property
  have hSL := P.compositionExceptional_ctf f d L.obj L.property
  let := P.finiteReductionCompactSupportComparison_isIso m hm hmn f SK hSK
  have hi := Q.finiteReduction_counit_bijective_public f (RX.obj SK)
    (P.finiteReduction_preserves_ctf m hm hmn X SK hSK) (RY.obj L.obj)
    (P.finiteReduction_preserves_ctf m hm hmn Y L.obj L.property)
  apply hi.1
  apply (cancel_epi (P.finiteReductionCompactSupportComparison m hm hmn f SK)).1
  have hn := P.pointReductionCompactSupport_naturality m hm hmn f
    (K := ⟨SK, hSK⟩) (L := ⟨SL, hSL⟩)
    (ObjectProperty.homMk ((P.compositionExceptional f).map a.hom))
  have hK := (P.existsUnique_finiteReductionExceptionalComparison m hm hmn f d
    K.obj K.property).choose_spec.1
  have hL := (P.existsUnique_finiteReductionExceptionalComparison m hm hmn f d
    L.obj L.property).choose_spec.1
  change P.finiteReductionCompactSupportComparison m hm hmn f SK ≫
      (Q.smoothCompactSupport f).map
        (P.finiteReductionExceptionalComparison m hm hmn f d K.obj K.property) ≫
      Q.smoothExceptionalCounit f (RY.obj K.obj) =
    RY.map (P.smoothExceptionalCounit f K.obj) at hK
  change P.finiteReductionCompactSupportComparison m hm hmn f SL ≫
      (Q.smoothCompactSupport f).map
        (P.finiteReductionExceptionalComparison m hm hmn f d L.obj L.property) ≫
      Q.smoothExceptionalCounit f (RY.obj L.obj) =
    RY.map (P.smoothExceptionalCounit f L.obj) at hL
  have hcP := pointReductionCounit_naturality P f K.property L.property a.hom
  have hcQ := pointReductionCounit_naturality Q f
    (P.finiteReduction_preserves_ctf m hm hmn Y K.obj K.property)
    (P.finiteReduction_preserves_ctf m hm hmn Y L.obj L.property) (RY.map a.hom)
  change RY.map ((P.smoothCompactSupport f).map
      ((P.compositionExceptional f).map a.hom)) ≫
      P.finiteReductionCompactSupportComparison m hm hmn f SL =
    P.finiteReductionCompactSupportComparison m hm hmn f SK ≫
      (Q.smoothCompactSupport f).map (RX.map ((P.compositionExceptional f).map a.hom)) at hn
  change (P.finiteReductionCompactSupportComparison m hm hmn f SK) ≫
      (Q.smoothCompactSupport f).map
        (RX.map ((P.compositionExceptional f).map a.hom) ≫
          P.finiteReductionExceptionalComparison m hm hmn f d L.obj L.property) ≫
        Q.smoothExceptionalCounit f (RY.obj L.obj) =
    (P.finiteReductionCompactSupportComparison m hm hmn f SK) ≫
      (Q.smoothCompactSupport f).map
        (P.finiteReductionExceptionalComparison m hm hmn f d K.obj K.property ≫
          (Q.compositionExceptional f).map (RY.map a.hom)) ≫
        Q.smoothExceptionalCounit f (RY.obj L.obj)
  simp only [Functor.map_comp, Category.assoc]
  erw [← Category.assoc, ← hn, Category.assoc, hL,
    ← RY.map_comp, hcP, RY.map_comp, ← hK]
  simp only [Category.assoc]
  exact congrArg
    (fun z ↦ P.finiteReductionCompactSupportComparison m hm hmn f SK ≫
      (Q.smoothCompactSupport f).map
        (P.finiteReductionExceptionalComparison m hm hmn f d K.obj K.property) ≫ z)
    hcQ.symm

end Comparisons

end WeilConjectures.PurityFiniteSetting
