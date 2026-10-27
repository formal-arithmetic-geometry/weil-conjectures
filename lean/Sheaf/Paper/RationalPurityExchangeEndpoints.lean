/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.RationalScalarComparisonData
public import Sheaf.Paper.FieldWeilShriekShiftData
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.AdicPurityScalarNaturalityData
public import Sheaf.Paper.RationalPurityExchangeEndpointData
import Sheaf.Paper.RationalScalarComparisonIdentification
import Sheaf.Paper.RationalLatticeAdicDomain
import Sheaf.Paper.TwistedPullbackCoefficientCoherence

/-! # Scalar comparisons at the two rational purity exchange endpoints

Source: current blueprint sec-smooth-purity/sk-thm-purity-transport,
coefficient change and base change, Steps 2--4
(blueprint: lem-pur-rational-purity-exchange-endpoints).

The families below retain the normalized localization of the supplied integral
purity maps. The exceptional comparison is always the published counit mate.
The endpoint comparisons are composites of these maps and the actual pullback
scalar comparison, including the associators of the original tensor functors.

## Main definitions

- `LocalizedFamily` retains the normalized localized integral purity family.
- `endpointA`, `endpointB`, `comparisonA`, `comparisonB` give the four endpoint comparisons.
- `EndpointEquations` records both naturality squares and their coefficient and shift laws.

## Main statements

- `rationalPurityExchangeEndpoints` supplies the domains, localized families and endpoint equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.RationalPurityExchangeEndpoints
open AdicPurityScalarNaturality RationalScalarComparisonIdentification


section Pasting
variable {A B V A' B' V' : Type (u + 2)}
  [Category.{u + 2} A] [Category.{u + 2} B] [Category.{u + 2} V]
  [Category.{u + 2} A'] [Category.{u + 2} B'] [Category.{u + 2} V']
  {F : A ⥤ B} {U : B ⥤ V} {F' : A' ⥤ B'} {U' : B' ⥤ V'}
  {TA : A ⥤ A'} {TB : B ⥤ B'} {TV : V ⥤ V'}

private theorem compositeComparison_app
    (aF : F ⋙ TB ≅ TA ⋙ F') (aU : U ⋙ TV ≅ TB ⋙ U') (K : A) :
    (compositeComparison aF aU).hom.app K =
      aU.hom.app (F.obj K) ≫ U'.map (aF.hom.app K) := by
  simp [compositeComparison]

private theorem compositeComparison_unit
    {TA : A ⥤ A} {TB : B ⥤ B} {TV : V ⥤ V}
    (aF : F ⋙ TB ≅ TA ⋙ F) (aU : U ⋙ TV ≅ TB ⋙ U)
    (uA : TA ≅ 𝟭 A) (uB : TB ≅ 𝟭 B) (uV : TV ≅ 𝟭 V)
    (hF : UnitEquation aF uB uA) (hU : UnitEquation aU uV uB) :
    UnitEquation (compositeComparison aF aU) uV uA := by
  intro K
  simp only [compositeComparison_app, Functor.comp_map, Functor.comp_obj, Category.assoc]
  rw [← U.map_comp, hF K]
  exact hU (F.obj K)

private theorem compositeComparison_tower
    {A'' B'' V'' : Type (u + 2)}
    [Category.{u + 2} A''] [Category.{u + 2} B''] [Category.{u + 2} V'']
    {F'' : A'' ⥤ B''} {U'' : B'' ⥤ V''}
    {UA : A' ⥤ A''} {UB : B' ⥤ B''} {UV : V' ⥤ V''}
    {VA : A ⥤ A''} {VB : B ⥤ B''} {VV : V ⥤ V''}
    (aF : F ⋙ TB ≅ TA ⋙ F') (aU : U ⋙ TV ≅ TB ⋙ U')
    (bF : F' ⋙ UB ≅ UA ⋙ F'') (bU : U' ⋙ UV ≅ UB ⋙ U'')
    (cF : F ⋙ VB ≅ VA ⋙ F'') (cU : U ⋙ VV ≅ VB ⋙ U'')
    (eA : TA ⋙ UA ≅ VA) (eB : TB ⋙ UB ≅ VB) (eV : TV ⋙ UV ≅ VV)
    (hF : CompositionEquation aF bF cF eB eA)
    (hU : CompositionEquation aU bU cU eV eB) :
    CompositionEquation (compositeComparison aF aU) (compositeComparison bF bU)
      (compositeComparison cF cU) eV eA := by
  intro K
  simp only [compositeComparison_app, Functor.comp_obj, Functor.comp_map]
  rw [← Category.assoc, hU (F.obj K)]
  simp only [Category.assoc]
  rw [← U''.map_comp, hF K]
  simp only [Functor.map_comp, Category.assoc]
  have hn : bU.hom.app (TB.obj (F.obj K)) ≫ U''.map (UB.map (aF.hom.app K)) =
      UV.map (U'.map (aF.hom.app K)) ≫ bU.hom.app (F'.obj (TA.obj K)) := by
    simpa only [Functor.comp_map, Functor.comp_obj] using (bU.hom.naturality (aF.hom.app K)).symm
  rw [reassoc_of% hn]

private theorem compositeComparison_shift
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    [HasShift A' ℤ] [HasShift B' ℤ] [HasShift V' ℤ]
    (sF : F.CommShift ℤ) (sU : U.CommShift ℤ)
    (sF' : F'.CommShift ℤ) (sU' : U'.CommShift ℤ)
    (sA : TA.CommShift ℤ) (sB : TB.CommShift ℤ) (sV : TV.CommShift ℤ)
    (aF : F ⋙ TB ≅ TA ⋙ F') (aU : U ⋙ TV ≅ TB ⋙ U')
    (hF : ShiftCompatibility _ _ (composeShift _ _ sF sB)
      (composeShift _ _ sA sF') aF)
    (hU : ShiftCompatibility _ _ (composeShift _ _ sU sV)
      (composeShift _ _ sB sU') aU) :
    ShiftCompatibility _ _ (composeShift _ _ (composeShift _ _ sF sU) sV)
      (composeShift _ _ sA (composeShift _ _ sF' sU')) (compositeComparison aF aU) := by
  let := sF
  let := sU
  let := sF'
  let := sU'
  let := sA
  let := sB
  let := sV
  let : NatTrans.CommShift aF.hom ℤ := hF
  let : NatTrans.CommShift aU.hom ℤ := hU
  unfold ShiftCompatibility composeShift compositeComparison
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom]
  infer_instance

private theorem whiskerRight_inverse_shift
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    {F' : A ⥤ B} (sF : F.CommShift ℤ) (sF' : F'.CommShift ℤ)
    (sU : U.CommShift ℤ) (eta : F ≅ F') (h : ShiftCompatibility F F' sF sF' eta) :
    ShiftCompatibility _ _ (composeShift _ _ sF' sU) (composeShift _ _ sF sU)
      (Functor.isoWhiskerRight eta.symm U) := by
  let := sF
  let := sF'
  let := sU
  let : NatTrans.CommShift eta.hom ℤ := h
  unfold ShiftCompatibility composeShift
  simp only [Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

private theorem whiskerLeft_shift
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    {U' : B ⥤ V} (sF : F.CommShift ℤ) (sU : U.CommShift ℤ)
    (sU' : U'.CommShift ℤ) (eta : U ≅ U') (h : ShiftCompatibility U U' sU sU' eta) :
    ShiftCompatibility _ _ (composeShift _ _ sF sU) (composeShift _ _ sF sU')
      (Functor.isoWhiskerLeft F eta) := by
  let := sF
  let := sU
  let := sU'
  let : NatTrans.CommShift eta.hom ℤ := h
  unfold ShiftCompatibility composeShift
  simp only [Functor.isoWhiskerLeft_hom]
  infer_instance

private theorem inverse_purity_square
    {GE : A ⥤ B} {GF : A' ⥤ B'}
    (eta : F ≅ GE) (eta' : F' ≅ GF)
    (a : F ⋙ TB ≅ TA ⋙ F') (b : GE ⋙ TB ≅ TA ⋙ GF)
    (h : PuritySquares eta eta' a b) (K : A) :
    TB.map (eta.inv.app K) ≫ a.hom.app K = b.hom.app K ≫ eta'.inv.app (TA.obj K) := by
  apply (cancel_epi (TB.map (eta.hom.app K))).mp
  simp only [← TB.map_comp_assoc, Iso.hom_inv_id_app]
  rw [← Category.assoc, h.1 K]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  change TB.map (𝟙 (F.obj K)) ≫ a.hom.app K = a.hom.app K ≫ 𝟙 _
  rw [TB.map_id, Category.id_comp, Category.comp_id]

private theorem compositeComparison_square_right
    {GE : A ⥤ B} {GF : A' ⥤ B'}
    (eta : F ≅ GE) (eta' : F' ≅ GF)
    (a : F ⋙ TB ≅ TA ⋙ F') (b : GE ⋙ TB ≅ TA ⋙ GF)
    (p : U ⋙ TV ≅ TB ⋙ U') (h : PuritySquares eta eta' a b) :
    Functor.whiskerRight (Functor.isoWhiskerRight eta.symm U).hom TV ≫
        (compositeComparison a p).hom =
      (compositeComparison b p).hom ≫
        Functor.whiskerLeft TA (Functor.isoWhiskerRight eta'.symm U').hom := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, compositeComparison_app]
  change TV.map (U.map (eta.inv.app K)) ≫
      (p.hom.app (F.obj K) ≫ U'.map (a.hom.app K)) =
    (p.hom.app (GE.obj K) ≫ U'.map (b.hom.app K)) ≫
      U'.map (eta'.inv.app (TA.obj K))
  have hn : TV.map (U.map (eta.inv.app K)) ≫ p.hom.app (F.obj K) =
      p.hom.app (GE.obj K) ≫ U'.map (TB.map (eta.inv.app K)) := by
    simpa only [Functor.comp_map] using p.hom.naturality (eta.inv.app K)
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← U'.map_comp, inverse_purity_square eta eta' a b h K, U'.map_comp]

private theorem compositeComparison_square_left
    {GE : B ⥤ V} {GF : B' ⥤ V'}
    (eta : U ≅ GE) (eta' : U' ≅ GF)
    (a : U ⋙ TV ≅ TB ⋙ U') (b : GE ⋙ TV ≅ TB ⋙ GF)
    (p : F ⋙ TB ≅ TA ⋙ F') (h : PuritySquares eta eta' a b) :
    Functor.whiskerRight (Functor.isoWhiskerLeft F eta).hom TV ≫
        (compositeComparison p b).hom =
      (compositeComparison p a).hom ≫
        Functor.whiskerLeft TA (Functor.isoWhiskerLeft F' eta').hom := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_hom, compositeComparison_app]
  change TV.map (eta.hom.app (F.obj K)) ≫
      (b.hom.app (F.obj K) ≫ GF.map (p.hom.app K)) =
    (a.hom.app (F.obj K) ≫ U'.map (p.hom.app K)) ≫
      eta'.hom.app (F'.obj (TA.obj K))
  rw [← Category.assoc, h.1 (F.obj K)]
  simp only [Category.assoc]
  rw [← eta'.hom.naturality]
  simp only [Functor.comp_obj]

end Pasting

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)


attribute [local irreducible] sfRationalScalarExtension rationalDerivedPullback
  constructibleIntegralPullback

private theorem pullbackUnit_eq (W : Scheme.{u})
    (E : AdicPurityScalarNaturality.Field D C) :
    TwistedPullbackScalars.unit C.l C.Qbar W E = unit D C E W := by
  unfold TwistedPullbackScalars.unit unit
  dsimp only [TwistedPullbackScalars.T]
  erw [eqToIso_refl, Iso.refl_trans]

private theorem pullbackAlpha_eq (W : Scheme.{u})
    (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) :
    TwistedPullbackScalars.alpha C.l C.Qbar W E F L h k = alpha D C E F L h k W := by
  unfold TwistedPullbackScalars.alpha alpha
  dsimp only [TwistedPullbackScalars.T]
  erw [eqToIso_refl, Iso.trans_refl]

section Family
attribute [local irreducible] O G H T Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : AdicPurityScalarNaturality.Data D C f d S)


private theorem localizedFamily_exists : Nonempty (LocalizedFamily D C f d S I) := by
  obtain ⟨hs, he, hl, hn, hls, hgs, sl, sn, ss, _, _, _,
    eta, es, el, a, ash, bsh, ac, al, bl, bm, ps, au, bu, atw, btw⟩ :=
    rationalScalarComparisonIdentification D C f d S I
  exact ⟨{
    data := {
      hShift := hs
      hLocalization := hl
      scalarLocalization := sl
      gamma := eta
      a := a
    }
    laws := {
      hExact := by
        simpa only [localizedFamilyLawHExact] using he
      hNormalized := by
        simpa only [localizedFamilyLawHNormalized] using hn
      hLocalizationShift := by
        simpa only [localizedFamilyLawHLocalizationShift] using hls
      gLocalizationShift := by
        simpa only [localizedFamilyLawGLocalizationShift] using hgs
      scalarNormalized := by
        simpa only [localizedFamilyLawScalarNormalized] using sn
      scalarLocalizationShift := by
        simpa only [localizedFamilyLawScalarLocalizationShift] using ss
      gammaLocalized := by
        simpa only [localizedFamilyLawGammaLocalized] using el
      aCanonical := by
        simpa only [localizedFamilyLawACanonical] using ac
      aLocalized := by
        simpa only [localizedFamilyLawALocalized] using al
      bLocalized := by
        simpa only [localizedFamilyLawBLocalized] using bl
      bMate := by
        simpa only [localizedFamilyLawBMate] using bm
      purity := by
        simpa only [localizedFamilyLawPurity] using ps
      aUnit := by
        simpa only [localizedFamilyLawAUnit] using au
      bUnit := by
        simpa only [localizedFamilyLawBUnit] using bu
      aTower := by
        simpa only [localizedFamilyLawATower] using atw
      bTower := by
        simpa only [localizedFamilyLawBTower] using btw
      gammaShift := by
        simpa only [localizedFamilyLawGammaShift] using es
      aShift := by
        simpa only [localizedFamilyLawAShift] using ash
      bShift := by
        simpa only [localizedFamilyLawBShift] using bsh
    }
  }⟩
end Family

section Statement
attribute [local irreducible] O G H Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target
variable {X X' Y Y' : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [X'.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
  [IsSeparated (X' ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
  [IsSeparated (Y' ↘ Spec (.of D.k))]
  (uMap : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  [uMap.IsOver (Spec (.of D.k))] [f.IsOver (Spec (.of D.k))]
  [f'.IsOver (Spec (.of D.k))] [v.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Rational purity and scalar extension at both exchange endpoints, including all domains.
Source: current blueprint purity transport Steps 2--4, coefficient-change proof (2)--(3),
and its base-change conclusion (blueprint: lem-pur-rational-purity-exchange-endpoints).
Proof: (1) rational_lattice_adic_base and rational_lattice_adic_domain apply to each
of the four separated finite-type schemes. Smooth relative dimension and separatedness
are preserved by the given Cartesian square, including an empty X'. (2) Pull back
an integral representative using integralOperations_preserve_constructible, then use
the uniform Tor interval from rational_lattice_adic_domain. The object formula for
rationalDerivedPullback gives exactly the claimed representative. (3) Apply
rationalScalarComparisonIdentification to the two supplied simultaneous integral
families. Its normalized source localization, canonical sourceScalar formula and
counit transpose fix all the maps and give (P). (4) Extend integral naturality to
all fractional arrows by linearity and a common denominator; localize the unit,
tower and shift equations. (5) Cancel the inverse purity maps in (P), and use
naturality of p_u at gamma_f inverse to get (A). (6) Use (P) for f' at Lv*K and
naturality of gamma_f' at p_v to get (B). (7) At an identity field inclusion both
factors of each pasted comparison are units. (8) For a coefficient tower apply
the factor tower equations, then naturality to interchange the middle factors;
the remaining outer maps are precisely the displayed tensor associators.
(9) Apply the factor shift equations to each composite. The same equations for
gamma and its inverse shift (P), (A), (B) term by term. Substitution of their
unit and tower equations in the two calculations proves compatibility without
any additional identification of the exceptional comparison. -/
theorem rationalPurityExchangeEndpoints (sq : IsPullback uMap f' f v) :
    BaseConditions D C X ∧ BaseConditions D C X' ∧
    BaseConditions D C Y ∧ BaseConditions D C Y' ∧
    LatticeDomain D C X ∧ LatticeDomain D C X' ∧
    LatticeDomain D C Y ∧ LatticeDomain D C Y' ∧
    PullbackLattice D C v ∧
    ∃ (hSmooth : SmoothOfRelativeDimension d f') (hSep : IsSeparated f')
      (hLft : LocallyOfFiniteType f') (hQc : QuasiCompact f'),
    (fun [hs : SmoothOfRelativeDimension d f'] [hi : IsSeparated f']
      [ht : LocallyOfFiniteType f'] [hc : QuasiCompact f'] ↦
      ∀ (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
        (S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f'))
        (I : AdicPurityScalarNaturality.Data D C f d S)
        (I' : AdicPurityScalarNaturality.Data D C f' d S'),
        ∃ (R : LocalizedFamily D C f d S I) (R' : LocalizedFamily D C f' d S' I'),
          EndpointEquations D C uMap f f' v d S S' I I' R R')
      (hs := hSmooth) (hi := hSep) (ht := hLft) (hc := hQc) := by
  classical
  let P (E : AdicPurityScalarNaturality.Field D C) : PurityFiniteSetting :=
    { field := D, coefficients := C, extension := E.val, level := 1, level_pos := le_rfl }
  have hBase (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
      [QuasiCompact (W ↘ Spec (.of D.k))] [IsSeparated (W ↘ Spec (.of D.k))] :
      BaseConditions D C W :=
    rational_lattice_adic_base (P ⟨⊥, inferInstance⟩) W
  have hLattice (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
      [QuasiCompact (W ↘ Spec (.of D.k))] [IsSeparated (W ↘ Spec (.of D.k))] :
      LatticeDomain D C W := by
    intro E K
    refine ⟨K.obj, ?_, ⟨Iso.refl _⟩⟩
    exact ((rational_lattice_adic_domain (P E) W).1 K.obj.obj K.obj.property).2
  have hPull : PullbackLattice D C v := by
    intro E K
    refine ⟨K.obj, ?_, ⟨Iso.refl _⟩, ?_, ?_⟩
    · exact ((rational_lattice_adic_domain (P E) Y).1 K.obj.obj K.obj.property).2
    · exact ((rational_lattice_adic_domain (P E) Y').1 _
        ((constructibleIntegralPullback C.l E.val v).obj K.obj).property).2
    · unfold rationalDerivedPullback
      exact ⟨eqToIso ((rationalDerivedPullback_existsUnique C.l E.val v).exists.choose_spec.2.1
        K).symm⟩
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  let hs : SmoothOfRelativeDimension d f' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq inferInstance
  let hi : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  let ht : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  let hc : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let := hs
  let := hi
  let := ht
  let := hc
  refine ⟨hBase X, hBase X', hBase Y, hBase Y', hLattice X, hLattice X',
    hLattice Y, hLattice Y', hPull, hs, hi, ht, hc, ?_⟩
  let : IsNoetherian X := (hBase X).1
  let : IsNoetherian X' := (hBase X').1
  let : IsNoetherian Y := (hBase Y).1
  let : IsNoetherian Y' := (hBase Y').1
  let : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n) := ⟨(hBase X).2.1⟩
  let : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n) := ⟨(hBase X').2.1⟩
  let : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n) := ⟨(hBase Y).2.1⟩
  let : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n) := ⟨(hBase Y').2.1⟩
  let : Fact (∀ x : X, IsUnit (C.l : X.presheaf.stalk x)) := ⟨(hBase X).2.2⟩
  let : Fact (∀ x : X', IsUnit (C.l : X'.presheaf.stalk x)) := ⟨(hBase X').2.2⟩
  let : Fact (∀ x : Y, IsUnit (C.l : Y.presheaf.stalk x)) := ⟨(hBase Y).2.2⟩
  let : Fact (∀ x : Y', IsUnit (C.l : Y'.presheaf.stalk x)) := ⟨(hBase Y').2.2⟩
  obtain ⟨sh, _, tw, _⟩ := TwistedPullbackScalars.twistedPullbackCoefficientCoherence
    C.l C.Qbar uMap f f' v sq.w d
  obtain ⟨_, _, pu, _, _, pv, _⟩ := tw
  have pUnit {W V : Scheme.{u}} (g : W ⟶ V)
      [∀ x : W, Invertible (C.l : W.residueField x)]
      [∀ x : V, Invertible (C.l : V.residueField x)]
      (hp : TwistedPullbackScalars.Coherent C.l C.Qbar
        (TwistedPullbackScalars.pFamily C.l C.Qbar g))
      (E : AdicPurityScalarNaturality.Field D C) :
      UnitEquation
        (rationalPullbackScalarComparison C.l E.val E.val (IntermediateField.inclusion le_rfl) g)
        (unit D C E W) (unit D C E V) := by
    unfold UnitEquation
    intro K
    simpa only [TwistedPullbackScalars.pFamily, TwistedPullbackScalars.p,
      pullbackUnit_eq D C, Iso.app_hom] using hp.2.1 E K
  have pTower {W V : Scheme.{u}} (g : W ⟶ V)
      [∀ x : W, Invertible (C.l : W.residueField x)]
      [∀ x : V, Invertible (C.l : V.residueField x)]
      (hp : TwistedPullbackScalars.Coherent C.l C.Qbar
        (TwistedPullbackScalars.pFamily C.l C.Qbar g))
      (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) :
      CompositionEquation
        (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) g)
        (rationalPullbackScalarComparison C.l F.val L.val (IntermediateField.inclusion k) g)
        (rationalPullbackScalarComparison C.l E.val L.val
          (IntermediateField.inclusion (h.trans k)) g)
        (alpha D C E F L h k W) (alpha D C E F L h k V) := by
    unfold CompositionEquation
    intro K
    simpa only [TwistedPullbackScalars.pFamily, TwistedPullbackScalars.p,
      TwistedPullbackScalars.T, pullbackAlpha_eq D C, Iso.app_hom] using hp.2.2 E F L h k K
  have pShift {W V : Scheme.{u}} (g : W ⟶ V)
      [∀ x : W, Invertible (C.l : W.residueField x)]
      [∀ x : V, Invertible (C.l : V.residueField x)]
      (hp : TwistedPullbackScalars.ShiftCompatible C.l C.Qbar
        (TwistedPullbackScalars.pFamily C.l C.Qbar g)
        (fun E ↦ fieldRationalPullShift C.l E.val g))
      (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
      ShiftCompatibility _ _
        (composeShift _ _ (fieldRationalPullShift C.l E.val g) (tShift D C E F h W))
        (composeShift _ _ (tShift D C E F h V) (fieldRationalPullShift C.l F.val g))
        (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) g) := by
    let := fieldRationalPullShift C.l E.val g
    let := fieldRationalPullShift C.l F.val g
    let := tShift D C E F h W
    let := tShift D C E F h V
    unfold ShiftCompatibility composeShift
    refine { shift_comm := ?_ }
    intro n
    ext K
    dsimp +instances only [Functor.commShiftIso, Functor.CommShift.comp, tShift, T]
    simp only [Iso.trans_hom, Iso.symm_hom,
      Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Category.id_comp, Category.comp_id]
    delta tShift
    simpa only [TwistedPullbackScalars.pFamily, TwistedPullbackScalars.p,
      TwistedPullbackScalars.T, Iso.app_hom] using (hp E F h n K).symm
  intro S S' I I'
  obtain ⟨R⟩ := localizedFamily_exists D C f d S I
  obtain ⟨R'⟩ := localizedFamily_exists D C f' d S' I'
  refine ⟨R, R', ?_⟩
  refine {
    squareA := ?_
    squareB := ?_
    unitA := ?_
    unitB := ?_
    towerA := ?_
    towerB := ?_
    shiftComparisonA := ?_
    shiftComparisonB := ?_
    shiftS := ?_
    shiftT := ?_ }
  · intro E F h
    exact compositeComparison_square_right (R.gamma E) (R.gamma F)
      (R.a E F h) (b D C f S E F h)
      (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) uMap)
      (R.purity E F h)
  · intro E F h
    exact compositeComparison_square_left (R'.gamma E) (R'.gamma F)
      (R'.a E F h) (b D C f' S' E F h)
      (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) v)
      (R'.purity E F h)
  · intro E exceptional
    cases exceptional with
    | false =>
        exact compositeComparison_unit _ _ _ _ _ (R.aUnit E) (pUnit uMap pu E)
    | true =>
        exact compositeComparison_unit _ _ _ _ _ (R.bUnit E) (pUnit uMap pu E)
  · intro E exceptional
    cases exceptional with
    | false =>
        exact compositeComparison_unit _ _ _ _ _ (pUnit v pv E) (R'.aUnit E)
    | true =>
        exact compositeComparison_unit _ _ _ _ _ (pUnit v pv E) (R'.bUnit E)
  · intro E F L h k exceptional
    cases exceptional with
    | false =>
        exact compositeComparison_tower _ _ _ _ _ _ _ _ _
          (R.aTower E F L h k) (pTower uMap pu E F L h k)
    | true =>
        exact compositeComparison_tower _ _ _ _ _ _ _ _ _
          (R.bTower E F L h k) (pTower uMap pu E F L h k)
  · intro E F L h k exceptional
    cases exceptional with
    | false =>
        exact compositeComparison_tower _ _ _ _ _ _ _ _ _
          (pTower v pv E F L h k) (R'.aTower E F L h k)
    | true =>
        exact compositeComparison_tower _ _ _ _ _ _ _ _ _
          (pTower v pv E F L h k) (R'.bTower E F L h k)
  · intro E F h exceptional
    cases exceptional with
    | false =>
        exact compositeComparison_shift _ _ _ _ _ _ _ _ _ (R.aShift E F h)
          (pShift uMap sh.pu E F h)
    | true =>
        exact compositeComparison_shift _ _ _ _ _ _ _ _ _ (R.bShift E F h)
          (pShift uMap sh.pu E F h)
  · intro E F h exceptional
    cases exceptional with
    | false =>
        exact compositeComparison_shift _ _ _ _ _ _ _ _ _ (pShift v sh.pv E F h)
          (R'.aShift E F h)
    | true =>
        exact compositeComparison_shift _ _ _ _ _ _ _ _ _ (pShift v sh.pv E F h)
          (R'.bShift E F h)
  · intro E
    exact whiskerRight_inverse_shift _ _ _ (R.gamma E) (R.gammaShift E)
  · intro E
    exact whiskerLeft_shift _ _ _ (R'.gamma E) (R'.gammaShift E)
end Statement
end WeilConjectures.RationalPurityExchangeEndpoints
