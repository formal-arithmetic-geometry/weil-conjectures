/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.PurityVectorBundleZeroSection
public import Sheaf.Paper.CartierClassAgreement
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import Sheaf.Paper.ComparisonImageClosedSectionNormalization
public import Sheaf.Paper.CartierSupportedComparisonSquare
import Sheaf.Paper.CartierRelativeKummerRealization
import Sheaf.Paper.LineZeroGeometry
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-! # The zero divisor of a line bundle and its etale realization

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 1
(blueprint: lem-pur-line-zero-class-etale-realization).

The supported maps are the published Cartier maps in their canonical finite-root chart.
The source identifications use the composition and identity comparisons, rather than
an unspecified isomorphism. The target witness retains the etale compact-support object.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v w c
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting
set_option allowUnsafeReducibility true in
attribute [local irreducible] PurityVectorBundle.zeroSection VectorBundleZeroSection.zero


set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupSheaves functorialCupCategory functorialCupAbelian
  functorialCupHasDerived functorialCupSingle functorialCupComparisonFunctor
  functorialCupSource functorialCupTwist

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategorySingleFunctor
  agreementCartierMap agreementCartierEtale functorialCupCompare

variable {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
  {b : B ⟶ Spec (.of P.field.k)}
  [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]

/-- The base-changed zero section over an arbitrary scheme B'. No flatness or
Noetherian hypothesis is used. Source: blueprint Step 1, universal Cartier clause
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroBaseChange (V : PurityVectorBundle P B b 1) {B' : Scheme.{u}} (h : B' ⟶ B) :
    B' ⟶ pullback V.p h :=
  pullback.lift (h ≫ V.zeroSection) (𝟙 B') (by
    rw [Category.assoc, V.zeroSection_spec.1, Category.comp_id, Category.id_comp])

/-- All geometric assertions and the domain facts needed to form compact supports.
Source: blueprint Step 1, expanded proof steps 1--2
(blueprint: lem-pur-line-zero-class-etale-realization).
Proof: on a Zariski affine frame the bundle is Spec R[t], its projection is smooth
of relative dimension one, and its zero section is the quotient t=0. The section
identity makes its map to B smooth of relative dimension zero. Multiplication by t
is injective by coefficient comparison, over every R and every base-changed R'.
Thus the zero ideal is Cartier, universally over B. B and E are Noetherian by
finite type over the field; quotienting their local rings by t drops dimension by
one. The relative-Spec charts and vector-projective completion give separatedness,
finite type and compactifiability; composing diagonals gives the absolute facts.
Closed pro-etale direct image is exact because E has a quasi-compact complement
to its zero section. The composite of the section and projection is the identity,
so it has the identity compactification. -/
theorem line_zero_geometry (V : PurityVectorBundle P B b 1) :
    IsSeparated V.p ∧ LocallyOfFiniteType V.p ∧ QuasiCompact V.p ∧
    SmoothOfRelativeDimension 1 V.p ∧ IsClosedImmersion V.zeroSection ∧
    SmoothOfRelativeDimension 0 (V.zeroSection ≫ V.p) ∧
    V.zeroSection.ker.IsInvertible ∧
    (∀ x : B, ringKrullDim (V.E.presheaf.stalk (V.zeroSection x)) =
      ringKrullDim (B.presheaf.stalk x) + (1 : WithBot ℕ∞)) ∧
    (∀ (B' : Scheme.{u}) (h : B' ⟶ B),
      IsClosedImmersion (lineZeroBaseChange V h) ∧
        (lineZeroBaseChange V h).ker.IsInvertible) ∧
    IsSeparated (V.p ≫ b) ∧ LocallyOfFiniteType (V.p ≫ b) ∧ QuasiCompact (V.p ≫ b) ∧
    HasCompactification V.p ∧ HasCompactification (V.zeroSection ≫ V.p) ∧
    PreservesFiniteColimits (ProEtale.lowerStar
      (ModuleCat.{u + 1} P.Coefficient) V.zeroSection) := by
  obtain ⟨hB, hE, haSep, haFt, haQc, hpSep, hpFt, hpQc, hpSm, hcompletion,
    hz, hsection, hcartier, hzSm, hdim, hcompl, hbase, hcharts⟩ :=
    PurityVectorBundle.lineZeroGeometry P B b V
  let := hB
  let := hE
  let := hpSep
  let := hpFt
  let := hpQc
  let := hz
  let := hcompl
  obtain ⟨Q, ht, a, _, _, c, e, _⟩ := hcompletion
  let := c.hasCompactification
  have : HasCompactification (V.zeroSection ≫ V.p) :=
    HasCompactification.of_eq hsection.symm
  refine ⟨hpSep, hpFt, hpQc, hpSm, hz, hzSm,
    isEffectiveCartierCenter_iff_isInvertible_ker.mp hcartier, hdim, ?_,
    haSep, haFt, haQc, inferInstance, inferInstance, ?_⟩
  · intro B' h
    have heq : lineZeroBaseChange V h =
        sectionBaseChange V.p V.zeroSection V.zeroSection_spec.1 (Over.mk h) := rfl
    rw [heq]
    have := (hbase B' h).isClosedImmersion
    exact ⟨inferInstance, isEffectiveCartierCenter_iff_isInvertible_ker.mp (hbase B' h)⟩
  · exact ProEtale.preservesFiniteColimits_lowerStar_of_isCompl
      V.zeroSection V.zeroSection.openComplement.ι
      (eq_compl_iff_isCompl.mp V.zeroSection.range_eq_compl_range_openComplement_ι)

/-- The geometric domain facts, taken from line_zero_geometry.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroSeparated (V : PurityVectorBundle P B b 1) : IsSeparated V.p :=
  (line_zero_geometry V).1

/-- The same finite-type domain fact.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroFiniteType (V : PurityVectorBundle P B b 1) : LocallyOfFiniteType V.p :=
  (line_zero_geometry V).2.1

/-- The quasi-compact part of finite type.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroQuasiCompact (V : PurityVectorBundle P B b 1) : QuasiCompact V.p :=
  (line_zero_geometry V).2.2.1

/-- The zero immersion needed by supported-Hom.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroClosed (V : PurityVectorBundle P B b 1) : IsClosedImmersion V.zeroSection :=
  (line_zero_geometry V).2.2.2.2.1

/-- Absolute separatedness, for the existing divisor class.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroAbsoluteSeparated (V : PurityVectorBundle P B b 1) :
    IsSeparated (V.p ≫ b) := (line_zero_geometry V).2.2.2.2.2.2.2.2.2.1

/-- Absolute local finite type, for the existing divisor class.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroAbsoluteFiniteType (V : PurityVectorBundle P B b 1) :
    LocallyOfFiniteType (V.p ≫ b) := (line_zero_geometry V).2.2.2.2.2.2.2.2.2.2.1

/-- Absolute quasi-compactness, for the existing divisor class.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroAbsoluteQuasiCompact (V : PurityVectorBundle P B b 1) :
    QuasiCompact (V.p ≫ b) := (line_zero_geometry V).2.2.2.2.2.2.2.2.2.2.2.1

/-- The compactification exists by projective completion.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroCompactifiable (V : PurityVectorBundle P B b 1) :
    HasCompactification V.p := (line_zero_geometry V).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The section composite has the identity compactification.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroCompositeCompactifiable (V : PurityVectorBundle P B b 1) :
    HasCompactification (V.zeroSection ≫ V.p) :=
  (line_zero_geometry V).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Exactness of the closed image on the Noetherian total space.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
instance lineZeroPushforwardExact (V : PurityVectorBundle P B b 1) :
    PreservesFiniteColimits (ProEtale.lowerStar
      (ModuleCat.{u + 1} P.Coefficient) V.zeroSection) :=
  (line_zero_geometry V).2.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option linter.defProp false in
/-- The already constructed invertible Cartier ideal, without choosing divisor data.
Source: blueprint Step 1 (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroIdeal (V : PurityVectorBundle P B b 1) : V.zeroSection.ker.IsInvertible :=
  (line_zero_geometry V).2.2.2.2.2.2.1

/-- Degree-zero constants, regarded in the published bounded-below etale category.
Source: blueprint Step 1, etale witness (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.constantEtale T)

/-- Degree-zero supported constants in the etale witness.
Source: blueprint Step 1, c^e source (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleSource (V : PurityVectorBundle P B b 1) :
    DerivedCategory.Plus (Sheaf V.E.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf V.E.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.functorialCupSource false V.zeroSection)

/-- The etale root line shifted by two. Its degree-zero model is the derived tensor
mu_N tensor^L A, since mu_N is flat; no flatness of A over Z/N is required.
Source: blueprint Step 1, L_E[2] (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  P.cartierComparisonEtaleTarget T

/-- The canonical Ext realization, with the derived-category instance fixed by the
expected endpoints, before specializing to a site.
Source: Mathlib Ext.hom (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroExtHom {C : Type c} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] [hD : HasDerivedCategory.{w} C] {X Y : C} (κ : Abelian.Ext X Y 2) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧ := κ.hom

/-- The same supported Cartier arrow, lifted by the fully faithful D+ inclusion.
Source: blueprint Step 1, c^e (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleMap (V : PurityVectorBundle P B b 1) :
    lineZeroEtaleSource V ⟶ P.lineZeroEtaleTarget V.E :=
  P.cartierComparisonEtaleMap (V.p ≫ b) V.zeroSection (lineZeroIdeal V)

/-- The prescribed pro-etale constants in degree zero.
Source: blueprint Step 1, A_B (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroProUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.constant T)

/-- The supported pro-etale constants in degree zero.
Source: blueprint Step 1, c^p source (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroProSource (V : PurityVectorBundle P B b 1) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology V.E) (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf (Scheme.ProEt.topology V.E) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.functorialCupSource true V.zeroSection)

/-- The prescribed Tate twist in its published finite-root chart, shifted by two.
Source: def-pur-frame-class, projection-induced chart and blueprint Step 1
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroProTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  P.cartierComparisonProTarget T

/-- The actual supported Cartier arrow in that same root chart, as published by
cartier_class_agreement. Source: blueprint Step 1, c^p
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroProMap (V : PurityVectorBundle P B b 1) :
    lineZeroProSource V ⟶ P.lineZeroProTarget V.E :=
  P.cartierComparisonProMap (V.p ≫ b) V.zeroSection (lineZeroIdeal V)

/-- Exact comparison on the coefficient unit, including its single-object identification.
Source: blueprint Step 1, canonical constant comparison
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroUnitComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.lineZeroEtaleUnit T).obj ≅ (P.lineZeroProUnit T).obj :=
  closedSectionChi P T

/-- Exact comparison on the supported unit, normalized by the supported constant quotient.
Source: blueprint Step 1, supported source comparison
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroSupportedComparison (V : PurityVectorBundle P B b 1) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategory.obj
      (lineZeroEtaleSource V).obj ≅ (lineZeroProSource V).obj :=
  closedSectionEpsilon P V.zeroSection

/-- Exact comparison on the shifted root line. Its finite-root presentation is exactly
that of def-pur-frame-class, hence it retains the projection-induced Tate comparison.
Source: blueprint Step 1, theta_E[2]
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroTwistComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.lineZeroEtaleTarget T).obj ≅ (P.lineZeroProTarget T).obj :=
  P.cartierComparisonTwist T

/-- The coefficient unit as an object of the existing full etale-origin class.
It is the explicit image of the degree-zero etale unit under the comparison functor.
Source: blueprint Step 1, constant source
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroOriginUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) T).FullSubcategory :=
  (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T).obj
    (P.lineZeroEtaleUnit T)

/-- The proper/exact pro-etale closed-image identification.
Source: blueprint Step 1, Rz_!=Rz_*=z_*
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroProClosedIso (V : PurityVectorBundle P B b 1) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj (P.lineZeroOriginUnit B).obj ≅ (lineZeroProSource V).obj :=
  closedSectionIp P V.zeroSection

/-- The proper/exact etale closed-image identification, lifted through the full inclusion.
Source: blueprint Step 1, ordinary etale Rz_!=z_*
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleClosedIso (V : PurityVectorBundle P B b 1) :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj (P.lineZeroEtaleUnit B) ≅ lineZeroEtaleSource V :=
  closedSectionIe P V.zeroSection

/-- The prescribed pro-etale source isomorphism: closed image, composition,
section equality, and identity normalization, in that order.
Source: blueprint Step 1, Rpi_! z_* A_B = A_B
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroProSourceIso (V : PurityVectorBundle P B b 1) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (lineZeroProSource V).obj ≅ (P.lineZeroProUnit B).obj :=
  closedSectionSigmap P V.p V.zeroSection V.zeroSection_spec.1

/-- The identical etale source normalization, using the published etale compositor.
Source: blueprint Step 1, ordinary etale source A_B
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleSourceIso (V : PurityVectorBundle P B b 1) :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (lineZeroEtaleSource V) ≅ P.lineZeroEtaleUnit B :=
  closedSectionSigmae P V.p V.zeroSection V.zeroSection_spec.1

/-- The actual pro-etale tau, with the specified source isomorphism.
Source: blueprint Step 1, tau_E (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroTau (V : PurityVectorBundle P B b 1) :
    (P.lineZeroProUnit B).obj ⟶
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (P.lineZeroProTarget V.E).obj :=
  (lineZeroProSourceIso V).inv ≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).map
      (lineZeroProMap V).hom

/-- Its etale antecedent, with source A_B fixed by the same composition normalization.
Source: blueprint Step 1, Rpi_!^et c^e
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroEtaleTau (V : PurityVectorBundle P B b 1) :
    P.lineZeroEtaleUnit B ⟶
      (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (P.lineZeroEtaleTarget V.E) :=
  (lineZeroEtaleSourceIso V).inv ≫
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).map
      (lineZeroEtaleMap V)

/-- The bounded-below pro-etale target, with the existing compactification functor.
Source: blueprint Step 1, target of tau (blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroCompactTarget (V : PurityVectorBundle P B b 1) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)) :=
  (ProEtale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
    (P.lineZeroProTarget V.E)

/-- The retained target witness. The comparison is the specified compact-support site
comparison and the prescribed root-chart target comparison, including D+ compatibility.
Source: blueprint Step 1, bounded-below etale-origin witness
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroTargetWitness (V : PurityVectorBundle P B b 1) :
    Scheme.FixedEtaleOriginWitness B P.Coefficient (lineZeroCompactTarget V) where
  complex := (Etale.rightDerivedLowerShriekPlus
    (ModuleCat.{u + 1} P.Coefficient) V.p).obj (P.lineZeroEtaleTarget V.E)
  iso := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekPlusCompatibility
        (ModuleCat.{u + 1} P.Coefficient) V.p).app (P.lineZeroEtaleTarget V.E)) ≪≫
    ((compactSupportSiteComparison P.Coefficient
      (HasCompactification.compactification V.p)).app (P.lineZeroEtaleTarget V.E)).symm ≪≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).mapIso
      (P.lineZeroTwistComparison V.E) ≪≫
    ((ProEtale.rightDerivedLowerShriekPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) V.p).app (P.lineZeroProTarget V.E)).symm


/-- The source component of compact-support site comparison, including supported
constants. This is fixed before imposing its identity-normalization equation.
Source: blueprint Step 1, beta_(z_*A_B)
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroCompactSourceComparison (V : PurityVectorBundle P B b 1) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (lineZeroEtaleSource V)).obj ≅
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (lineZeroProSource V).obj :=
  closedSectionBeta P V.p V.zeroSection

/-- The retained source witness is the constant etale complex with the canonical
constant comparison. Source: blueprint Step 1, source A_B
(blueprint: lem-pur-line-zero-class-etale-realization). -/
def lineZeroSourceWitness (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Scheme.FixedEtaleOriginWitness T P.Coefficient (P.lineZeroProUnit T) where
  complex := P.lineZeroEtaleUnit T
  iso := P.lineZeroUnitComparison T

private theorem lineZeroTransport {C D E H : Type*}
    [Category* C] [Category* D] [Category* E] [Category* H]
    (F : C ⥤ D) (N : D ⥤ H) (Q : C ⥤ E) (G : E ⥤ H)
    (β : F ⋙ N ≅ Q ⋙ G) {S T : C} {S' T' : E} {U : D} {U' : H}
    (σe : F.obj S ≅ U) (σp : G.obj S' ≅ U') (χ : N.obj U ≅ U')
    (ε : Q.obj S ≅ S') (θ : Q.obj T ≅ T') (ce : S ⟶ T) (cp : S' ⟶ T')
    (hs : N.map σe.hom ≫ χ.hom = β.hom.app S ≫ G.map ε.hom ≫ σp.hom)
    (hm : Q.map ce ≫ θ.hom = ε.hom ≫ cp) :
    N.map (σe.inv ≫ F.map ce) ≫ β.hom.app T ≫ G.map θ.hom =
      χ.hom ≫ σp.inv ≫ G.map cp := by
  have hi : N.map σe.inv ≫ β.hom.app S ≫ G.map ε.hom = χ.hom ≫ σp.inv := by
    apply (cancel_mono σp.hom).1
    rw [Category.assoc, Category.assoc, ← hs]
    simp only [← Category.assoc, ← N.map_comp, σe.inv_hom_id, N.map_id,
      Category.id_comp]
    simp only [Category.assoc, σp.inv_hom_id, Category.comp_id]
  have hn : N.map (F.map ce) ≫ β.hom.app T =
      β.hom.app S ≫ G.map (Q.map ce) := β.hom.naturality ce
  rw [N.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  change N.map σe.inv ≫ β.hom.app S ≫ G.map (Q.map ce) ≫ G.map θ.hom = _
  rw [← G.map_comp, hm, G.map_comp]
  simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ G.map cp) hi

private theorem lineZeroSupportedSquare (V : PurityVectorBundle P B b 1) :
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategory.map
        (lineZeroEtaleMap V).hom ≫ (P.lineZeroTwistComparison V.E).hom =
      (lineZeroSupportedComparison V).hom ≫ (lineZeroProMap V).hom) := by
  exact P.cartierSupported_comparison_square (V.p ≫ b) V.zeroSection (lineZeroIdeal V)



/-- The global zero-divisor class is the supported Cartier Kummer map, its coordinate
class is minus the frame boundary, and both the supported map and its compact image
are the specified etale realizations. The final equation is a witness for the actual
arrow tau with the specified source and target identifications.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 1; expanded DAG proof steps 1--7
(blueprint: lem-pur-line-zero-class-etale-realization).

Proof:
1. Use line_zero_geometry: relative-Spec affine frames and projective completion
   give the finiteness and compactification facts. The equations t=0 give Cartier
   ideals over arbitrary base changes, smoothness, and pure codimension one.
2. The coefficient exponent is ell^n, which kills A since ell lies in (varpi).
   The finite etale root line is flat, so its derived scalar extension is its
   ordinary degree-zero tensor, even for ramified coefficients not flat over Z/N.
   FiniteTateSiteDescent and the def-pur-frame-class projection give the stipulated
   root chart of the existing pro-etale twist.
3. ordinary_supported_kummer normalizes the etale class by SupportedKummerBoundary.
   cartier_kummer_map realizes precisely this relative construction. Their unique
   normalizations identify it with agreementCartierEtale and agreementCartierMap;
   the exact single and shift comparisons give the displayed supported square.
4. Apply divisor_class and cartier_class_agreement to the zero Cartier divisor.
   Uniqueness identifies its relative family with generalDivisorEtaleClasses.
   DivisorLocalEquations gives minus the individual frame boundary in every
   principal bundle coordinate, with the Yoneda sign of the relative torsor.
5. For z use the identity/proper compactification and exact closed pushforward
   on both sites (closedFiniteAdjointCounitTransport and the pro-etale closed
   exactness theorem). The etale and origin compositors for z followed by pi,
   the section equality, and their identity normalizations are exactly the
   two source isomorphisms defined above.
6. Naturality of compactSupportSiteComparison at c^e gives the compact-support
   square. compactSupportSiteCoherence for composition and identity gives its
   displayed normalized source equation; insert the supported square from step 3.
7. Both etale input objects lie in D+, and etale compact support preserves D+.
   The constructed FixedEtaleOriginWitness objects retain those antecedents and
   the exact comparison isomorphisms. Substitution of the normalized source
   equation gives the final equality for lineZeroTau itself. -/
theorem line_zero_class_etale_realization (V : PurityVectorBundle P B b 1) :
    P.generalDivisorClass (V.p ≫ b) V.zeroSection (lineZeroIdeal V) =
      P.agreementCartierMap (V.p ≫ b) V.zeroSection (lineZeroIdeal V) ∧
    P.DivisorLocalEquations (V.p ≫ b) (P.generalDivisorEtaleClasses V.E (V.p ≫ b))
      V.zeroSection (lineZeroIdeal V) ∧
    Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates V.zeroSection (lineZeroIdeal V)
      (P.diagonalExponent_isUnit (V.p ≫ b))
      (P.agreementCartierEtale (V.p ≫ b) V.zeroSection (lineZeroIdeal V)) ∧
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategory.map
        (lineZeroEtaleMap V).hom ≫ (P.lineZeroTwistComparison V.E).hom =
      (lineZeroSupportedComparison V).hom ≫ (lineZeroProMap V).hom) ∧
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (lineZeroEtaleSourceIso V).hom) ≫
        (P.lineZeroUnitComparison B).hom =
      (lineZeroCompactSourceComparison V).hom ≫ (lineZeroProSourceIso V).hom) ∧
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (lineZeroEtaleTau V)) ≫
        (lineZeroTargetWitness V).iso.hom =
      (P.lineZeroSourceWitness B).iso.hom ≫ lineZeroTau V ≫
        ((ProEtale.rightDerivedLowerShriekPlusCompatibility
          (ModuleCat.{u + 1} P.Coefficient) V.p).app (P.lineZeroProTarget V.E)).inv)  := by
  have hgeom := line_zero_geometry V
  let : SmoothOfRelativeDimension 1 V.p := hgeom.2.2.2.1
  let : SmoothOfRelativeDimension 0 (V.zeroSection ≫ V.p) := hgeom.2.2.2.2.2.1
  let : Smooth (V.zeroSection ≫ V.p) := SmoothOfRelativeDimension.smooth 0 _
  have hdim := hgeom.2.2.2.2.2.2.2.1
  have hcart := P.relativeCartierKummer_realization b V.p 1 V.zeroSection
    (lineZeroIdeal V) hdim
  obtain ⟨C, hC, _, _, hlocal, _, _⟩ :=
    P.divisor_class b V.p 1 V.zeroSection hdim
  have hCe : C = P.generalDivisorEtaleClasses V.E (V.p ≫ b) :=
    (P.existsUnique_generalDivisorEtaleClasses V.E (V.p ≫ b)).choose_spec.2 C hC
  subst C
  have : IsNoetherian V.E := isNoetherian_of_locallyOfFiniteType (V.p ≫ b)
  have hmap := lineZeroSupportedSquare V
  have hsource :
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (lineZeroEtaleSourceIso V).hom) ≫
        (P.lineZeroUnitComparison B).hom =
      (lineZeroCompactSourceComparison V).hom ≫ (lineZeroProSourceIso V).hom := by
    exact P.comparisonImage_closed_section_normalization b V.p V.zeroSection
      V.zeroSection_spec.1
  refine ⟨hcart.2.2.2.1, hlocal, hcart.1, hmap, hsource, ?_⟩
  let F := Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p
  let N := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let Q := DerivedCategory.Plus.ι ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategory
  let G := ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p
  let β : F ⋙ DerivedCategory.Plus.ι ⋙ N ≅ Q ⋙ G :=
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) V.p) N ≪≫
      (compactSupportSiteComparison P.Coefficient
        (HasCompactification.compactification V.p)).symm
  have ht := lineZeroTransport (F ⋙ DerivedCategory.Plus.ι) N Q G β
    (S := lineZeroEtaleSource V) (T := P.lineZeroEtaleTarget V.E)
    (S' := (lineZeroProSource V).obj) (T' := (P.lineZeroProTarget V.E).obj)
    (DerivedCategory.Plus.ι.mapIso (lineZeroEtaleSourceIso V))
    (lineZeroProSourceIso V) (P.lineZeroUnitComparison B)
    (lineZeroSupportedComparison V) (P.lineZeroTwistComparison V.E)
    (lineZeroEtaleMap V) (lineZeroProMap V).hom
    (by simpa only [lineZeroCompactSourceComparison, closedSectionBeta,
      closedSectionSe, closedSectionEpsilon, lineZeroSupportedComparison,
      lineZeroEtaleSource, β, Iso.trans_hom, Iso.app_inv,
      Iso.app_hom, Functor.mapIso_hom, Functor.isoWhiskerRight_hom,
      F, N, Q, G, NatTrans.comp_app,
      Functor.whiskerRight_app, Iso.symm_hom, Category.assoc] using hsource) hmap
  simpa only [lineZeroEtaleTau, lineZeroTau, lineZeroTargetWitness,
    lineZeroSourceWitness, β, F, N, Q, G, CategoryTheory.Functor.map_comp, Iso.trans_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.comp_map, Category.assoc]
    using congrArg (fun t ↦ t ≫
      ((ProEtale.rightDerivedLowerShriekPlusCompatibility
        (ModuleCat.{u + 1} P.Coefficient) V.p).app (P.lineZeroProTarget V.E)).inv) ht

end WeilConjectures.PurityFiniteSetting
