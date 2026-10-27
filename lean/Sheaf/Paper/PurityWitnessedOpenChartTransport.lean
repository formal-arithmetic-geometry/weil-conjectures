/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FixedEtaleOriginDerivedCategory
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.EtaleCoefficientSystemAdjoint
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

/-! # Normalized witnessed open chart transport

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
thm-pur-general-admissibility.proof.md, Steps 1 and 3, expanded in Q24's
retained argument, Steps 1--2 and 6--9
(blueprint: lem-pur-witnessed-open-chart-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.PurityWitnessedChart

/-- The coefficient ring of the fixed finite purity setting is finite.
Source: finite purity conventions and coefficient-extension finiteness
(blueprint: lem-pur-witnessed-open-chart-transport). -/
instance coefficientFinite (S : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite S.Coefficient :=
  letI : Finite S.Ring :=
    Padic.finite_coefficientExtensionRing S.coefficients.l S.extension S.level S.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} S.Ring))

variable (A : Type (u + 1)) [CommRing A]

/-- Ordinary etale derived category. Source: the displayed Hom chain
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev Et (T : Scheme.{u}) := Etale.DerivedCategoryModule A T

/-- Ordinary pro-etale derived category. Source: the witnessed chart formula
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev Pr (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- Exact comparison pullback, applied termwise. Source: the displayed C_T
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev compare (T : Scheme.{u}) : Et A T ⥤ Pr A T :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- Derived comparison direct image. Source: the displayed R nu_*
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev recover (T : Scheme.{u}) : Pr A T ⥤ Et A T :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor

/-- Termwise etale inverse image. Source: the displayed j_e^*
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev etPull {W Z : Scheme.{u}} (j : W ⟶ Z) : Et A Z ⥤ Et A W :=
  (Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- Termwise pro-etale inverse image. Source: the displayed Lj^*=j^*
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev prPull {W Z : Scheme.{u}} (j : W ⟶ Z) : Pr A Z ⥤ Pr A W :=
  (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- Localization of the canonical inverse-image comparison, with the exact-functor
composition identifications. Source: Step 3 of the retained argument
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def kappa {W Z : Scheme.{u}} (j : W ⟶ Z) :
    etPull A j ⋙ compare A W ≅ compare A Z ⋙ prPull A j :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@id (Etale.upperStar (ModuleCat.{u + 1} A) j ⋙
          comparisonUpperStar (ModuleCat.{u + 1} A) W ≅
        comparisonUpperStar (ModuleCat.{u + 1} A) Z ⋙
          upperStar (ModuleCat.{u + 1} A) j)
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical witnessed open restriction. Both antecedents are transported
termwise, and the witness is kappa followed by pullback of the given isomorphism.
Its arrow map is the ordinary pullback on every underlying pro-etale arrow.
Source: retained argument Step 3
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def openLift {W Z : Scheme.{u}} (j : W ⟶ Z) :
    FixedEtaleOriginDerivedCategory Z A ⥤ FixedEtaleOriginDerivedCategory W A where
  obj N := ⟨(upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj N.1,
    ⟨(Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj N.2.complex,
      (kappa A j).app N.2.complex.obj ≪≫ (prPull A j).mapIso N.2.iso⟩⟩
  map h := InducedCategory.homMk
    ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map h.hom)
  map_id N := by ext; simp
  map_comp h k := by ext; simp

/-- Canonical identity comparison for termwise pro-etale pullback.
Source: open restriction identity (blueprint: lem-pur-witnessed-open-chart-transport). -/
def prId (Z : Scheme.{u}) : prPull A (𝟙 Z) ≅ 𝟭 (Pr A Z) :=
  Functor.mapDerivedCategoryNatIso
    (@id (upperStar (ModuleCat.{u + 1} A) (𝟙 Z) ≅ 𝟭 _)
      (supportSiteProEtaleComparisonId (ModuleCat.{u + 1} A) Z)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Canonical composition comparison for termwise pro-etale pullback.
Source: successive open restriction
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def prComp {U W Z : Scheme.{u}} (h : U ⟶ W) (j : W ⟶ Z) :
    prPull A (h ≫ j) ≅ prPull A j ⋙ prPull A h :=
  Functor.mapDerivedCategoryNatIso
    (@id (upperStar (ModuleCat.{u + 1} A) (h ≫ j) ≅
        upperStar (ModuleCat.{u + 1} A) j ⋙ upperStar (ModuleCat.{u + 1} A) h)
      (supportSiteProEtaleComparisonComp (ModuleCat.{u + 1} A) h j)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

variable [Finite A]

/-- Ordinary right adjoint at the chosen compactification. Source: H_v^c
(blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev right {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Et A Y ⥤ Et A X :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- Its specified ordinary etale adjunction. Source: the normalized Hom chain
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def adj {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ right A c :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint _

/-- The exceptional functor is the recorded C H R composite at this compactification.
Source: G_v^c in the statement (blueprint: lem-pur-witnessed-open-chart-transport). -/
abbrev exceptional {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Pr A Y ⥤ Pr A X :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  sfFiniteExceptionalAt A c

/-- The inverse image of an identity, localized termwise.
Source: identity normalization of the Hom chain
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def etId (V : Scheme.{u}) : etPull A (𝟙 V) ≅ 𝟭 (Et A V) :=
  Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} A) V) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Use the chosen compact-support adjunction through its canonical refinement comparison.
Source: ordinary adjunctions in the displayed Hom chain
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def chosenAdj {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    [HasCompactification f] (c : Compactification f) :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ right A c :=
  (adj A c).ofNatIsoLeft (Etale.rightDerivedLowerShriekIso A c)

/-- The normalized Hom chain at arbitrary supplied compactifications. The existing
chart comparison is specialized with base open id_V, followed by its canonical
identity-pullback normalization. Thus the i_* and compact-support compositor are
exactly those of the ordinary etale chart theorem.
Source: retained argument Step 5 (blueprint: lem-pur-witnessed-open-chart-transport). -/
def homChain {U X T V : Scheme.{u}} (f : X ⟶ V) (j : U ⟶ X)
    (i : U ⟶ T) (p : T ⟶ V) [IsOpenImmersion j] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [QuasiCompact j]
    (w : j ≫ f = i ≫ p) (cf : Compactification f)
    (ci : Compactification i) (cp : Compactification p)
    (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (N : Et A V) :
    (H.obj ⟶ (etPull A j).obj ((right A cf).obj N)) ≃
      (H.obj ⟶ (right A ci).obj ((right A cp).obj N)) :=
  letI := cf.hasCompactification
  letI := ci.hasCompactification
  letI := cp.hasCompactification
  letI := (Compactification.ofIsOpenImmersion j).hasCompactification
  letI := (Compactification.ofIsProper (𝟙 V)).hasCompactification
  let cjf := cf.precomp j
  let cip := cjf.copy w.symm
  letI := cjf.hasCompactification
  letI := cip.hasCompactification
  letI := (cip.copy (f' := i ≫ p ≫ 𝟙 V) (by simp)).hasCompactification
  letI := (cip.copy (f' := (i ≫ p) ≫ 𝟙 V) (by simp only [Category.comp_id])).hasCompactification
  (Etale.ChartAdjointComparison.homChain A f j (𝟙 V) i p
    (by simpa only [Category.comp_id] using w)
    (right A cf) (right A cp) (right A ci)
    (chosenAdj A cf) (chosenAdj A cp) (chosenAdj A ci) H N).trans
      (Iso.homCongr (Iso.refl H.obj)
        ((right A ci).mapIso ((right A cp).mapIso ((etId A V).app N))))

/-- The witness-unit map N_e -> R nu_* N is literally eta followed by R nu_* beta.
Source: retained argument Step 7
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def witnessUnit {V : Scheme.{u}} (N : FixedEtaleOriginDerivedCategory V A) :
    N.2.complex.obj ⟶ (recover A V).obj N.1.obj :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} A) V).unit.app N.2.complex.obj ≫
    (recover A V).map N.2.iso.hom

/-- The unit-induced identification C H N_e -> G N, before asserting invertibility.
Source: s_v in retained argument Step 7
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def witnessExceptional {X V : Scheme.{u}} {f : X ⟶ V} (c : Compactification f)
    (N : FixedEtaleOriginDerivedCategory V A) :
    (compare A X).obj ((right A c).obj N.2.complex.obj) ⟶
      (exceptional A c).obj N.1.obj :=
  (compare A X).map ((right A c).map (witnessUnit A N))

/-- The source witness map, kappa followed by j^* of the first unit identification.
Source: q_N in retained argument Step 7
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def sourceWitness {U X V : Scheme.{u}} {f : X ⟶ V} (j : U ⟶ X)
    (cf : Compactification f) (N : FixedEtaleOriginDerivedCategory V A) :
    (compare A U).obj ((etPull A j).obj ((right A cf).obj N.2.complex.obj)) ⟶
      (prPull A j).obj ((exceptional A cf).obj N.1.obj) :=
  (kappa A j).hom.app ((right A cf).obj N.2.complex.obj) ≫
    (prPull A j).map (witnessExceptional A cf N)

/-- The target witness includes the second comparison unit at H_pi N_e.
Source: t_N in retained argument Step 7
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def targetWitness {U T V : Scheme.{u}} {i : U ⟶ T} {p : T ⟶ V}
    (ci : Compactification i) (cp : Compactification p)
    (N : FixedEtaleOriginDerivedCategory V A) :
    (compare A U).obj ((right A ci).obj ((right A cp).obj N.2.complex.obj)) ⟶
      (exceptional A ci).obj ((exceptional A cp).obj N.1.obj) :=
  (compare A U).map ((right A ci).map
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        ((right A cp).obj N.2.complex.obj) ≫
      (recover A T).map (witnessExceptional A cp N)))

/-- The conclusions for a factored chart, with all choices normalized. Geometry and
boundedness are conclusions, not extra assumptions on exceptional images. The two
lifts retain Q and B and their exact unit-induced maps. A natural isomorphism in the
induced category quantifies over every underlying pro-etale arrow.
Source: the chart assertion, retained argument Steps 1--2 and 4--8
(blueprint: lem-pur-witnessed-open-chart-transport). -/
structure ChartTransportData {U X T V : Scheme.{u}}
    (f : X ⟶ V) (j : U ⟶ X) (i : U ⟶ T) (p : T ⟶ V)
    [IsOpenImmersion j] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (w : j ≫ f = i ≫ p) (cf : Compactification f)
    (ci : Compactification i) (cp : Compactification p) where
  /-- All four schemes are Noetherian. -/
  noetherian : IsNoetherian U ∧ IsNoetherian X ∧ IsNoetherian T ∧ IsNoetherian V
  /-- The open immersion is quasi-compact. -/
  j_qc : QuasiCompact j
  /-- The projection is separated. -/
  p_sep : IsSeparated p
  /-- The projection is locally of finite type. -/
  p_ft : LocallyOfFiniteType p
  /-- The projection is quasi-compact. -/
  p_qc : QuasiCompact p
  /-- H_f preserves bounded-below inputs. -/
  plusF : ∀ N : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
    DerivedCategory.TStructure.t.plus ((right A cf).obj N.obj)
  /-- H_pi preserves bounded-below inputs. -/
  plusP : ∀ N : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
    DerivedCategory.TStructure.t.plus ((right A cp).obj N.obj)
  /-- The composite H_i H_pi is bounded below. -/
  plusIP : ∀ N : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
    DerivedCategory.TStructure.t.plus ((right A ci).obj ((right A cp).obj N.obj))
  /-- Q is bounded below. -/
  plusQ : ∀ N : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
    DerivedCategory.TStructure.t.plus ((etPull A j).obj ((right A cf).obj N.obj))
  /-- The ordinary etale derived natural isomorphism Q ~= B. -/
  a : DerivedCategory.Plus.ι ⋙ right A cf ⋙ etPull A j ≅
    DerivedCategory.Plus.ι ⋙ right A cp ⋙ right A ci
  /-- Postcomposition with a is precisely the specified Hom chain. -/
  normalization : ∀ (N : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (t : H.obj ⟶ (etPull A j).obj ((right A cf).obj N.obj)),
    @homChain A _ _ U X T V f j i p _ _ _ _ _ p_sep p_ft p_qc j_qc
      w cf ci cp H N.obj t = t ≫ a.hom.app N
  /-- The normalization uniquely determines the representing isomorphism. -/
  unique : ∀ (N : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (b : (etPull A j).obj ((right A cf).obj N.obj) ≅
        (right A ci).obj ((right A cp).obj N.obj)),
    (∀ (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (t : H.obj ⟶ (etPull A j).obj ((right A cf).obj N.obj)),
      @homChain A _ _ U X T V f j i p _ _ _ _ _ p_sep p_ft p_qc j_qc
        w cf ci cp H N.obj t = t ≫ b.hom) → b = a.app N
  /-- The first witness unit is invertible. -/
  unit_iso : ∀ N : FixedEtaleOriginDerivedCategory V A, IsIso (witnessUnit A N)
  /-- G_f has the unit-induced witness identification. -/
  f_iso : ∀ N : FixedEtaleOriginDerivedCategory V A,
    IsIso (witnessExceptional A cf N)
  /-- G_pi has the unit-induced witness identification. -/
  p_iso : ∀ N : FixedEtaleOriginDerivedCategory V A,
    IsIso (witnessExceptional A cp N)
  /-- The second unit is used at the bounded-below object H_pi N_e. -/
  second_unit_iso : ∀ N : FixedEtaleOriginDerivedCategory V A,
    IsIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      ((right A cp).obj N.2.complex.obj))
  /-- The source functor with its retained Q witness. -/
  source : FixedEtaleOriginDerivedCategory V A ⥤ FixedEtaleOriginDerivedCategory U A
  /-- Its action on every underlying arrow is j^* G_f. -/
  source_underlying : source ⋙ fixedEtaleOriginForgetful U A =
    fixedEtaleOriginForgetful V A ⋙ exceptional A cf ⋙ prPull A j
  /-- Its etale witness is Q. -/
  source_complex : ∀ N, (source.obj N).2.complex.obj =
    (etPull A j).obj ((right A cf).obj N.2.complex.obj)
  /-- Its witness isomorphism is exactly q_N. -/
  source_iso : ∀ N, HEq (source.obj N).2.iso.hom (sourceWitness A j cf N)
  /-- The target functor with its retained B witness. -/
  target : FixedEtaleOriginDerivedCategory V A ⥤ FixedEtaleOriginDerivedCategory U A
  /-- Its action on every underlying arrow is G_i G_pi. -/
  target_underlying : target ⋙ fixedEtaleOriginForgetful U A =
    fixedEtaleOriginForgetful V A ⋙ exceptional A cp ⋙ exceptional A ci
  /-- Its etale witness is B. -/
  target_complex : ∀ N, (target.obj N).2.complex.obj =
    (right A ci).obj ((right A cp).obj N.2.complex.obj)
  /-- Its witness isomorphism is exactly t_N. -/
  target_iso : ∀ N, HEq (target.obj N).2.iso.hom (targetWitness A ci cp N)
  /-- The witnessed derived natural isomorphism, on all induced-category arrows. -/
  chart : source ≅ target
  /-- Conjugation by q_N,t_N identifies the chart map with C_U a_N. -/
  chart_normalization : ∀ N, HEq
    ((source.obj N).2.iso.hom ≫
      (fixedEtaleOriginForgetful U A).map (chart.hom.app N))
    ((compare A U).map (a.hom.app N.2.complex) ≫ targetWitness A ci cp N)

/-- Canonical composition comparison for termwise etale pullback.
Source: successive open restriction
(blueprint: lem-pur-witnessed-open-chart-transport). -/
def etComp {U W Z : Scheme.{u}} (h : U ⟶ W) (j : W ⟶ Z) :
    etPull A (h ≫ j) ≅ etPull A j ⋙ etPull A h :=
  Functor.mapDerivedCategoryNatIso
    (@id (Etale.upperStar (ModuleCat.{u + 1} A) (h ≫ j) ≅
        Etale.upperStar (ModuleCat.{u + 1} A) j ⋙
          Etale.upperStar (ModuleCat.{u + 1} A) h)
      (supportSiteEtaleComparisonComp (ModuleCat.{u + 1} A) h j)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Open restriction is exact on both sites, preserves every lower bound, and
transports the retained antecedent by the canonical comparison. Identity and
successive restrictions commute with both the underlying objects and witnesses.
Source: blueprint thm-pur-general-admissibility.proof.md Steps 1 and 3;
retained argument Step 3 (blueprint: lem-pur-witnessed-open-chart-transport).

Proof: the two constant-module inverse images are exact, so termwise pullback
preserves quasi-isomorphisms and computes cohomology by pulling back kernels and
images. Thus the same lower bound is retained and the left derived functor is
this exact functor. For a triple use j_e^* N_e and kappa followed by j^* beta,
exactly as in openLift; map every underlying arrow by j^*. The functor laws are
those of pullback. The comparison-pullback identity and composition laws give
the displayed witness equations. Lift the ordinary derived identity and composition
isomorphisms through the fully faithful induced category to obtain the stated
natural isomorphisms on all arrows. No constructibility hypothesis is used. -/
theorem open_restriction (S : WeilConjectures.PurityFiniteSetting.{u})
    (W Z : Over (Spec (.of S.field.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (j : W ⟶ Z) [IsOpenImmersion j.left] :
    (PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} S.Coefficient) j.left) ∧
      PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} S.Coefficient) j.left)) ∧
    (PreservesFiniteLimits (upperStar (ModuleCat.{u + 1} S.Coefficient) j.left) ∧
      PreservesFiniteColimits (upperStar (ModuleCat.{u + 1} S.Coefficient) j.left)) ∧
    Nonempty ((upperStar (ModuleCat.{u + 1} S.Coefficient) j.left).leftDerivedFunctor ≅
      prPull S.Coefficient j.left) ∧
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} S.Coefficient) j.left).leftDerivedFunctor ≅
      etPull S.Coefficient j.left) ∧
    (∀ (K : Et S.Coefficient Z.left) (n : ℤ), K.IsGE n →
      ((etPull S.Coefficient j.left).obj K).IsGE n) ∧
    (∀ (K : Pr S.Coefficient Z.left) (n : ℤ), K.IsGE n →
      ((prPull S.Coefficient j.left).obj K).IsGE n) ∧
    (∃ e : openLift S.Coefficient (𝟙 Z.left) ≅
        𝟭 (FixedEtaleOriginDerivedCategory Z.left S.Coefficient),
      (∀ N, (fixedEtaleOriginForgetful Z.left S.Coefficient).map (e.hom.app N) =
        (prId S.Coefficient Z.left).hom.app N.1.obj) ∧
      (∀ N : FixedEtaleOriginDerivedCategory Z.left S.Coefficient,
        ((openLift S.Coefficient (𝟙 Z.left)).obj N).2.iso.hom ≫
            (prId S.Coefficient Z.left).hom.app N.1.obj =
          (compare S.Coefficient Z.left).map
              ((etId S.Coefficient Z.left).hom.app N.2.complex.obj) ≫ N.2.iso.hom)) ∧
    (∀ (U : Over (Spec (.of S.field.k)))
        [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
        (h : U ⟶ W) [IsOpenImmersion h.left],
      ∃ e : openLift S.Coefficient (h.left ≫ j.left) ≅
          openLift S.Coefficient j.left ⋙ openLift S.Coefficient h.left,
        (∀ N, (fixedEtaleOriginForgetful U.left S.Coefficient).map (e.hom.app N) =
          (prComp S.Coefficient h.left j.left).hom.app N.1.obj) ∧
        (∀ N : FixedEtaleOriginDerivedCategory Z.left S.Coefficient,
          ((openLift S.Coefficient (h.left ≫ j.left)).obj N).2.iso.hom ≫
              (prComp S.Coefficient h.left j.left).hom.app N.1.obj =
            (compare S.Coefficient U.left).map
                ((etComp S.Coefficient h.left j.left).hom.app N.2.complex.obj) ≫
              ((openLift S.Coefficient h.left).obj
                ((openLift S.Coefficient j.left).obj N)).2.iso.hom)) := by
  sorry

/-- The normalized affine-chart comparison exists on arbitrary bounded-below
etale-origin inputs, with its specified witnesses and naturality on all underlying
pro-etale arrows. No separated structure morphism for X and no constructibility
or finite-Tor assumptions occur.
Source: blueprint thm-pur-general-admissibility.proof.md Steps 1 and 3, and the
retained Q24 chart argument Steps 1--2 and 6--9
(blueprint: lem-pur-witnessed-open-chart-transport).

Proof, following the eight DAG steps:
1. Finite type over the Noetherian field makes X,V Noetherian. Open restriction
makes U Noetherian; the polynomial affine space T is finite type and Noetherian.
All are qcqs, using locally-Noetherian quasi-separatedness.
2. The open immersion j is quasi-compact because inverse images of affine opens
are opens in a Noetherian space, hence finite type. The closed immersion is proper;
the affine-space projection is separated finite type. Composites are separated
finite type, so Nagata gives their compactifications without separatedness of X/k.
3. Apply open_restriction, using the exact comparison to retain every witness.
4. The coefficient-system adjoint's uniform lower bound and evaluation comparison,
applied to the strict system zero below n and constantly N_e above n, prove that
H_f, H_pi and H_i H_pi take these inputs to D+. Exact open pullback gives Q in D+.
5. Specialize lem-sf-etale-chart-adjoint-comparison to base open id_V; its normalized
compositor and the open, exceptional and closed adjunctions give homChain.
6. Evaluate that chain at 1_Q and its inverse at 1_B. Naturality gives inverse
maps and uniqueness; naturality in N_e gives the ordinary derived natural iso a.
7. Use eta followed by R nu_* beta to obtain s_f,s_pi. Define q_N and t_N by the
two displayed unit formulas, including the second unit at H_pi N_e. These are
invertible by the comparison theorem on D+. They retain Q and B as witnesses.
8. Every underlying pro-etale arrow has a unique etale lift by full faithfulness
of comparison on D+. Unit naturality gives G_v(h) s_v = s'_v C H_v(phi).
Combining this for f and pi with kappa and the second unit proves the q,t squares.
Conjugating C_U a by q,t is therefore natural on every underlying arrow and is the
required witnessed isomorphism. Zero objects, empty charts, d=0 and n=1 are included. -/
theorem witnessed_open_chart_transport (S : WeilConjectures.PurityFiniteSetting.{u})
    (X V : Over (Spec (.of S.field.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsAffine V.left]
    (f : X ⟶ V) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (U : Scheme.{u}) [IsAffine U] (j : U ⟶ X.left) [IsOpenImmersion j]
    (d : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V.left) [IsClosedImmersion i]
    (w : j ≫ f.left = i ≫ (AffineSpace (ULift.{u} (Fin d)) V.left ↘ V.left))
    (cf : Compactification f.left) (ci : Compactification i)
    (cp : Compactification (AffineSpace (ULift.{u} (Fin d)) V.left ↘ V.left)) :
    Nonempty (ChartTransportData S.Coefficient f.left j i
      (AffineSpace (ULift.{u} (Fin d)) V.left ↘ V.left) w cf ci cp) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityWitnessedChart
