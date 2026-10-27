/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Sheaf.Paper.DegreeZeroCompactSupportSections
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.Compactification.Dense
import Sheaf.Compactification.BoundaryRefinement
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.Paper.AdicSectionClosedSupport

/-! # Constructible degree-zero sections with proper support

Source: Milne, Lectures on Etale Cohomology, Definition 18.1 and Proposition 18.3(b);
Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-a1-constructible-degree-zero-proper-support).

The completed-model comparison below is the derived adjunction mate of the inverse
open-extension unit. Thus the compact comparison is specified before rationalization.

## Main definitions

* `a1ConstructibleCompletedComparison`: the completed open-adjunction mate.
* `a1ConstructibleModelRestriction`: ordinary restriction on every integral model.
* `A1ConstructibleDegreeZeroComparison`: natural sections and proper support.
* `A1ConstructibleLisseCompatibility`: the ordinary lisse realization squares.

## Main statements

* `a1ConstructibleDegreeZeroProperSupport`: the general constructible comparison.
* `a1ConstructibleDegreeZeroProperSupport_lisse`: its lisse normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The unit for exact extension by zero is invertible, also after deriving.
Source: Milne 18.1; Stacks 03DI
(blueprint: lem-a1-constructible-degree-zero-proper-support).
Proof: restricting the extension-by-zero presheaf to the open recovers the original
presheaf and its identity section map. Sheafification preserves this identity.
The underived unit is therefore invertible. Exact descent to complexes and then the
derived localization carries this same unit to openDerivedAdjunction's unit. -/
theorem a1ConstructibleOpenUnit_isIso {X T : Scheme.{u}} (j : X ⟶ T)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X)) :
    IsIso ((openDerivedAdjunction (completed l E) j).unit.app K) := by
  sorry

/-- The completed comparison j_! → Rj_* is the mate of the inverse open unit.
Source: Milne 18.1 and 18.3(b)
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleCompletedOpenComparison {X T : Scheme.{u}} (j : X ⟶ T)
    [IsOpenImmersion j] :
    (openExtension (completed l E) j).mapDerivedCategory ⟶ push (completed l E) j := by
  let J := (openExtension (completed l E) j).mapDerivedCategory
  let A := proEtaleRingDerivedAdjunction j ((completed l E).ring T)
    ((completed l E).ring X) ((completed l E).pull j)
  letI := fun K ↦ a1ConstructibleOpenUnit_isIso l E j K
  letI : IsIso (openDerivedAdjunction (completed l E) j).unit :=
    NatIso.isIso_of_isIso_app _
  exact Functor.whiskerLeft J A.unit ≫
    Functor.whiskerRight (inv (openDerivedAdjunction (completed l E) j).unit)
      (push (completed l E) j)

/-- Completed direct-image pasting is conjugate to the specified pullback pasting.
Source: Stacks 03DA, 0D6E
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleCompletedPushComp {X T S : Scheme.{u}} (j : X ⟶ T) (p : T ⟶ S) :
    push (completed l E) j ⋙ push (completed l E) p ≅ push (completed l E) (j ≫ p) :=
  (conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction p ((completed l E).ring S)
      ((completed l E).ring T) ((completed l E).pull p)).comp
        (proEtaleRingDerivedAdjunction j ((completed l E).ring T)
          ((completed l E).ring X) ((completed l E).pull j)))
    (proEtaleRingDerivedAdjunction (j ≫ p) ((completed l E).ring S)
      ((completed l E).ring X) ((completed l E).pull (j ≫ p))))
    (geometricPullComposition (completed l E) j p (completedPull_comp l E j p))

/-- The canonical completed compact-to-ordinary map for the supplied compactification.
Source: Milne 18.1 and 18.3(b)
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleCompletedComparison {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Compactification f) : image (completed l E) c ⟶ push (completed l E) f :=
  Functor.whiskerRight (a1ConstructibleCompletedOpenComparison l E c.i)
      (push (completed l E) c.g) ≫
    (a1ConstructibleCompletedPushComp l E c.i c.g).hom ≫
      eqToHom (congrArg (push (completed l E)) c.comm.symm)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The scalar map from the integer model of the finite coefficient stage to Ω.
Source: BS 6.8.14, finite-stage convention
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleIntegerEmbedding (L : Padic.FiniteCoefficientFields l Ω) :
    Padic.coefficientExtensionIntegers l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) →+* Ω :=
  (sfAdicCoefficientEmbedding.{u} l Ω L).comp
    (Padic.coefficientExtensionIntegers l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).subtype

/-- Actual point sections, H⁰, coefficient down-transport and final scalar extension.
Source: blueprint ordinary/compact cohomology; BS 6.8.14
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructiblePointH0 (L : Padic.FiniteCoefficientFields l Ω) :
    DerivedCategory (scalarReductionSource l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (Spec (.of D.k))) ⥤
      ModuleCat.{max (u + 1) v} Ω := by
  letI : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionIntegers l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)))) := inferInstance
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionIntegers l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  exact pointFibreIntegralAmbient D l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) ⋙
    DerivedCategory.homologyFunctor _ 0 ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) ≃+*
        Padic.coefficientExtensionIntegers l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).symm.toRingHom ⋙
    ModuleCat.extendScalars (a1ConstructibleIntegerEmbedding.{u} l Ω L)

variable (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Finite type over a field supplies Noetherianness, including the empty scheme.
Source: Stacks 01T6 (blueprint: lem-a1-constructible-degree-zero-proper-support).
Proof: Spec(k) is Noetherian since k is a field. Local finite type makes X locally
Noetherian; quasi-compactness of its structure morphism makes X quasi-compact.
The locally Noetherian and quasi-compact criteria give IsNoetherian X. -/
theorem a1ConstructibleNoetherian (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] : IsNoetherian X := by
  sorry

/-- The coefficient unit, using the recorded common-stage constant coefficient object.
Source: blueprint ordinary/compact cohomology, coefficient object
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleUnit :=
  letI := constructiblePullbackResidueUnits D l hl X
  pullbackTensorCommonUnit l Ω X

/-- Maps from the coefficient unit, with no Weil structure on maps or targets.
Source: Milne 18.3(b); BS 6.8.14
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
abbrev A1ConstructibleSections (G : generalAlgebraicallyClosedConstructibleCategory l Ω X) :=
  a1ConstructibleUnit l D hl Ω X ⟶ G

/-- The exact common-stage restriction, with residue invertibility derived from the datum.
Source: BS 6.8.15 (blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleRestriction (U : X.Opens) :=
  letI := a1ConstructibleNoetherian D X
  letI : QuasiCompact (U.toScheme ↘ Spec (.of D.k)) := by
    change QuasiCompact (U.ι ≫ (X ↘ Spec (.of D.k)))
    infer_instance
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl U.toScheme
  commonStageDerivedPullback l Ω U.ι

/-- The coefficient unit on an arbitrary open; finite type follows from Noetherianness.
Source: Stacks 01T6; BS 6.8.15
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleOpenUnit (U : X.Opens) :=
  letI := a1ConstructibleNoetherian D X
  letI : QuasiCompact (U.toScheme ↘ Spec (.of D.k)) := by
    change QuasiCompact (U.ι ≫ (X ↘ Spec (.of D.k)))
    infer_instance
  a1ConstructibleUnit l D hl Ω U.toScheme

/-- The normalized tensor-unit equation for the open restriction.
Source: BS 6.8.14--15; Stacks 07A4
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def A1ConstructibleRestrictionUnitSpec (U : X.Opens) : Prop :=
  letI := a1ConstructibleNoetherian D X
  letI : QuasiCompact (U.toScheme ↘ Spec (.of D.k)) := by
    change QuasiCompact (U.ι ≫ (X ↘ Spec (.of D.k)))
    infer_instance
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl U.toScheme
  canonicalCommonStagePullbackTensor_unit l Ω U.ι

/-- Ordinary completed-model cohomology on every integral constructible representative.
Source: Milne 18.1; BS 6.8.14
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleModelOrdinary (L : Padic.FiniteCoefficientFields l Ω) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X ⥤
      ModuleCat.{max (u + 1) v} Ω :=
  (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).ι ⋙
    push (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
      (X ↘ Spec (.of D.k)) ⋙ a1ConstructiblePointH0 l D Ω L

/-- Compact completed-model cohomology on those same representatives.
Source: Milne 18.1; BS 6.8.14
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleModelCompact (c : Compactification (X ↘ Spec (.of D.k)))
    (L : Padic.FiniteCoefficientFields l Ω) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X ⥤
      ModuleCat.{max (u + 1) v} Ω :=
  (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).ι ⋙
    image (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) c ⋙
      a1ConstructiblePointH0 l D Ω L

/-- H⁰ of the actual completed compact-to-ordinary map, followed by scalar extension.
Source: Milne 18.3(b); BS 6.8.14
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleModelComparison (c : Compactification (X ↘ Spec (.of D.k)))
    (L : Padic.FiniteCoefficientFields l Ω) :
    a1ConstructibleModelCompact l D Ω X c L ⟶ a1ConstructibleModelOrdinary l D Ω X L :=
  Functor.whiskerLeft
    (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).ι
    (Functor.whiskerRight
      (a1ConstructibleCompletedComparison l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) c)
      (a1ConstructiblePointH0 l D Ω L))

/-- Ordinary cohomology after actual completed pullback to an arbitrary open.
Source: BS 6.8.15; Milne 18.3(b)
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleModelOpenOrdinary (U : X.Opens)
    (L : Padic.FiniteCoefficientFields l Ω) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X ⥤
      ModuleCat.{max (u + 1) v} Ω :=
  (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).ι ⋙
    pull (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) U.ι ⋙
    push (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
      (U.toScheme ↘ Spec (.of D.k)) ⋙ a1ConstructiblePointH0 l D Ω L

/-- The completed ordinary restriction is the pullback/direct-image adjunction unit,
followed by the canonical composition of direct images.
Source: Milne 18.3(b); Stacks 03DA
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleCompletedRestriction (U : X.Opens)
    (L : Padic.FiniteCoefficientFields l Ω) :
    push (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (X ↘ Spec (.of D.k)) ⟶
      pull (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) U.ι ⋙
        push (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
          (U.toScheme ↘ Spec (.of D.k)) := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  let A := proEtaleRingDerivedAdjunction U.ι ((completed l E).ring X)
    ((completed l E).ring U.toScheme) ((completed l E).pull U.ι)
  exact Functor.whiskerRight A.unit (push (completed l E) (X ↘ Spec (.of D.k))) ≫
    Functor.whiskerLeft (pull (completed l E) U.ι)
      (a1ConstructibleCompletedPushComp l E U.ι (X ↘ Spec (.of D.k))).hom

/-- H⁰ and coefficient extension of the specified ordinary restriction.
Source: Milne 18.3(b); BS 6.8.15
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleModelRestriction (U : X.Opens)
    (L : Padic.FiniteCoefficientFields l Ω) :
    a1ConstructibleModelOrdinary l D Ω X L ⟶
      a1ConstructibleModelOpenOrdinary l D Ω X U L :=
  Functor.whiskerLeft
    (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).ι
    (Functor.whiskerRight (a1ConstructibleCompletedRestriction l D Ω X U L)
      (a1ConstructiblePointH0 l D Ω L))

/-- The actual integral inclusion into the common-stage category.
Source: BS 6.8.14 (blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleModelInclusion (L : Padic.FiniteCoefficientFields l Ω) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L

/-- The canonical tensor-unit equation supplies the unit identification on every open.
Source: BS 6.8.14--15; Stacks 07A4
(blueprint: lem-a1-constructible-degree-zero-proper-support).
Proof: apply derivedPullbackTensorIso to the open immersion. Its unit clause is
canonicalCommonStagePullbackTensor_unit, with the normalized completed coefficient
unit. The residue inverses here are the ones extracted from the finite-field datum;
they are subsingletons and add no hypothesis. -/
theorem a1ConstructibleRestrictionUnit_spec (U : X.Opens) :
    A1ConstructibleRestrictionUnitSpec l D hl Ω X U := by
  sorry

/-- The unique unit comparison satisfying the canonical tensor-unit equations.
Source: BS 6.8.15 (blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleRestrictionUnit (U : X.Opens) :
    (a1ConstructibleRestriction l D hl Ω X U).obj (a1ConstructibleUnit l D hl Ω X) ≅
      a1ConstructibleOpenUnit l D hl Ω X U :=
  (a1ConstructibleRestrictionUnit_spec l D hl Ω X U).exists.choose

/-- Ordinary restriction is actual pullback of the morphism from the unit.
Source: BS 6.8.14--15 (blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleSectionRestriction (U : X.Opens)
    {G : generalAlgebraicallyClosedConstructibleCategory l Ω X}
    (s : A1ConstructibleSections l D hl Ω X G) :
    a1ConstructibleOpenUnit l D hl Ω X U ⟶
      (a1ConstructibleRestriction l D hl Ω X U).obj G :=
  (a1ConstructibleRestrictionUnit l D hl Ω X U).inv ≫
    (a1ConstructibleRestriction l D hl Ω X U).map s

/-- A carrier lift of the specified coefficient-module value; it changes no sections.
Source: blueprint coefficient-size convention
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleOrdinaryValue
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :=
  (ModuleCat.uliftFunctor.{u + 1, max u v} Ω).obj
    (adicOrdinaryCohomology D l hl X Ω K 0)

/-- The same harmless carrier lift for compact cohomology.
Source: blueprint coefficient-size convention
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleCompactValue (c : Compactification (X ↘ Spec (.of D.k)))
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :=
  (ModuleCat.uliftFunctor.{u + 1, max u v} Ω).obj
    (adicCompactCohomology D l hl X Ω c K 0)

/-- Natural comparisons on the recorded category, normalized by the actual completed
operations on every integral model at every finite coefficient field. The square
`comparisonIntegral` prescribes the compact-to-ordinary arrow before rationalization.
No independent arbitrary map between vector spaces is used.
Source: Milne 18.1 and 18.3(b); BS 6.8.14 and Remark 6.8.15
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
structure A1ConstructibleDegreeZeroComparison
    (c : Compactification (X ↘ Spec (.of D.k))) where
  /-- Ordinary cohomology with its actual finite-model action. -/
  ordinary : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
    ModuleCat.{max (u + 1) v} Ω
  /-- Compact cohomology with its actual finite-model action. -/
  compact : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
    ModuleCat.{max (u + 1) v} Ω
  /-- The values are the specified ordinary coefficient modules. -/
  ordinaryValue : ∀ K, ordinary.obj K ≅ a1ConstructibleOrdinaryValue l D hl Ω X K
  /-- The values are the specified compact coefficient modules. -/
  compactValue : ∀ K, compact.obj K ≅ a1ConstructibleCompactValue l D hl Ω X c K
  /-- Ordinary finite-model normalization, on objects and all integral maps. -/
  ordinaryIntegral : ∀ L : Padic.FiniteCoefficientFields l Ω,
    a1ConstructibleModelInclusion l Ω X L ⋙ ordinary ≅
      a1ConstructibleModelOrdinary l D Ω X L
  /-- Compact finite-model normalization, on the same objects and maps. -/
  compactIntegral : ∀ L : Padic.FiniteCoefficientFields l Ω,
    a1ConstructibleModelInclusion l Ω X L ⋙ compact ≅
      a1ConstructibleModelCompact l D Ω X c L
  /-- The natural compact-to-ordinary comparison. -/
  comparison : compact ⟶ ordinary
  /-- At every finite stage it is the derived open-adjunction comparison above. -/
  comparisonIntegral : ∀ L : Padic.FiniteCoefficientFields l Ω,
    Functor.whiskerLeft (a1ConstructibleModelInclusion l Ω X L) comparison ≫
        (ordinaryIntegral L).hom =
      (compactIntegral L).hom ≫ a1ConstructibleModelComparison l D Ω X c L
  /-- H⁰ of a heart object is ordinary Hom from the coefficient unit. -/
  sections :
    (sfCommonStageHeartProperty l X Ω).ι ⋙ ordinary ⋙
        forget (ModuleCat.{max (u + 1) v} Ω) ⋙
        uliftFunctor.{u + 2, max (u + 1) v} ≅
      (sfCommonStageHeartProperty l X Ω).ι ⋙
        coyoneda.obj (Opposite.op (a1ConstructibleUnit l D hl Ω X))
  /-- Ordinary H⁰ on each open, natural in the original constructible object. -/
  openOrdinary : ∀ _U : X.Opens,
    generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤ ModuleCat.{max (u + 1) v} Ω
  /-- Its integral-model action is actual pullback followed by derived sections. -/
  openOrdinaryIntegral : ∀ (U : X.Opens) (L : Padic.FiniteCoefficientFields l Ω),
    a1ConstructibleModelInclusion l Ω X L ⋙ openOrdinary U ≅
      a1ConstructibleModelOpenOrdinary l D Ω X U L
  /-- The natural ordinary cohomology restriction to that open. -/
  openRestriction : ∀ U : X.Opens, ordinary ⟶ openOrdinary U
  /-- This is exactly the derived adjunction-unit map on every integral model. -/
  openRestrictionIntegral : ∀ (U : X.Opens) (L : Padic.FiniteCoefficientFields l Ω),
    Functor.whiskerLeft (a1ConstructibleModelInclusion l Ω X L) (openRestriction U) ≫
        (openOrdinaryIntegral U L).hom =
      (ordinaryIntegral L).hom ≫ a1ConstructibleModelRestriction l D Ω X U L
  /-- The ordinary H⁰ section identification after pullback to the open. -/
  openSections : ∀ U : X.Opens,
    (sfCommonStageHeartProperty l X Ω).ι ⋙ openOrdinary U ⋙
        forget (ModuleCat.{max (u + 1) v} Ω) ⋙
        uliftFunctor.{u + 2, max (u + 1) v} ≅
      (sfCommonStageHeartProperty l X Ω).ι ⋙ a1ConstructibleRestriction l D hl Ω X U ⋙
        coyoneda.obj (Opposite.op (a1ConstructibleOpenUnit l D hl Ω X U))
  /-- The comparison agrees with ordinary restriction on every open, without exceptions. -/
  restrictionSections : ∀ (U : X.Opens) (G : sfCommonStageHeart l X Ω)
    (z : ordinary.obj G.obj),
    (openSections U).hom.app G (ULift.up ((openRestriction U).app G.obj z)) =
      a1ConstructibleSectionRestriction l D hl Ω X U (sections.hom.app G (ULift.up z))
  /-- The compact comparison is injective on every heart object. -/
  injective : ∀ G : sfCommonStageHeart l X Ω, Function.Injective (comparison.app G.obj)
  /-- Linearity of the Hom comparison, tested on the actual normalized adic fibres. -/
  linear : ∀ (G : sfCommonStageHeart l X Ω)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X)
    (F : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
      ModuleCat.{max (u + 1) v} Ω), SfAdicCommonFiberSpec l X x Ω F →
      F.map (sections.hom.app G (ULift.up 0)) = 0 ∧
      ∀ (a : Ω) (s t : ordinary.obj G.obj),
        F.map (sections.hom.app G (ULift.up (a • s + t))) =
          a • F.map (sections.hom.app G (ULift.up s)) + F.map (sections.hom.app G (ULift.up t))
  /-- Every compact section vanishes off a closed subset proper over the field. -/
  support : ∀ (G : sfCommonStageHeart l X Ω) (z : compact.obj G.obj),
    ∃ Z : TopologicalSpace.Closeds X,
      IsClosedSubsetProperOver (X ↘ Spec (.of D.k)) Z ∧
      a1ConstructibleSectionRestriction l D hl Ω X ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
        (sections.hom.app G (ULift.up (comparison.app G.obj z))) = 0

/-- The section map on the actual specified H_c⁰ module. The carrier lift is canonical
and the displayed value comparison gives its presentation in the natural model.
Source: Milne 18.3(b); BS 6.8.14
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
def a1ConstructibleCompactSection (c : Compactification (X ↘ Spec (.of D.k)))
    (N : A1ConstructibleDegreeZeroComparison l D hl Ω X c)
    (G : sfCommonStageHeart l X Ω)
    (z : adicCompactCohomology D l hl X Ω c G.obj 0) :
    A1ConstructibleSections l D hl Ω X G.obj :=
  N.sections.hom.app G
    (ULift.up (N.comparison.app G.obj ((N.compactValue G.obj).inv (ULift.up z))))

/-- Constructible degree-zero compact support gives a natural injective linear section
comparison with proper support. Linearity of the Hom target is expressed on adic
coefficient fibres, which are exact and jointly conservative. Restriction of these
sections to every open is the actual pullback of the unit morphism, as defined above.
The final theorem below records the existing lisse H⁰ normalization on its domain.
Source: Milne, Definition 18.1 and Proposition 18.3(b), pp. 120--121;
BS, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-a1-constructible-degree-zero-proper-support).

Proof:
1. Nagata compactification gives a quasi-compact open j:X→Xbar with proper structural
map p. The base is affine and qcqs, and X is separated of finite type. No density is used
(sk-thm-nagata-compactification; sk-def-nagata-sketch-data).
2. Adic compactification section realization identifies H_c⁰ with Hom(1,j_!G) on Xbar
and H⁰ with Hom(1,G) on X. The comparison is restriction along j. Its integral map is
exactly a1ConstructibleCompletedComparison. Apply point sections and H⁰, invert the
uniformizer, and extend scalars at a common finite field. All these operations respect
arrows and their unit maps, so the comparison is natural and linear
(lem-a1-adic-compactification-section-realization).
3. A section restricting to zero on X has zero fibre inside X. Its target j_!G has zero
fibre on the boundary. Exactness of fibres kills the fibres of its image, and joint
conservativity kills the image. Thus the section is zero and the comparison is injective
(lem-per-adic-heart-pullback-fibres).
4. The nonzero-fibre support S of the representing morphism is closed in Xbar and the
morphism vanishes off S. Boundary fibres vanish, so S lies in j(X). Its inverse image
Z in X is closed and the section restricts to zero off Z
(lem-a1-adic-section-closed-support).
5. Xbar is proper, hence S is proper. Its reduced induced closed subscheme is unchanged
when regarded inside j(X), because its entire underlying set lies there. Consequently
Z is proper in exactly the recorded reduced-induced sense
(lem-weil-pbc-closed-subset-proper-over-base-properties).
6. Further open restriction is composition of the same pullbacks and their canonical
unit comparisons. Lisse realization preserves units and pullbacks, and maps a section
to its ordinary continuous adic section. On the smooth finite-field/Weil domain this
is the H⁰ normalization of lem-a1-degree-zero-compact-support-sections; its extra
hypotheses are imposed only in that specialization, never on general X or G. -/
theorem a1ConstructibleDegreeZeroProperSupport
    (c : Compactification (X ↘ Spec (.of D.k))) :
    Nonempty (A1ConstructibleDegreeZeroComparison l D hl Ω X c) := by
  sorry

section LisseNormalization

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (Ω' : Type (u + 1)) [Field Ω'] [Algebra ℚ_[l] Ω'] [IsAlgClosure ℚ_[l] Ω']

/-- Compatibility with the recorded lisse comparison, on precisely its coefficient
universe and geometric-fibre domain. Realization is normalized on every integral model,
and both the ordinary section square and compact comparison square commute.
Source: BS 6.8.4, 6.8.14--15; Milne 18.1
(blueprint: lem-a1-constructible-degree-zero-proper-support). -/
structure A1ConstructibleLisseCompatibility
    (c : Compactification (D.geometricFiber X₀).hom)
    (N : A1ConstructibleDegreeZeroComparison l D hl Ω' (D.geometricFiber X₀).left c)
    (M : A1DegreeZeroNaturalComparison D l hl X₀ Ω' c) where
  /-- Realization lands in the recorded constructible heart. -/
  realization : A1DegreeZeroLisse D l hl X₀ Ω' ⥤
    sfCommonStageHeart l (D.geometricFiber X₀).left Ω'
  /-- The object realization is the actual completed inverse-limit realization. -/
  realizes : ∀ L, A1DegreeZeroRealizes D l hl X₀ Ω' L (realization.obj L).obj
  /-- The arrow realization is fixed on every integral coefficient model. -/
  integral : ∀ E : Padic.FiniteCoefficientFields l Ω',
    a1DegreeZeroLisseInclusion D l hl X₀ Ω' E ⋙ realization ⋙
        (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω').ι ≅
      a1DegreeZeroIntegralModel D l hl X₀ Ω' E ⋙
        a1ConstructibleModelInclusion l Ω' (D.geometricFiber X₀).left E
  /-- The coefficient unit under this same realization. -/
  unit : (realization.obj (a1DegreeZeroUnit D l hl X₀ Ω')).obj ≅
    a1ConstructibleUnit l D hl Ω' (D.geometricFiber X₀).left
  /-- The ordinary H⁰ comparison on all lisse arrows. -/
  ordinary : realization ⋙ (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω').ι ⋙
      N.ordinary ≅ M.ordinaryCohomology
  /-- The compact comparison on those same arrows. -/
  compact : realization ⋙ (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω').ι ⋙
      N.compact ≅ M.compactCohomology
  /-- The ordinary Hom section is exactly the realized ordinary lisse section. -/
  sections : ∀ (L : A1DegreeZeroLisse D l hl X₀ Ω')
    (z : N.ordinary.obj (realization.obj L).obj),
    N.sections.hom.app (realization.obj L) (ULift.up z) =
      unit.inv ≫ (realization.map
        (M.ordinary.hom.app L (ULift.up (ordinary.hom.app L z)))).hom
  /-- Compact-to-ordinary restriction agrees with the lisse compact restriction. -/
  comparison : Functor.whiskerLeft
      (realization ⋙ (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω').ι)
        N.comparison ≫ ordinary.hom = compact.hom ≫ M.compact

/-- On the old lemma's smooth finite-field/Weil domain the constructible comparison
has exactly its ordinary lisse normalization. These assumptions occur only here.
Source: Milne 18.1 and 18.3(b); BS 6.8.4, 6.8.14--15
(blueprint: lem-a1-constructible-degree-zero-proper-support).
Proof: choose the ordinary lisse comparison of
lem-a1-degree-zero-compact-support-sections, using its smooth lisse lattice for F.
Realize normalized integral lisse systems by their completed inverse limits. The
completed-system comparison makes them integral constructible, and rationalization
puts them in the common-stage heart. Full faithfulness of
lem-tw-lisse-rational-realization extends this to all rational and common-stage arrows.
The finite-model formula is exactly a1DegreeZeroIntegralModel followed by the recorded
localization and inclusion, giving integral. Its constant system supplies unit.
The ordinary derived adjunction identifies its unit Hom with ordinary lisse sections;
this is the sections equation. The compact-to-ordinary map is the same completed
open-adjunction mate on each integral model. Taking H⁰ and scalar extension gives
comparison, and common-stage coefficient coherence makes these equations natural.
The selected lisse object realizes For(F), with the two cohomology comparisons stated
by the old lemma. This imposes no smoothness, descent or Weil condition on the general
constructible theorem above. -/
theorem a1ConstructibleDegreeZeroProperSupport_lisse [Smooth X₀.hom]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω')
    (_hF : HasCommonStageLisseLattice l Ω' (D.geometricFiber X₀).left
      ((sfCommonStageWeilForget D l hl X₀ Ω').obj F.obj))
    (c : Compactification (D.geometricFiber X₀).hom) :
    ∃ (N : A1ConstructibleDegreeZeroComparison l D hl Ω' (D.geometricFiber X₀).left c)
      (M : A1DegreeZeroNaturalComparison D l hl X₀ Ω' c),
      Nonempty (A1ConstructibleLisseCompatibility l D hl X₀ Ω' c N M) ∧
      ∃ L : A1DegreeZeroLisse D l hl X₀ Ω',
        A1DegreeZeroRealizes D l hl X₀ Ω' L
          ((sfCommonStageWeilForget D l hl X₀ Ω').obj F.obj) ∧
        Nonempty (adicOrdinaryCohomology D l hl (D.geometricFiber X₀).left Ω'
          ((sfCommonStageWeilForget D l hl X₀ Ω').obj F.obj) 0 ≃ₗ[Ω']
            M.ordinaryCohomology.obj L) ∧
        Nonempty (adicCompactCohomology D l hl (D.geometricFiber X₀).left Ω' c
          ((sfCommonStageWeilForget D l hl X₀ Ω').obj F.obj) 0 ≃ₗ[Ω']
            M.compactCohomology.obj L) := by
  sorry

end LisseNormalization

end WeilConjectures
