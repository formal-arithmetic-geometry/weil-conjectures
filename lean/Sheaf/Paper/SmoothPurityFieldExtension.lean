module

public import Sheaf.Paper.RationalScalarComparisonData
public import Sheaf.Paper.AdicPurityScalarNaturalityData
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.IntegralAdjunctionBijection
public import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.CategoryTheory.PurityConjugatedCoefficientAdjunction
import Sheaf.Paper.AdicPurityScalarNaturality
import Sheaf.Paper.RationalScalarComparisonIdentification

/-! # Finite coefficient extension and the smooth purity adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/_section.md and its proof
(blueprint: sk-lem-sp-field-extension).

## Main definitions

* `leftComparison`: the shared left-coordinate isomorphism constructor.
* `compactSupport`: the existing raw rational compact-support functor.
* `compactRealization`: its specified normalized exceptional realization.
* `compactComparison`: the coefficient comparison in those coordinates.

## Main statements

* `fieldExtension`: coefficient comparisons with unit, counit and cocycle equations.

The compact-support functor is the published raw rational functor. Its comparison
is transported along the recorded normalized compact-support realization. The
purity map is pinned to the integral purity map before forming the adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.SmoothPurityFieldExtension
open AdicPurityScalarNaturality
open RationalScalarComparisonIdentification

attribute [local irreducible] RationalScalarComparisonIdentification.O
  RationalScalarComparisonIdentification.H
  RationalScalarComparisonIdentification.T RationalScalarComparisonIdentification.Q
  RationalScalarComparisonIdentification.alpha RationalScalarComparisonIdentification.unit
  RationalScalarComparisonIdentification.SourceLocalizationNormalization
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target

-- Expose only the small native-to-raw category aliases during implicit matching.
attribute [local implicit_reducible] RationalScalarComparisonIdentification.G
  AdicPurityScalarNaturality.fieldStage
  ConstructibleExceptionalCoefficients.category
  ConstructibleExceptionalCoefficients.FieldComparison.q
  ConstructibleExceptionalCoefficients.FieldComparison.b

section Transport

universe vT uT

variable {A B C D E F : Type uT}
  [catA : Category.{vT} A] [catB : Category.{vT} B] [catC : Category.{vT} C]
  [catD : Category.{vT} D] [catE : Category.{vT} E] [catF : Category.{vT} F]

/-- Transport a left coefficient comparison through the fixed endpoint isomorphisms. -/
def leftComparison {P P' : A ⥤ B} {Q Q' : C ⥤ D}
    {TX : A ⥤ C} {TY : B ⥤ D} (e : P ≅ P') (e' : Q ≅ Q')
    (b : P ⋙ TY ≅ TX ⋙ Q) : P' ⋙ TY ≅ TX ⋙ Q' :=
  Functor.isoWhiskerRight e.symm TY ≪≫ b ≪≫ Functor.isoWhiskerLeft TX e'

/-- Left-coordinate transport preserves both adjunction comparison equations. -/
private theorem leftAdjunctionComparison
    {P P' : A ⥤ B} {Q Q' : C ⥤ D} {J : B ⥤ A} {K : D ⥤ C}
    {TX : A ⥤ C} {TY : B ⥤ D}
    (e : P ≅ P') (e' : Q ≅ Q') (adj : P ⊣ J) (adj' : Q ⊣ K)
    (b : P ⋙ TY ≅ TX ⋙ Q) (c : J ⋙ TX ≅ TY ⋙ K)
    (hu : ∀ M, TX.map (adj.unit.app M) ≫ c.hom.app (P.obj M) ≫
      K.map (b.hom.app M) = adj'.unit.app (TX.obj M))
    (he : ∀ N, b.hom.app (J.obj N) ≫ Q.map (c.hom.app N) ≫
      adj'.counit.app (TY.obj N) = TY.map (adj.counit.app N)) :
    (∀ M, TX.map ((adj.ofNatIsoLeft e).unit.app M) ≫ c.hom.app (P'.obj M) ≫
      K.map ((leftComparison e e' b).hom.app M) =
        (adj'.ofNatIsoLeft e').unit.app (TX.obj M)) ∧
    (∀ N, (leftComparison e e' b).hom.app (J.obj N) ≫ Q'.map (c.hom.app N) ≫
      (adj'.ofNatIsoLeft e').counit.app (TY.obj N) =
        TY.map ((adj.ofNatIsoLeft e).counit.app N)) := by
  constructor
  · intro M
    simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
      Functor.whiskerRight_app, leftComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.map_comp, Category.assoc]
    have hn := c.hom.naturality (e.hom.app M)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    erw [(TY.mapIso (e.app M)).map_hom_inv_id_assoc K]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ K.map (e'.hom.app (TX.obj M))) (hu M)
  · intro N
    simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, leftComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.map_comp, Category.assoc]
    rw [← e'.hom.naturality_assoc]
    erw [(e'.app (K.obj (TY.obj N))).hom_inv_id_assoc]
    rw [he, ← TY.map_comp]

/-- Left-coordinate transport preserves the specified coefficient unitor equation. -/
private theorem leftIdentity {P P' : A ⥤ B} {TX : A ⥤ A} {TY : B ⥤ B}
    (e : P ≅ P') (b : P ⋙ TY ≅ TX ⋙ P)
    (uX : TX ≅ 𝟭 A) (uY : TY ≅ 𝟭 B) (hb : UnitEquation b uY uX) :
    UnitEquation (leftComparison e e b) uY uX := by
  intro M
  simp only [leftComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rw [← e.hom.naturality, reassoc_of% (hb M)]
  simp

/-- Left-coordinate transport preserves the specified scalar associator equation. -/
private theorem leftComposition
    {P P' : A ⥤ B} {Q Q' : C ⥤ D} {R R' : E ⥤ F}
    {TX : A ⥤ C} {TY : B ⥤ D} {UX : C ⥤ E} {UY : D ⥤ F}
    {VX : A ⥤ E} {VY : B ⥤ F}
    (e : P ≅ P') (e' : Q ≅ Q') (e'' : R ≅ R')
    (b : P ⋙ TY ≅ TX ⋙ Q) (c : Q ⋙ UY ≅ UX ⋙ R)
    (d : P ⋙ VY ≅ VX ⋙ R) (aX : TX ⋙ UX ≅ VX) (aY : TY ⋙ UY ≅ VY)
    (hc : CompositionEquation b c d aY aX) :
    CompositionEquation (leftComparison e e' b) (leftComparison e' e'' c)
      (leftComparison e e'' d) aY aX := by
  intro M
  simp only [leftComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← e''.hom.naturality]
  erw [((e'.app (TX.obj M))).map_hom_inv_id_assoc UY]
  have hn := aY.hom.naturality (e.inv.app M)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, reassoc_of% (hc M)]

/-- The purity square identifies generic right-adjoint transport with its given comparison. -/
private theorem rightAdjunctionComparison
    {I : Type*} [Preorder I] (X Y : I → Type uT)
    [catX : ∀ i, Category.{vT} (X i)] [catY : ∀ i, Category.{vT} (Y i)]
    (P : ∀ i, X i ⥤ Y i) (J H : ∀ i, Y i ⥤ X i)
    (adj : ∀ i, P i ⊣ J i) (γ : ∀ i, H i ≅ J i)
    (TX : ∀ i j, i ≤ j → (X i ⥤ X j))
    (TY : ∀ i j, i ≤ j → (Y i ⥤ Y j))
    (b : ∀ i j h, P i ⋙ TY i j h ≅ TX i j h ⋙ P j)
    (c : ∀ i j h, J i ⋙ TX i j h ≅ TY i j h ⋙ J j)
    (a : ∀ i j h, H i ⋙ TX i j h ≅ TY i j h ⋙ H j)
    (hs : ∀ i j h K, (TX i j h).map ((γ i).hom.app K) ≫ (c i j h).hom.app K =
      (a i j h).hom.app K ≫ (γ j).hom.app ((TY i j h).obj K))
    (hu : ∀ i j h M, (TX i j h).map ((adj i).unit.app M) ≫
      (c i j h).hom.app ((P i).obj M) ≫ (J j).map ((b i j h).hom.app M) =
        (adj j).unit.app ((TX i j h).obj M))
    (he : ∀ i j h K, (b i j h).hom.app ((J i).obj K) ≫
      (P j).map ((c i j h).hom.app K) ≫ (adj j).counit.app ((TY i j h).obj K) =
        (TY i j h).map ((adj i).counit.app K)) :
    (∀ i j h M, (TX i j h).map (((adj i).ofNatIsoRight (γ i).symm).unit.app M) ≫
      (a i j h).hom.app ((P i).obj M) ≫ (H j).map ((b i j h).hom.app M) =
        ((adj j).ofNatIsoRight (γ j).symm).unit.app ((TX i j h).obj M)) ∧
    (∀ i j h K, (b i j h).hom.app ((H i).obj K) ≫
      (P j).map ((a i j h).hom.app K) ≫
        ((adj j).ofNatIsoRight (γ j).symm).counit.app ((TY i j h).obj K) =
          (TY i j h).map (((adj i).ofNatIsoRight (γ i).symm).counit.app K)) := by
  obtain ⟨adjH, a', hUnit, -, hMap, hunit, hcounit, -, -⟩ :=
    purity_conjugated_coefficient_adjunction X Y P J H adj γ TX TY b c hu he
  have hAdj (i) : adjH i = (adj i).ofNatIsoRight (γ i).symm := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    simpa using hUnit i M
  have ha : a' = a := by
    funext i j h
    apply Iso.ext
    apply NatTrans.ext
    funext K
    rw [hMap, ← Category.assoc, hs]
    simp
  constructor
  · intro i j h M
    simpa only [ha, hAdj] using hunit i j h M
  · intro i j h K
    simpa only [ha, hAdj] using hcounit i j h K

/-- Transport both coordinates once, keeping the displayed left comparison as fixed data. -/
private theorem coordinateAdjunctionComparison
    {I : Type*} [Preorder I] (X Y : I → Type uT)
    [catX : ∀ i, Category.{vT} (X i)] [catY : ∀ i, Category.{vT} (Y i)]
    (P P' : ∀ i, X i ⥤ Y i) (J H : ∀ i, Y i ⥤ X i)
    (adj : ∀ i, P i ⊣ J i) (e : ∀ i, P i ≅ P' i) (γ : ∀ i, H i ≅ J i)
    (TX : ∀ i j, i ≤ j → (X i ⥤ X j))
    (TY : ∀ i j, i ≤ j → (Y i ⥤ Y j))
    (b : ∀ i j h, P i ⋙ TY i j h ≅ TX i j h ⋙ P j)
    (b' : ∀ i j h, P' i ⋙ TY i j h ≅ TX i j h ⋙ P' j)
    (hb : ∀ i j h, b' i j h = leftComparison (e i) (e j) (b i j h))
    (c : ∀ i j h, J i ⋙ TX i j h ≅ TY i j h ⋙ J j)
    (a : ∀ i j h, H i ⋙ TX i j h ≅ TY i j h ⋙ H j)
    (hs : ∀ i j h K, (TX i j h).map ((γ i).hom.app K) ≫ (c i j h).hom.app K =
      (a i j h).hom.app K ≫ (γ j).hom.app ((TY i j h).obj K))
    (hu : ∀ i j h M, (TX i j h).map ((adj i).unit.app M) ≫
      (c i j h).hom.app ((P i).obj M) ≫ (J j).map ((b i j h).hom.app M) =
        (adj j).unit.app ((TX i j h).obj M))
    (he : ∀ i j h K, (b i j h).hom.app ((J i).obj K) ≫
      (P j).map ((c i j h).hom.app K) ≫ (adj j).counit.app ((TY i j h).obj K) =
        (TY i j h).map ((adj i).counit.app K)) :
    (∀ i j h M,
      (TX i j h).map ((((adj i).ofNatIsoLeft (e i)).ofNatIsoRight (γ i).symm).unit.app M) ≫
        (a i j h).hom.app ((P' i).obj M) ≫ (H j).map ((b' i j h).hom.app M) =
          (((adj j).ofNatIsoLeft (e j)).ofNatIsoRight (γ j).symm).unit.app
            ((TX i j h).obj M)) ∧
    (∀ i j h K, (b' i j h).hom.app ((H i).obj K) ≫
      (P' j).map ((a i j h).hom.app K) ≫
        (((adj j).ofNatIsoLeft (e j)).ofNatIsoRight (γ j).symm).counit.app
          ((TY i j h).obj K) =
            (TY i j h).map
              ((((adj i).ofNatIsoLeft (e i)).ofNatIsoRight (γ i).symm).counit.app K)) := by
  apply rightAdjunctionComparison X Y P' J H
    (fun i ↦ (adj i).ofNatIsoLeft (e i)) γ TX TY b' c a hs
  · intro i j h M
    rw [hb]
    exact (leftAdjunctionComparison (e i) (e j) (adj i) (adj j)
      (b i j h) (c i j h) (hu i j h) (he i j h)).1 M
  · intro i j h K
    rw [hb]
    exact (leftAdjunctionComparison (e i) (e j) (adj i) (adj j)
      (b i j h) (c i j h) (hu i j h) (he i j h)).2 K

end Transport

attribute [local irreducible] leftComparison
  UnitEquation CompositionEquation PuritySquares
  integralExceptionalCompactification sfRationalScalarExtension
  sfRationalScalarComp sfRationalScalarUnit

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The already defined raw rational compact-support functor, in the canonical
compactification coordinates. Source: the compact-support convention in the
field-extension lemma (blueprint: sk-lem-sp-field-extension). -/
def compactSupport (E : AdicPurityScalarNaturality.Field D C) :
    RCat D C E X ⥤ RCat D C E Y :=
  sfCompactSupportFiniteFunctor C.l D.k
    (PurCompactSupport.coefficientPrimeUnit C.l D C.different)
    (integralExceptionalCompactification D f) E.val

/-- The specified realization of the normalized exceptional system's left adjoint
as the existing compact-support functor. Source: the alternative-adjoint-model
transport in the field-extension proof, Step 1
(blueprint: sk-lem-sp-field-extension). -/
def compactRealization
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (E : AdicPurityScalarNaturality.Field D C) :
    (O D C f S E).F ≅ compactSupport D C f E :=
  by
    simpa only [O, compactSupport, fieldStage] using
      S.ring.rationalLeft (integralExceptionalCompactification D f) (fieldStage D C E)

/-- The actual compact-support coefficient comparison in the displayed direction
of the field-extension lemma. Source: its proof, Step 1 followed by scalar
localization in Step 3 (blueprint: sk-lem-sp-field-extension). -/
def compactComparison
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    compactSupport D C f E ⋙ T D C E F h Y ≅
      T D C E F h X ⋙ compactSupport D C f F :=
  leftComparison (A := RCat D C E X) (B := RCat D C E Y)
    (C := RCat D C F X) (D := RCat D C F Y)
    (catA := inferInstance) (catB := inferInstance)
    (catC := inferInstance) (catD := inferInstance)
    (compactRealization D C f S E) (compactRealization D C f S F)
    (RationalScalarComparisonIdentification.c D C f S E F h)

attribute [local irreducible] compactSupport compactRealization compactComparison

set_option maxHeartbeats 1000000 in
-- The nested normalized comparison record requires more elaboration heartbeats (U4).
/-- Finite coefficient extension preserves the normalized smooth purity
adjunction, including its unit, counit, identities and coefficient cocycles.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/_section.md and its proof
(blueprint: sk-lem-sp-field-extension).

Proof: at every positive quotient level use the finite-free tensor comparisons
of the compact-support and exceptional adjunctions. They preserve the finite
units, counits, purity roots and reduction maps. Take the compatible strict
inverse limits. Finite freeness commutes with these limits; the canonical
completion comparison identifies ordinary tensor with completed scalar
extension and transports its associators. Transport the right adjoint along
the integral purity isomorphism of det-sp-integral-adjunction-bijection. Thus
the twisted-pullback comparison is purity inverse, exceptional comparison,
and scalar extension of purity, in that order. Cancellation of these purity
maps gives the unit and counit equations. Localize the integral linear Hom
bijections and all these diagrams at the coefficient uniformizer. The
normalized source-localization map identifies the resulting purity morphism
with Q(I.gamma), so the resulting adjunction is the specified one. Naturality
extends from integral arrows to rational scalar multiples and sums. Finally
localize the integral coefficient cocycles and identity equations, retaining
the canonical scalar-extension associators. Transport compact supports along
compactRealization at every endpoint; its inverse pairs cancel in both the
adjunction diagrams and the cocycles. -/
theorem fieldExtension :
    ∃ (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
      (I : AdicPurityScalarNaturality.Data D C f d S)
      (qH : ∀ E : AdicPurityScalarNaturality.Field D C,
        source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E),
    (∀ E : AdicPurityScalarNaturality.Field D C,
      SourceLocalizationNormalization D C f d E (qH E)) ∧
    ∃ (γ : ∀ E : AdicPurityScalarNaturality.Field D C,
        H D C f d E ≅ G D C f S E),
    (∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
      (qH E).hom.app K ≫ (γ E).hom.app ((Q D C E Y).obj K) =
        (Q D C E X).map ((I.gamma E).hom.app K) ≫
          (gLocalization D C f S E).hom.app K) ∧
    ∃ (a : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
        H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F),
    (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
        (K : RCat D C E Y),
      HEq ((a E F h).app K)
        (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
          (IntermediateField.inclusion h) f d K)) ∧
    let adj := fun E : AdicPurityScalarNaturality.Field D C ↦
      ((O D C f S E).adjunction.ofNatIsoLeft
        (compactRealization D C f S E)).ofNatIsoRight (γ E).symm
    (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
        (M : RCat D C E X),
      (T D C E F h X).map ((adj E).unit.app M) ≫
        (a E F h).hom.app ((compactSupport D C f E).obj M) ≫
        (H D C f d F).map ((compactComparison D C f S E F h).hom.app M) =
          (adj F).unit.app ((T D C E F h X).obj M)) ∧
    (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
        (K : RCat D C E Y),
      (compactComparison D C f S E F h).hom.app ((H D C f d E).obj K) ≫
        (compactSupport D C f F).map ((a E F h).hom.app K) ≫
        (adj F).counit.app ((T D C E F h Y).obj K) =
          (T D C E F h Y).map ((adj E).counit.app K)) ∧
    (∀ E : AdicPurityScalarNaturality.Field D C,
      UnitEquation (a E E le_rfl) (unit D C E X) (unit D C E Y)) ∧
    (∀ E : AdicPurityScalarNaturality.Field D C,
      UnitEquation (compactComparison D C f S E E le_rfl)
        (unit D C E Y) (unit D C E X)) ∧
    (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (a E F h) (a F L k) (a E L (h.trans k))
        (alpha D C E F L h k X) (alpha D C E F L h k Y)) ∧
    (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (compactComparison D C f S E F h)
        (compactComparison D C f S F L k) (compactComparison D C f S E L (h.trans k))
        (alpha D C E F L h k Y) (alpha D C E F L h k X)) := by
  obtain ⟨S, ⟨I⟩⟩ := adicPurityScalarNaturality D C f d
  refine ⟨S, I, ?_⟩
  have hr := rationalScalarComparisonIdentification D C f d S I
  unfold RationalScalarComparisonIdentification.Result at hr
  obtain ⟨hShift, _, qH, hNorm, hq⟩ := hr
  refine ⟨qH, hNorm, ?_⟩
  obtain ⟨_, _, scalarLocalization, _, _, _, _, _, γ, _, hGamma, hg⟩ := hq
  refine ⟨γ, hGamma, ?_⟩
  obtain ⟨a, _, _, hCanonical, _, _, _, hSquare, hAUnit, _, hAComp, _⟩ := hg
  refine ⟨a, hCanonical, ?_⟩
  have hSmooth := coordinateAdjunctionComparison
    (fun E ↦ RCat D C E X) (fun E ↦ RCat D C E Y)
    (catX := fun E ↦ inferInstance) (catY := fun E ↦ inferInstance)
    (fun E ↦ (O D C f S E).F) (compactSupport D C f) (G D C f S) (H D C f d)
    (fun E ↦ (O D C f S E).adjunction) (compactRealization D C f S) γ
    (fun E F h ↦ T D C E F h X) (fun E F h ↦ T D C E F h Y)
    (c D C f S) (compactComparison D C f S) (fun E F h ↦ by unfold compactComparison; rfl)
    (b D C f S) a
    (fun E F h ↦ by
      have hs := hSquare E F h
      unfold PuritySquares at hs
      exact hs.1)
    (fun E F h ↦ by
      let cmp := S.fields.rationalComparison (integralExceptionalCompactification D f)
        (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)
      let := cmp.shiftX
      let := cmp.shiftY
      delta G O c b T
      with_unfolding_all exact cmp.comparison.unit)
    (fun E F h ↦ by
      let cmp := S.fields.rationalComparison (integralExceptionalCompactification D f)
        (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)
      let := cmp.shiftX
      let := cmp.shiftY
      delta G O c b T
      with_unfolding_all exact cmp.comparison.counit)
  refine ⟨hSmooth.1, hSmooth.2, hAUnit, ?_, hAComp, ?_⟩
  · intro E
    unfold compactComparison
    refine leftIdentity (A := RCat D C E X) (B := RCat D C E Y)
      (catA := inferInstance) (catB := inferInstance)
      (compactRealization D C f S E) (c D C f S E E le_rfl)
      (unit D C E X) (unit D C E Y) ?_
    unfold UnitEquation
    intro M
    delta c O T unit
    with_unfolding_all
      exact S.fields.rationalIdentityLeft (integralExceptionalCompactification D f)
        (fieldStage D C E) M
  · intro E F L h k
    unfold compactComparison
    refine leftComposition
      (A := RCat D C E X) (B := RCat D C E Y)
      (C := RCat D C F X) (D := RCat D C F Y)
      (E := RCat D C L X) (F := RCat D C L Y)
      (catA := inferInstance) (catB := inferInstance) (catC := inferInstance)
      (catD := inferInstance) (catE := inferInstance) (catF := inferInstance)
      (compactRealization D C f S E) (compactRealization D C f S F)
      (compactRealization D C f S L) (c D C f S E F h) (c D C f S F L k)
      (c D C f S E L (h.trans k))
      (alpha D C E F L h k X) (alpha D C E F L h k Y) ?_
    unfold CompositionEquation
    intro M
    rcases S.fields.rationalCocycle (integralExceptionalCompactification D f)
      (fieldStage D C E) (fieldStage D C F) (fieldStage D C L)
      (IntermediateField.inclusion h) (IntermediateField.inclusion k) with ⟨hc, -⟩
    delta c O T alpha
    with_unfolding_all exact (hc M).symm

end WeilConjectures.SmoothPurityFieldExtension
