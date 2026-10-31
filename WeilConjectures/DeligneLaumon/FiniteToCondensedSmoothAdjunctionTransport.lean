/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportScalarLines
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHeartTensor
public import WeilConjectures.SecSmoothPurity.TransportFiniteLineDerived
public import WeilConjectures.SecSmoothPurity.TransportFiniteSupport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothAdjunctionGeneralBase
public import WeilConjectures.AlgebraicGeometry.ConstructibleCoefficientHomComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
import WeilConjectures.DeligneLaumon.GeneralFieldLocalizingTools
import WeilConjectures.AlgebraicGeometry.NativeCondensedIntegralTransport
import WeilConjectures.AlgebraicGeometry.CondensedOpenDerivedCalculus
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstruction

/-! # Finite-to-condensed smooth adjunction transport over perfect fields

Source: current blueprint, sk-thm-purity-transport, Steps 1--4, and
thm-a1-curve-perverse-heart, Step 2.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GeneralFieldSmoothTransport
open PurityTransport

/-- The base field, including characteristic zero. Invertibility is a condition in
this field, rather than the choice of a positive characteristic.
Source: standing hypotheses of the transport lemma.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
structure Base (ell : ℕ) where
  carrier : Type u
  [field : Field carrier]
  [perfect : PerfectField carrier]
  invertible : IsUnit (ell : carrier)

attribute [instance] Base.field Base.perfect

/-- A geometric index for the conditional transport assertion. The two absolute
and the relative dimensions range independently over zero and one, also for the
empty scheme. The finite input is the published etale-origin system, including
its normalized traces and quotient cocycles.
Source: hypotheses of the transport lemma and its finite-system dependency.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
structure Index (ell : ℕ) [Fact ell.Prime] where
  base : Base.{u} ell
  X : Over (Spec (.of base.carrier))
  Y : Over (Spec (.of base.carrier))
  dimX : Fin 2
  dimY : Fin 2
  [xSmooth : SmoothOfRelativeDimension dimX.val X.hom]
  [ySmooth : SmoothOfRelativeDimension dimY.val Y.hom]
  [xFinite : LocallyOfFiniteType X.hom]
  [yFinite : LocallyOfFiniteType Y.hom]
  [xCompact : QuasiCompact X.hom]
  [yCompact : QuasiCompact Y.hom]
  [xSeparated : IsSeparated X.hom]
  [ySeparated : IsSeparated Y.hom]
  f : X.left ⟶ Y.left
  [isOver : f.IsOver (Spec (.of base.carrier))]
  dim : Fin 2
  [smooth : SmoothOfRelativeDimension dim.val f]
  [separated : IsSeparated f]
  [finiteType : LocallyOfFiniteType f]
  [quasiCompact : QuasiCompact f]
  compactification : Compactification f
  noetherianX : IsNoetherian X.left
  noetherianY : IsNoetherian Y.left
  finite : Etale.FiniteSmoothPurity.FiniteSmoothAdjunctionDatum ell f dim.val
    compactification noetherianX noetherianY

attribute [instance] Index.xSmooth Index.ySmooth Index.xFinite Index.yFinite
  Index.xCompact Index.yCompact Index.xSeparated Index.ySeparated Index.isOver
  Index.smooth Index.separated Index.finiteType Index.quasiCompact
  Index.noetherianX Index.noetherianY

variable (ell : ℕ) [Fact ell.Prime]

/-- Actual bounded compact support and twisted pullback, with preservation proofs
and adjunction data. No functor is chosen in place of a geometric operation.
Source: clauses (1)--(2).
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
structure BoundedFor (c : Coefficient ell) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) (cf : Compactification f) where
  support_closed : ∀ K, property ell c X K → property ell c Y
    ((CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) cf).obj K)
  source_closed : ∀ K, property ell c Y K → property ell c X
    ((c.smoothSource ell f d).obj K)
  adjunction : support ell c cf support_closed ⊣
    source ell c f d source_closed

/-- The bounded adjunction at the specified geometric index.
Source: clauses (1)--(2).
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
abbrev Bounded (c : Coefficient ell) (s : Index.{u} ell) :=
  BoundedFor ell c s.f s.dim.val s.compactification

/-- The ambient counit of precisely the bounded adjunction just recorded.
Source: clauses (1)--(2).
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def Bounded.trace {c : Coefficient ell} {s : Index.{u} ell}
    (a : Bounded ell c s) (K : c.ctf ell s.Y.left) :=
  (a.adjunction.counit.app K).hom

/-- Indexing the same normalized adjunction at every coefficient presentation.
Source: the coefficient cases of clauses (1)--(2), including finite reductions.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
abbrev Family := ∀ (c : Coefficient ell) (s : Index.{u} ell), Bounded ell c s

/-- An actual right adjoint on the ordinary localizing closures, together with
its bounded restriction and the unique counit-compatible purity isomorphism.
The first existential is the existence of the localizing right adjoint itself.
Source: clause (3).
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def Localizing (a : Family.{u} ell) (c : Coefficient ell) (s : Index.{u} ell) : Prop :=
  ∃ hL : ∀ K, localizing ell c s.X.left K → localizing ell c s.Y.left
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).obj K),
  ∃ G : (localizing ell c s.Y.left).FullSubcategory ⥤
      (localizing ell c s.X.left).FullSubcategory,
  ∃ b : (localizing ell c s.Y.left).lift
      ((localizing ell c s.X.left).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification)
      (fun K ↦ hL K.obj K.property) ⊣ G,
  ∃ hG : ∀ K : c.ctf ell s.Y.left,
      property ell c s.X.left (G.obj ((inclusion ell c s.Y.left).obj K)).obj,
  ∃ bctf : support ell c s.compactification (a c s).support_closed ⊣
      exceptional ell c G hG,
    (∀ K : c.ctf ell s.Y.left,
      HEq (bctf.counit.app K).hom
        (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom) ∧
    ∃! gamma : source ell c s.f s.dim.val (a c s).source_closed ≅ exceptional ell c G hG,
      CounitCompatible (a c s).adjunction bctf gamma

/-- Scalar preservation, invertibility of the actual compact-support exchange,
and the trace equation with the canonical pullback/twist scalar arrow. This is
an equation of maps, and determines both the transported unit and counit.
Source: coefficient compatibility and the displayed mate equation.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def Scalars (a : Family.{u} ell) : Prop :=
  ∀ (c c' : Coefficient ell) (q : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell q →
    ∃ hq : c.integralMap ell ≫ q.hom.hom = c'.integralMap ell,
    ∀ s : Index.{u} ell,
    ∃ p : ScalarLineCoordinates ell q hq s.X.left,
      (∀ (W : Scheme.{u}), W = s.X.left ∨ W = s.Y.left →
        ∀ K : c.derived ell W, property ell c W K →
          property ell c' W ((scalarSixChange q W).obj K)) ∧
      (∀ M : c.ctf ell s.X.left,
        IsIso ((scalarSupportMap q s.compactification).app M.obj)) ∧
      ∀ K : c.ctf ell s.Y.left,
        IsIso (sourceScalar ell q s.f s.dim.val hq p K.obj) ∧
        ∃ hK : property ell c' s.Y.left ((scalarSixChange q s.Y.left).obj K.obj),
          (scalarSixChange q s.Y.left).map ((a c s).trace ell K) =
            (scalarSupportMap q s.compactification).app
                ((c.smoothSource ell s.f s.dim.val).obj K.obj) ≫
              (CondensedRing.rightDerivedLowerShriekOfCompactification
                (c'.obj ell) s.compactification).map
                  (sourceScalar ell q s.f s.dim.val hq p K.obj) ≫
              (a c' s).trace ell ⟨_, hK⟩



/-- Additive-section identification for inverse finite encoding.
Source: finite section-action realization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def inverseForget (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (X : Scheme.{u}) :=
  Functor.isoWhiskerLeft (finiteEncoding A X).inverse (finiteEncodingForget A X).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteEncoding A X).counitIso (Mod.forget _) ≪≫
    Functor.leftUnitor _

/-- The finite tensorator is normalized on every local pure pair.
Source: finite section-action tensor realization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def FiniteTensorNormalized (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (X : Scheme.{u})
    (m : (finiteEncoding A X).inverse.Monoidal) : Prop :=
  ∀ (M N : FiniteDiscreteInternalModules A X) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((m.toLaxMonoidal.μ M N).hom.app V)
      (ConstantScalarRestriction.fixedPure (ProEt.topology X) (ULift.{u + 1} A)
        ((finiteEncoding A X).inverse.obj M) ((finiteEncoding A X).inverse.obj N) V
        ((((inverseForget A X).inv.app M).hom.app V).hom x)
        ((((inverseForget A X).inv.app N).hom.app V).hom y)) =
      (((inverseForget A X).inv.app (M ⊗ N)).hom.app V).hom
        (InternalAbelianSheafModule.comparison_internalTmul (ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj A) X) M N V x y)

/-- Derive the exact finite encoding with its K-flat tensorator.
Source: finite tensor realization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
@[instance_reducible] def finiteDerivedMonoidal
    (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (X : Scheme.{u})
    (m : (finiteEncoding A X).inverse.Monoidal) :
    (finiteEncodingDerived A X).inverse.Monoidal := by
  let F := (finiteEncoding A X).inverse
  letI : F.Monoidal := m
  letI : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  letI : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  exact Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory

/-- Localize the inverse-image mate of the section identity.
Source: finite operation realization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def finiteDerivedPull (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj A) f) _ ≪≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar (Profinite.continuousMapRingObj A) f)
      (finiteEncoding A X).inverse).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteEncodingPull A f).symm ≪≫
    Functor.mapDerivedCategoryCompIso (finiteEncoding A Y).inverse
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f) ≪≫
    Functor.isoWhiskerLeft _
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm

/-- Root-normalized finite line, including the ordered target's unit factor.
Source: finite Tate coordinates.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def finiteLine (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) (X : Scheme.{u})
    (hX : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (p : FiniteLineCoordinates ell A fin n hA X hX) (d : Fin 2) :
    (letI : Finite A := fin
     letI : TopologicalSpace A := ⊥
     letI : DiscreteTopology A := discreteTopology_bot A
     (finiteEncodingDerived A X).inverse.obj
       ((Coefficient.finite A fin n hA).derivedLine ell X d.val) ≅
       (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1} A) X).obj
         (Etale.FiniteSmoothPurity.line (ULift.{u + 1} A) (ell ^ (n + 1))
           (finiteLiftAnnihilator ell A n hA) X d.val)) := by
  letI : Finite A := fin
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  rcases d with ⟨d, hd⟩
  by_cases h : d = 0
  · subst d
    exact ((finiteEncodingDerived A X).inverse.mapIso
        ((shiftFunctorZero _ ℤ).app _) ≪≫ finiteDerivedUnit ell A n hA X hX p)
  · have h1 : d = 1 := by omega
    subst d
    exact (finiteDerivedLine ell A n hA X hX p ≪≫
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1} A) X).mapIso
        (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
          ((Etale.ordinaryFiniteLine (ULift.{u + 1} A) (ell ^ (n + 1))
            (finiteLiftAnnihilator ell A n hA) X) ⟦(2 : ℤ)⟧)).symm)

/-- Compare the entire finite twisted inverse image with its etale-origin model.
Source: finite tensor, inverse-image and root realization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def finiteSource (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (p : FiniteLineCoordinates ell A fin n hA X hX) (d : Fin 2)
    (K : (Coefficient.finite A fin n hA).derived ell Y)
    (m : (letI : Finite A := fin
          letI : TopologicalSpace A := ⊥
          letI : DiscreteTopology A := discreteTopology_bot A
          (finiteEncoding A X).inverse.Monoidal)) :
    (letI : Finite A := fin
     letI : TopologicalSpace A := ⊥
     letI : DiscreteTopology A := discreteTopology_bot A
     (finiteEncodingDerived A X).inverse.obj
       (((Coefficient.finite A fin n hA).smoothSource ell f d.val).obj K) ≅
       (Etale.FiniteSmoothPurity.proSource (ULift.{u + 1} A) f
         (Etale.FiniteSmoothPurity.line (ULift.{u + 1} A) (ell ^ (n + 1))
           (finiteLiftAnnihilator ell A n hA) X d.val)).obj
         ((finiteEncodingDerived A Y).inverse.obj K)) := by
  letI : Finite A := fin
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI := finiteDerivedMonoidal A X m
  exact ((Functor.Monoidal.μIso (finiteEncodingDerived A X).inverse
    ((CondensedRing.upperStar (Profinite.continuousMapRingObj A) f).leftDerivedFunctor.obj K)
    ((Coefficient.finite A fin n hA).derivedLine ell X d.val)).symm ≪≫
      tensorIso ((finiteDerivedPull A f).app K) (finiteLine ell A fin n hA X hX p d))

/-- Finite counits agree on every object with the specified diagonal/DNC
orientation, after the actual encoding and common-refinement comparison. The
etale-origin witness only provides coordinates for the canonical comparison.
Source: clause (1), finite trace normalization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def FiniteNormalized (a : Family.{u} ell) : Prop :=
  ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) (s : Index.{u} ell),
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : HasCompactification s.f := s.compactification.hasCompactification
    ∃ hX : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(s.X.left, ⊤)),
    ∃ p : FiniteLineCoordinates ell A fin n hA s.X.left hX,
    ∃ m : (finiteEncoding A s.X.left).inverse.Monoidal,
      FiniteTensorNormalized A s.X.left m ∧
      ∃ L : Etale.FiniteSmoothPurity.SmoothLevel (ULift.{u + 1} A)
        (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
        (finiteLiftAnnihilator ell A n hA) s.f s.dim.val,
      ∀ K : (Coefficient.finite A fin n hA).ctf ell s.Y.left,
      ∃ E : DerivedCategory.Plus
          (Sheaf s.X.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))),
      ∃ e : (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1} A) s.X.left).obj E.obj ≅
          (finiteEncodingDerived A s.X.left).inverse.obj
            (((Coefficient.finite A fin n hA).smoothSource ell s.f s.dim.val).obj K.obj),
        (finiteEncodingDerived A s.Y.left).inverse.map
            ((a (.finite A fin n hA) s).trace ell K) =
          (finiteEncodingSupport A s.compactification).hom.app
              (((Coefficient.finite A fin n hA).smoothSource ell s.f s.dim.val).obj K.obj) ≫
            (ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) s.compactification).map e.inv ≫
            (ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso
              (ULift.{u + 1} A) s.compactification
              (HasCompactification.compactification s.f)).hom.app E ≫
            (Etale.FiniteSmoothPurity.proCompact (ULift.{u + 1} A) s.f).map
              (e.hom ≫ (finiteSource ell A fin n hA s.f hX p s.dim K.obj m).hom) ≫
            Etale.FiniteSmoothPurity.proTrace (ULift.{u + 1} A) s.f
              (Etale.FiniteSmoothPurity.line (ULift.{u + 1} A) (ell ^ (n + 1))
                (finiteLiftAnnihilator ell A n hA) s.X.left s.dim.val)
              L.alpha ((finiteEncodingDerived A s.Y.left).inverse.obj K.obj)

/-- Open source restriction of compact support uses the specified open compositor.
Source: final paragraph, source restriction.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def openSupport (c : Coefficient ell) {X Y V : Scheme.{u}} {f : X ⟶ Y}
    (cf : Compactification f) (j : V ⟶ X) [IsOpenImmersion j] :=
  Functor.isoWhiskerRight (openComp (c.obj ell) j cf.i).symm
      (actualPush (c.obj ell) cf.g) ≪≫ Functor.associator _ _ _

/-- The restriction of the smooth source, using the root-normalized Tate
pullback and the canonical derived inverse-image tensorator.
Source: source restriction of the smooth dualizing object.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def openSource (c : Coefficient ell) {X Y V : Scheme.{u}}
    (f : X ⟶ Y) (j : V ⟶ X) (d : ℕ)
    (p : LinePullCoordinates ell c j) (K : c.derived ell Y) :
    (c.smoothSource ell (j ≫ f) d).obj K ≅
      (actualPull (c.obj ell) j).obj ((c.smoothSource ell f d).obj K) :=
  tensorIso ((CondensedRing.leftDerivedUpperStarComp (c.obj ell) j f).app K)
      (p.derived ell d).symm ≪≫
    Functor.Monoidal.μIso (actualPull (c.obj ell) j) _ _

/-- The actual open adjunction, expressed with the total-derived inverse image.
Source: source restriction and the exact/derived inverse-image comparison.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def openAdjunction (c : Coefficient ell) {X V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction (c.obj ell) j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) j).symm

/-- Exact source-open operations preserve bounded objects and localizing closures.
The open adjunction restricts to the latter, and the compact-support counit is
the composite of the given smooth counit with the canonical open counit.
Source: source-restriction paragraph.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def OpenRestriction (a : Family.{u} ell) (c : Coefficient ell) (s : Index.{u} ell) : Prop :=
  ∀ (V : Scheme.{u}) (j : V ⟶ s.X.left) [IsOpenImmersion j] [QuasiCompact j],
    (∀ K, property ell c V K → property ell c s.X.left
      ((actualOpen (c.obj ell) j).obj K)) ∧
    (∀ K, property ell c s.X.left K → property ell c V
      ((actualPull (c.obj ell) j).obj K)) ∧
    ∃ hL : ∀ K, localizing ell c V K → localizing ell c s.X.left
      ((actualOpen (c.obj ell) j).obj K),
    ∃ hP : ∀ K, localizing ell c s.X.left K → localizing ell c V
      ((actualPull (c.obj ell) j).obj K),
    ∃ b : (localizing ell c s.X.left).lift
        ((localizing ell c V).ι ⋙ actualOpen (c.obj ell) j)
        (fun K ↦ hL K.obj K.property) ⊣
      (localizing ell c V).lift
        ((localizing ell c s.X.left).ι ⋙ actualPull (c.obj ell) j)
        (fun K ↦ hP K.obj K.property),
      (∀ K, HEq (b.counit.app K).hom ((openAdjunction ell c j).counit.app K.obj)) ∧
      ∃ p : LinePullCoordinates ell c j,
      ∃ r : BoundedFor ell c (j ≫ s.f) s.dim.val (s.compactification.precomp j),
      ∀ K : c.ctf ell s.Y.left,
        (r.adjunction.counit.app K).hom =
          (openSupport ell c s.compactification j).hom.app
              ((c.smoothSource ell (j ≫ s.f) s.dim.val).obj K.obj) ≫
            (CondensedRing.rightDerivedLowerShriekOfCompactification
              (c.obj ell) s.compactification).map
              ((actualOpen (c.obj ell) j).map
                  (openSource ell c s.f j s.dim.val p K.obj).hom ≫
                (openAdjunction ell c j).counit.app
                  ((c.smoothSource ell s.f s.dim.val).obj K.obj)) ≫
            (a c s).trace ell K

/-- The canonical scalar functor on the full bounded subcategories.
Source: coefficient-change paragraph.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def scalarBounded {c c' : Coefficient ell}
    (q : c.bundled.{u} ell ⟶ c'.bundled ell) (W : Scheme.{u})
    (h : ∀ K, property ell c W K → property ell c' W ((scalarSixChange q W).obj K)) :
    c.ctf ell W ⥤ c'.ctf ell W :=
  (property ell c' W).lift ((property ell c W).ι ⋙ scalarSixChange q W)
    (fun K ↦ h K.obj K.property)

/-- The exceptional scalar comparison is the unique counit mate of the actual
compact-support comparison. Its purity equation uses the same comparisons, for
any specified right adjoints with their counit-preserving purity isomorphisms.
This applies to the finite exceptional functor, the integral source itself,
and the bounded restriction of the localizing rational adjoint.
Source: both displayed equations of the coefficient-change paragraph.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def Mates (a : Family.{u} ell) : Prop :=
  ∀ (c c' : Coefficient ell) (q : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell q → ∀ s : Index.{u} ell,
    ∃ hX : ∀ K, property ell c s.X.left K →
      property ell c' s.X.left ((scalarSixChange q s.X.left).obj K),
    ∃ hY : ∀ K, property ell c s.Y.left K →
      property ell c' s.Y.left ((scalarSixChange q s.Y.left).obj K),
    ∃ hq : c.integralMap ell ≫ q.hom.hom = c'.integralMap ell,
    ∃ p : ScalarLineCoordinates ell q hq s.X.left,
    ∃ b : support ell c s.compactification (a c s).support_closed ⋙
          scalarBounded ell q s.Y.left hY ≅
        scalarBounded ell q s.X.left hX ⋙
          support ell c' s.compactification (a c' s).support_closed,
      (∀ K, (b.hom.app K).hom = (scalarSupportMap q s.compactification).app K.obj) ∧
      ∀ (H : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left)
        (H' : c'.ctf ell s.Y.left ⥤ c'.ctf ell s.X.left)
        (e : support ell c s.compactification (a c s).support_closed ⊣ H)
        (e' : support ell c' s.compactification (a c' s).support_closed ⊣ H')
        (g : source ell c s.f s.dim.val (a c s).source_closed ≅ H)
        (g' : source ell c' s.f s.dim.val (a c' s).source_closed ≅ H'),
        CounitCompatible (a c s).adjunction e g →
        CounitCompatible (a c' s).adjunction e' g' →
        ∃! z : H ⋙ scalarBounded ell q s.X.left hX ≅
            scalarBounded ell q s.Y.left hY ⋙ H',
          (∀ K,
            (support ell c' s.compactification (a c' s).support_closed).map
                (z.hom.app K) ≫ e'.counit.app ((scalarBounded ell q s.Y.left hY).obj K) =
              b.inv.app (H.obj K) ≫
                (scalarBounded ell q s.Y.left hY).map (e.counit.app K)) ∧
          ∀ K,
            ((scalarBounded ell q s.X.left hX).map (g.hom.app K)).hom ≫
                (z.hom.app K).hom =
              sourceScalar ell q s.f s.dim.val hq p K.obj ≫
                (g'.hom.app ((scalarBounded ell q s.Y.left hY).obj K)).hom

/-- The normalized smooth source map on an isomorphism square, including a
change of base field. Only the actual scheme square enters the map.
Source: final naturality paragraph.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def isoSource (c : Coefficient ell) (s t : Index.{u} ell)
    (w : t.X.left ⟶ s.X.left) (v : t.Y.left ⟶ s.Y.left)
    (sq : CommSq w t.f s.f v) (hd : s.dim = t.dim)
    (p : LinePullCoordinates ell c w) (K : c.derived ell s.Y.left) :
    (actualPull (c.obj ell) w).obj ((c.smoothSource ell s.f s.dim.val).obj K) ≅
      (c.smoothSource ell t.f t.dim.val).obj ((actualPull (c.obj ell) v).obj K) :=
  (Functor.Monoidal.μIso (actualPull (c.obj ell) w) _ _).symm ≪≫
    tensorIso ((CondensedRing.pullbackSquareComparison (c.obj ell) sq).symm.app K)
      (p.derived ell s.dim.val) ≪≫
    eqToIso (congrArg (fun d : Fin 2 ↦
      (c.smoothSource ell t.f d.val).obj ((actualPull (c.obj ell) v).obj K)) hd)

/-- The counits commute with the canonical compactification reindexing cube.
The two geometric indices may use different fields; thus base-field
isomorphisms are included without a positive-characteristic restriction.
Source: final naturality paragraph and compactification reindexing.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def Isomorphisms (a : Family.{u} ell) : Prop :=
  ∀ (c : Coefficient ell) (s t : Index.{u} ell)
    (w : t.X.left ⟶ s.X.left) (v : t.Y.left ⟶ s.Y.left)
    [IsIso w] [IsIso v] (sq : CommSq w t.f s.f v) (hd : s.dim = t.dim),
    ∃ p : LinePullCoordinates ell c w,
    ∀ reindex : CompactificationReindexing.Square s.compactification t.compactification w v,
    ∀ K : c.ctf ell s.Y.left,
    ∃ hK : property ell c t.Y.left ((actualPull (c.obj ell) v).obj K.obj),
      (actualPull (c.obj ell) v).map ((a c s).trace ell K) =
        (CompactificationReindexing.squareExchange (c.obj ell) reindex).app
            ((c.smoothSource ell s.f s.dim.val).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) t.compactification).map (isoSource ell c s t w v sq hd p K.obj).hom ≫
          (a c t).trace ell ⟨_, hK⟩

/-- The scalar associator is the adjunction comparison of actual scalar
extensions, with the coefficient-composition equation.
Source: coefficient-change cocycle.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def scalarComp {c c' c'' : Coefficient ell}
    (q : c.bundled.{u} ell ⟶ c'.bundled ell)
    (q' : c'.bundled.{u} ell ⟶ c''.bundled ell) (W : Scheme.{u}) :=
  (Mod.derivedExtendScalarsCompIso
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) q.hom.hom W)
    (coefficientMap (Λ := c'.obj ell) (Λ' := c''.obj ell) q'.hom.hom W)
    (coefficientMap (Λ := c.obj ell) (Λ' := c''.obj ell) (q ≫ q').hom.hom W)
    (coefficientMap_comp q.hom.hom q'.hom.hom W).symm).symm

/-- Actual compact-support and purity-source arrows obey the scalar cocycle.
Unique counit mates therefore obey the exceptional cocycle with these same
associators. This includes finite quotient composition and both extensions.
Source: coefficient-change paragraph.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
def ScalarCocycles : Prop :=
  ∀ (c c' c'' : Coefficient ell)
    (q : c.bundled.{u} ell ⟶ c'.bundled ell)
    (q' : c'.bundled.{u} ell ⟶ c''.bundled ell),
    IsListedScalarCoefficientMap ell q → IsListedScalarCoefficientMap ell q' →
    ∀ s : Index.{u} ell,
      (∀ M : c.ctf ell s.X.left,
        Etale.FiniteSmoothPurity.QuotientCocycle
          (scalarSixChange q s.X.left) (scalarSixChange q' s.X.left)
          (scalarSixChange (q ≫ q') s.X.left)
          (scalarSixChange q s.Y.left) (scalarSixChange q' s.Y.left)
          (scalarSixChange (q ≫ q') s.Y.left)
          (scalarComp ell q q' s.X.left) (scalarComp ell q q' s.Y.left)
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification)
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification)
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c''.obj ell) s.compactification)
          (scalarSupportMap q s.compactification).app
          (scalarSupportMap q' s.compactification).app
          (scalarSupportMap (q ≫ q') s.compactification).app M.obj) ∧
      ∃ (hq : c.integralMap ell ≫ q.hom.hom = c'.integralMap ell)
        (hq' : c'.integralMap ell ≫ q'.hom.hom = c''.integralMap ell)
        (hqq : c.integralMap ell ≫ (q ≫ q').hom.hom = c''.integralMap ell)
        (p : ScalarLineCoordinates ell q hq s.X.left)
        (p' : ScalarLineCoordinates ell q' hq' s.X.left)
        (pp : ScalarLineCoordinates ell (q ≫ q') hqq s.X.left),
      ∀ K : c.ctf ell s.Y.left,
        Etale.FiniteSmoothPurity.QuotientCocycle
          (scalarSixChange q s.Y.left) (scalarSixChange q' s.Y.left)
          (scalarSixChange (q ≫ q') s.Y.left)
          (scalarSixChange q s.X.left) (scalarSixChange q' s.X.left)
          (scalarSixChange (q ≫ q') s.X.left)
          (scalarComp ell q q' s.Y.left) (scalarComp ell q q' s.X.left)
          (c.smoothSource ell s.f s.dim.val)
          (c'.smoothSource ell s.f s.dim.val)
          (c''.smoothSource ell s.f s.dim.val)
          (sourceScalar ell q s.f s.dim.val hq p)
          (sourceScalar ell q' s.f s.dim.val hq' p')
          (sourceScalar ell (q ≫ q') s.f s.dim.val hqq pp) K.obj

/-- Transport the given general-base finite system to the native integral,
finite-extension and finite-subextension-valued algebraic-closure coefficients.
The family is uniquely fixed by its finite trace normalization and scalar maps;
this includes independence of lattices and descent stages.
Source: current blueprint sk-thm-purity-transport Steps 1--4, and
thm-a1-curve-perverse-heart Step 2.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport).

Proof: form the adjunction on normalized finite towers, with its specified
finite units and counits and quotient cocycle. Derived completeness and the
finite-Tor coefficient Hom comparison identify its Hom bijection with the
actual native integral Hom bijection via reduction and derived inverse limit.
The actual compactification-operation comparisons identify its functor with
Rp_*D(i_!), rather than with a completed replacement. Localize the balanced Hom
comparison and use bounded-below filtered-colimit continuity of global sections
to extend every adjunction map to E, independently of lattices. Descend each
finite collection of objects and maps over the algebraic closure to a common
finite subextension; coefficient Hom comparison and continuity of sections give
independence of that subextension and all adjunction identities. Proper direct
image preserves coproducts on the localizing closure and open extension preserves
its generators. General-field Brown representability and objectwise
right-adjoint assembly give the localizing right adjoint. The bounded counit,
triangles, coproducts and a localizing five-lemma argument identify its bounded
restriction uniquely with J. The canonical compact-support scalar map and its
counit mate obey the displayed purity equation at finite levels; the tower,
localization and finite-subextension comparisons carry it and its cocycle to
all coefficients. The open derived adjunction and its compositor give source
restriction. Compactification reindexing and root-normalized Tate pullback give
scheme-isomorphism and base-field-isomorphism naturality. Faithfulness of
normalized reductions, followed by localization and common-stage descent,
proves uniqueness of the same normalized family. No absolute cohomological
dimension bound on the perfect base field is used.
-/
theorem finite_to_condensed_smooth_adjunction_transport :
    ∃ a : Family.{u} ell,
      FiniteNormalized ell a ∧ Scalars ell a ∧ Mates ell a ∧ Isomorphisms ell a ∧
      (∀ (s : Index.{u} ell) (E : PadicAlgCl.FiniteIntermediateField ell),
        Localizing ell a (.rational E) s ∧ OpenRestriction ell a (.rational E) s) ∧
      (∀ s : Index.{u} ell,
        Localizing ell a (.closure) s ∧ OpenRestriction ell a (.closure) s) ∧
      ScalarCocycles.{u} ell := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralFieldSmoothTransport
