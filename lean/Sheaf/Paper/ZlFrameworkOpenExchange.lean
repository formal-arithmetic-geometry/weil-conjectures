/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ZlCompactificationOpenDiagram
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.FdPullbackComparison
public import Sheaf.Paper.CompleteProetaleStrictTowerRealization

/-! # Framework open exchange in its own coefficient presentation
Source: thm-cbc-qbar.proof.md, integral strict quotient construction
(blueprint: def-zl-framework-open-exchange).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ZlFrameworkPbc
open PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary pullback with the framework completed coefficient sheaf.
Source: Stacks 099N(5) (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkModulePull {U T : Scheme.{u}} (h : U ⟶ T) :=
  proEtaleRingModulePullback h ((completed l E).ring T)
    ((completed l E).ring U) ((completed l E).pull h)

/-- The canonical quotient-unit/Roos normalization. It specifies every first-coordinate
projection on inverse-image generators and the entire shifted coordinate as zero.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange). -/
def FrameworkPullChainSpec {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P) : Prop :=
  (∀ (n : ℕ) (i : ℤ) (V : T.ProEt) (x : (P.X i).val.obj (op V)),
    ((ξ ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
      Pi.π (fun n ↦
        ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)) n).f i).val.app
        (op ((proEtaleBaseChange h).obj V))
      (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
          (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x)) ∧
  (∀ (i j : ℤ) (hij : i + -1 = j), ξ.f i ≫
    (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).v
        i j hij = 0)

/-- The quotient-unit comparison is uniquely determined before localization.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange).
Proof: apply inverse image to the quotient augmentation x maps to 1 tensor x at
all levels simultaneously. These maps commute with quotient transitions, so the
first-coordinate product map and zero shifted coordinate form a chain map to Roos.
The inverse-image generators generate after sheafification. Product projections
and the two cocone coordinates therefore determine the chain map uniquely. -/
theorem frameworkPullChain_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ∃! ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P,
      FrameworkPullChainSpec l E h P ξ := by
  sorry

/-- The specified whole quotient-diagram augmentation into its Roos realization.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange). -/
def frameworkPullChain {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :=
  (frameworkPullChain_existsUnique l E h P).exists.choose

/-- Open inverse image preserves the completed constructible realization, with the
whole quotient-unit normalization. No PBC presentation or comparison enters this type.
Source: Stacks 099N(5), 09BQ (blueprint: def-zl-framework-open-exchange).
Proof: open inverse image is exact and preserves products. Apply it to the strict
quotient diagram of a flat K-flat representative. The quotient-unit map just
constructed becomes its canonical completion augmentation. Complete constructible
inputs have invertible augmentation; the Roos product and shifted coordinates
identify it with the defining integral pullback realization. Descent from good
representatives supplies naturality and uniqueness with this equation. -/
theorem frameworkOpenPullRealization_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∃! a : (sfIntegralConstructible l E T).ι ⋙ pull (completed l E) h ≅
      constructibleIntegralPullback l E h ⋙ (sfIntegralConstructible l E U).ι,
      ∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (hP : sfIntegralConstructible l E T (DerivedCategory.Q.obj P.obj)),
        a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
          (integralDerivedPullbackComparison l E h).hom.app P =
        (frameworkModulePull l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (frameworkPullChain l E h P.obj) := by
  sorry

/-- The framework pullback realization fixed by quotient and shifted Roos coordinates.
Source: Stacks 099N(5) (blueprint: def-zl-framework-open-exchange). -/
def frameworkOpenPullRealization {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :=
  (frameworkOpenPullRealization_existsUnique l E h).exists.choose

/-- Framework pullback around a commutative square, using the specified coefficient
compositors. Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkSquare {A B C T : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ T) (d : C ⟶ T)
    (h : a ≫ c = b ≫ d) :
    pull (completed l E) c ⋙ pull (completed l E) a ≅
      pull (completed l E) d ⋙ pull (completed l E) b :=
  (geometricPullComposition (completed l E) a c (completedPull_comp l E a c)).symm ≪≫
    eqToIso (congrArg (fun g ↦ pull (completed l E) g) h) ≪≫
    geometricPullComposition (completed l E) b d (completedPull_comp l E b d)

variable (D : FiniteFieldDatum.{u}) (G : OpenDiagram D l)

/-- The framework proper adjunction mate; it is fixed before any endpoint comparison.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkProperMate :
    push (completed l E) G.c.g ⋙ pull (completed l E) G.v ⟶
      pull (completed l E) G.w ⋙ push (completed l E) G.c'.g :=
  mateEquiv
    (proEtaleRingDerivedAdjunction G.c.g _ _ ((completed l E).pull G.c.g))
    (proEtaleRingDerivedAdjunction G.c'.g _ _ ((completed l E).pull G.c'.g))
    (frameworkSquare l E G.w G.c'.g G.c.g G.v G.properSquare.w).inv

/-- Inverse open exchange, defined by the framework open-adjunction unit transpose.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange). -/
def frameworkOpenMate :
    pull (completed l E) G.u ⋙ (openExtension (completed l E) G.c'.i).mapDerivedCategory ⟶
      (openExtension (completed l E) G.c.i).mapDerivedCategory ⋙ pull (completed l E) G.w :=
  ((mateEquiv (openDerivedAdjunction (completed l E) G.c.i)
    (openDerivedAdjunction (completed l E) G.c'.i)).symm
      (TwoSquare.mk _ _ _ _
        (frameworkSquare l E G.u G.c'.i G.c.i G.w G.openSquare.w).hom)).natTrans

/-- The specified open mate is invertible on a Cartesian open square.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange).
Proof: restriction and direct image identify sections on the same pulled-back test
object. The conjugate comparison of their open left adjoints is invertible; its
unit transpose is exactly frameworkOpenMate. The triangle identities identify the
inverse. Exact localization preserves this equation on the whole quotient diagram. -/
theorem frameworkOpenMate_isIso : IsIso (frameworkOpenMate l E D G) := by
  sorry

/-- Proper mate first, then the framework open-adjunction comparison. All functors
use completed framework coefficients. The qcqs support and quotient-unit pullback
realizations below identify its endpoints with the actual recorded Roos endpoints.
Source: thm-cbc-qbar.proof.md, integral ordered exchange
(blueprint: def-zl-framework-open-exchange). -/
def frameworkAmbientExchange :
    image (completed l E) G.c ⋙ pull (completed l E) G.v ⟶
      pull (completed l E) G.u ⋙ image (completed l E) G.c' :=
  Functor.whiskerLeft (openExtension (completed l E) G.c.i).mapDerivedCategory
      (frameworkProperMate l E D G) ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (frameworkOpenMate l E D G) (frameworkOpenMate_isIso l E D G))
      (push (completed l E) G.c'.g)


/-- Framework inverse image on strict towers, before localization.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkTowerPull {U T : Scheme.{u}} (h : U ⟶ T) :=
  exchangeTowerPull h ((completed l E).ring T) ((completed l E).ring U)
    ((completed l E).pull h)

/-- Framework direct image on the one derived category of strict diagrams.
Source: Stacks 0A07 (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkTowerPush {U T : Scheme.{u}} (h : U ⟶ T) :=
  exchangeTowerPush h ((completed l E).ring T) ((completed l E).ring U)
    ((completed l E).pull h)

/-- Extension by zero of entire framework diagrams, with every transition retained.
Source: Stacks 03DI (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkTowerOpen {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (openExtension (completed l E) j)).mapDerivedCategory

/-- The open adjunction on framework diagrams, derived from the ordinary unit.
Source: Stacks 03DI (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerOpenAdj {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    frameworkTowerOpen l E j ⊣ frameworkTowerPull l E j :=
  Adjunction.ofNatIsoRight
    (((openAdjunction (completed l E) j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction)
    (exchangeTowerModulePull j ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull j)).rightDerivedFunctorIsoMapDerivedCategory

/-- The two framework coefficient paths agree over a commutative Cartesian square.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange).
Proof: completedPull_comp identifies each path with the coefficient map for its
composite. The supplied commutativity equality identifies these composites, hence
their inverse-image coefficient maps. This proves heterogeneous equality without
choosing another coefficient identification. -/
theorem frameworkRingedSquare_coherent {A B C T : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ T} {d : C ⟶ T}
    (sq : ChosenCartesianSquare a b c d) :
    HEq (proEtaleRingCompositeCoefficients a c ((completed l E).ring T)
      ((completed l E).ring B) ((completed l E).ring A)
      ((completed l E).pull c) ((completed l E).pull a))
      (proEtaleRingCompositeCoefficients b d ((completed l E).ring T)
        ((completed l E).ring C) ((completed l E).ring A)
        ((completed l E).pull d) ((completed l E).pull b)) := by
  sorry

/-- The ringed square in the framework's own completed presentation.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkRingedSquare {A B C T : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ T} {d : C ⟶ T}
    (sq : ChosenCartesianSquare a b c d) : StrictTowerRingedSquare sq where
  RY := (completed l E).ring T
  RX := (completed l E).ring B
  RY' := (completed l E).ring C
  RX' := (completed l E).ring A
  cf := (completed l E).pull c
  cg := (completed l E).pull d
  cg' := (completed l E).pull a
  cf' := (completed l E).pull b
  coherent := frameworkRingedSquare_coherent l E sq

/-- The framework proper mate on the whole strict coefficient diagram.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerProperMate :=
  (frameworkRingedSquare l E G.properSquare).exchangeTowerMate

/-- The inverse open comparison, transposed under the framework tower adjunction.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerOpenMate :
    frameworkTowerPull l E G.u ⋙ frameworkTowerOpen l E G.c'.i ⟶
      frameworkTowerOpen l E G.c.i ⋙ frameworkTowerPull l E G.w :=
  ((mateEquiv (frameworkTowerOpenAdj l E G.c.i)
    (frameworkTowerOpenAdj l E G.c'.i)).symm
      (TwoSquare.mk _ _ _ _
        ((frameworkRingedSquare l E
          G.openSquare.toChosenCartesianSquare).exchangeTowerSquare.inv))).natTrans

/-- Cartesian open exchange is invertible already on framework strict diagrams.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange).
Proof: the ordinary open unit mate is the extension of the identity on the same
pulled-back test objects. Its inverse has the same sectionwise description.
Termwise application retains the transition maps, and exact localization carries
the two inverse identities to the derived diagram category. -/
theorem frameworkTowerOpenMate_isIso : IsIso (frameworkTowerOpenMate l E D G) := by
  sorry

/-- The ordered framework exchange, proper mate first and then the open comparison,
formed before either total inverse limit or finite evaluation.
Source: thm-cbc-qbar.proof.md (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerExchange :
    frameworkTowerOpen l E G.c.i ⋙ frameworkTowerPush l E G.c.g ⋙
        frameworkTowerPull l E G.v ⟶
      frameworkTowerPull l E G.u ⋙ frameworkTowerOpen l E G.c'.i ⋙
        frameworkTowerPush l E G.c'.g :=
  Functor.whiskerLeft (frameworkTowerOpen l E G.c.i) (frameworkTowerProperMate l E D G) ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (frameworkTowerOpenMate l E D G)
        (frameworkTowerOpenMate_isIso l E D G)) (frameworkTowerPush l E G.c'.g)

/-- The actual strict quotient diagram of an ordinary framework module. Its
transition is the existing sheafified quotient map s tensor x ↦ rho(s) tensor x.
Source: Bhatt--Scholze 3.5.2 (blueprint: def-zl-framework-open-exchange). -/
def frameworkModuleQuotientTower (W : Scheme.{u}) :
    integralTowerModules l E W ⥤ exchangeTowers W ((completed l E).ring W) :=
  (Functor.ofOpSequence (X := fun n ↦ sfReductionRestricted l E W n)
    (sfReductionTransition l E W)).flip

/-- Additivity of the quotient diagram, read at every index before localization.
Source: Stacks 03CZ (blueprint: def-zl-framework-open-exchange).
Proof: each scalar extension and restriction is additive. The tower maps and
addition are pointwise, so their composites preserve zero and sums. -/
theorem frameworkModuleQuotientTower_additive (W : Scheme.{u}) :
    (frameworkModuleQuotientTower l E W).Additive := by
  sorry

attribute [instance] frameworkModuleQuotientTower_additive

/-- One simultaneous quotient complex, localized in the category of strict towers.
It is applied to flat K-flat representatives, never to independently chosen reductions.
Source: Bhatt--Scholze 3.5.2 (blueprint: def-zl-framework-open-exchange). -/
def frameworkStrictQuotients (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :=
  DerivedCategory.Q.obj
    (((frameworkModuleQuotientTower l E W).mapHomologicalComplex (.up ℤ)).obj P)

/-- Framework direct-image/total-limit comparison, fixed as the adjunction conjugate
of the constant-diagram inverse-image comparison, including its ordinary units.
Source: Stacks 0A07 (blueprint: def-zl-framework-open-exchange). -/
def frameworkPushLimit {U T : Scheme.{u}} (h : U ⟶ T) :
    completedRlim U ((completed l E).ring U) ⋙ push (completed l E) h ≅
      frameworkTowerPush l E h ⋙ completedRlim T ((completed l E).ring T) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction h _ _ ((completed l E).pull h)).comp
      (cbcRealizationLimitAdj U ((completed l E).ring U)))
    ((cbcRealizationLimitAdj T ((completed l E).ring T)).comp
      (exchangeTowerAdjunction h _ _ ((completed l E).pull h)))
    (cbcRealizationConst (frameworkModulePull l E h)).symm

/-- Source endpoint on the framework diagram, by open/limit, proper/limit and
inverse-image/limit in that order. All are the canonical constant-diagram mates.
Source: Stacks 09BP, 0A07 (blueprint: def-zl-framework-open-exchange). -/
def frameworkStrictSource
    (M : DerivedCategory (exchangeTowers G.X ((completed l E).ring G.X))) :
    (pull (completed l E) G.v).obj
        ((image (completed l E) G.c).obj
          ((completedRlim G.X ((completed l E).ring G.X)).obj M)) ⟶
      (completedRlim G.V ((completed l E).ring G.V)).obj
        ((frameworkTowerPull l E G.v).obj ((frameworkTowerPush l E G.c.g).obj
          ((frameworkTowerOpen l E G.c.i).obj M))) :=
  (pull (completed l E) G.v).map
      ((push (completed l E) G.c.g).map
        ((cbcRealizationLimitMap (openExtension (completed l E) G.c.i)).app M)) ≫
    (pull (completed l E) G.v).map
      ((frameworkPushLimit l E G.c.g).hom.app ((frameworkTowerOpen l E G.c.i).obj M)) ≫
    (cbcRealizationLimitMap (frameworkModulePull l E G.v)).app
      ((frameworkTowerPush l E G.c.g).obj ((frameworkTowerOpen l E G.c.i).obj M))

/-- Target endpoint uses the framework inverse-image/limit, open/limit and
proper/limit comparisons, with the same ordinary units as the source.
Source: Stacks 09BP, 0A07 (blueprint: def-zl-framework-open-exchange). -/
def frameworkStrictTarget
    (M : DerivedCategory (exchangeTowers G.X ((completed l E).ring G.X))) :
    (image (completed l E) G.c').obj
        ((pull (completed l E) G.u).obj
          ((completedRlim G.X ((completed l E).ring G.X)).obj M)) ⟶
      (completedRlim G.V ((completed l E).ring G.V)).obj
        ((frameworkTowerPush l E G.c'.g).obj ((frameworkTowerOpen l E G.c'.i).obj
          ((frameworkTowerPull l E G.u).obj M))) :=
  (push (completed l E) G.c'.g).map
      (((openExtension (completed l E) G.c'.i).mapDerivedCategory).map
        ((cbcRealizationLimitMap (frameworkModulePull l E G.u)).app M)) ≫
    (push (completed l E) G.c'.g).map
      ((cbcRealizationLimitMap (openExtension (completed l E) G.c'.i)).app
        ((frameworkTowerPull l E G.u).obj M)) ≫
    (frameworkPushLimit l E G.c'.g).hom.app
      ((frameworkTowerOpen l E G.c'.i).obj ((frameworkTowerPull l E G.u).obj M))

/-- The whole strict-diagram normalization of the framework ambient exchange.
This equation is in the derived strict-diagram category followed by total Rlim;
it does not infer equality of maps from their separate finite evaluations.
Source: thm-cbc-qbar.proof.md, ordered quotient-diagram exchange
(blueprint: def-zl-framework-open-exchange).
Proof: transpose the proper map using the tower adjunction. The conjugate defining
frameworkPushLimit preserves its unit and counit, so the proper square commutes
before evaluation. Transpose the open map with frameworkTowerOpenAdj: the
constant-diagram mate preserves the open unit, hence this square also commutes.
Compose in the stated proper-then-open order. Functorial total inverse limit
preserves the resulting equality. In particular it holds on the strict quotient
complex of one flat K-flat representative, with every transition retained. -/
theorem frameworkAmbientExchange_strict
    (M : DerivedCategory (exchangeTowers G.X ((completed l E).ring G.X))) :
    frameworkStrictSource l E D G M ≫
        (completedRlim G.V ((completed l E).ring G.V)).map
          ((frameworkTowerExchange l E D G).app M) =
      (frameworkAmbientExchange l E D G).app
          ((completedRlim G.X ((completed l E).ring G.X)).obj M) ≫
        frameworkStrictTarget l E D G M := by
  sorry

/-- The framework exchange on its recorded support and pullback endpoints. The source
and target factors are exclusively the framework's projection-normalized support and
whole quotient-unit pullback realizations. There is no coefficient-presentation J,
comparison S or T, or completed PBC exchange in its defining equation.
Source: thm-cbc-qbar.proof.md (blueprint: def-zl-framework-open-exchange). -/
@[irreducible] def frameworkExchange (hl : l ≠ D.p)
    (K : sfIntegralConstructibleCategory l E G.X) :
    ((constructibleIntegralPullback l E G.v).obj
      ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
        G.c E).obj K)).obj ⟶
    ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
      G.c' E).obj ((constructibleIntegralPullback l E G.u).obj K)).obj :=
  (frameworkOpenPullRealization l E G.v).inv.app
      ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) G.c E).obj K) ≫
    (pull (completed l E) G.v).map
      ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) G.c).inv.app K) ≫
    (frameworkAmbientExchange l E D G).app K.obj ≫
    (image (completed l E) G.c').map
      ((frameworkOpenPullRealization l E G.u).hom.app K) ≫
    (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) G.c').hom.app
      ((constructibleIntegralPullback l E G.u).obj K)

end WeilConjectures.ZlFrameworkPbc
