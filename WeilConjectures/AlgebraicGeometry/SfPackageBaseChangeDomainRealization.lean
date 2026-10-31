/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.ECoefficientSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.QbarCoefficientSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.CompleteCompactSupportProetale
public import WeilConjectures.AlgebraicGeometry.FiniteExtensionCompactSupportBaseChange
public import WeilConjectures.AlgebraicGeometry.QbarCompactSupportBaseChange
public import WeilConjectures.AlgebraicGeometry.ExchangeFunctoriality
public import WeilConjectures.AlgebraicGeometry.FiniteMateDomain
public import WeilConjectures.AlgebraicGeometry.SfBcCompletedMateDomain
public import WeilConjectures.AlgebraicGeometry.QbarProperBaseChange
import WeilConjectures.AlgebraicGeometry.SfBaseChangeGeometryHypotheses
import WeilConjectures.AlgebraicGeometry.CanonicalFiniteLevelCompactSupportBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange

/-! # Geometric and coefficient-domain realization of base change

Source: blueprint sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization).

The clause predicates below only collect assertions about the published canonical maps.
They introduce no coefficient category, exchange, lattice, or comparison construction.

## Main definitions

* `sfPackageBaseChangeGeometry`: geometric hypotheses on the actual square.
* `sfPackageBaseChangeFinite`: finite exchange and witnessed comparison equations.
* `sfPackageBaseChangeCompleted`: completed mate and conditional constructible landing.
* `sfPackageBaseChangeFields`: rational and common-stage lattice domains.
* `sfPackageBaseChangeCompactSupport`: compact-support domains at all stages.

## Main statements

* `sfPackageBaseChangeDomainRealization`: the package realization and named-map coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures

private theorem scalarBetween_map_localization
    {R : Type*} [CommRing R] (p : R)
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [Linear R A] [Linear R B] (F : A ⥤ B) [F.Additive] [F.Linear R]
    {J K : A} (a : J ⟶ K) :
    (ScalarLocalization.between R p F).map
        ((ScalarLocalization.localization R A p).map a) =
      (ScalarLocalization.localization R B p).map (F.map a) := by
  dsimp only [ScalarLocalization.between, ScalarLocalization.betweenHom,
    ScalarLocalization.localization]
  rw [LinearMap.baseChange_tmul]
  rfl

private theorem naturality_representative
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B} (α : F ⟶ G)
    {M N : A} (e : M ≅ N) (a : F.obj M ⟶ G.obj M) (ha : a = α.app M) :
    a ≫ 𝟙 _ ≫ G.map e.hom = (𝟙 _ ≫ F.map e.hom) ≫ α.app N := by
  rw [ha]
  simpa only [Category.id_comp] using (α.naturality e.hom).symm

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)

section Square
variable {X X' Y Y' : SixFunctorSpace D}
  [IsSeparated X.obj.hom] [IsSeparated X'.obj.hom]
  [IsSeparated Y.obj.hom] [IsSeparated Y'.obj.hom]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  [IsSeparated g'.hom.left] [LocallyOfFiniteType g'.hom.left] [QuasiCompact g'.hom.left]
  [IsSeparated f'.hom.left] [LocallyOfFiniteType f'.hom.left] [QuasiCompact f'.hom.left]
  (sq : ChosenCartesianSquare g'.hom.left f'.hom.left f.hom.left g.hom.left)

/-- The geometric conclusions, including empty fibres and quasi-compact open factors.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization). -/
def sfPackageBaseChangeGeometry : Prop :=
    (∀ T : Scheme.{u}, (T = X.obj.left ∨ T = Y.obj.left ∨ T = X'.obj.left ∨ T = Y'.obj.left) →
      IsNoetherian T ∧ CompactSpace T ∧ QuasiSeparatedSpace T ∧
      (∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)) ∧
      (∀ t : T, IsUnit (C.l : T.presheaf.stalk t))) ∧
    (QuasiCompact f.hom.left ∧ QuasiSeparated f.hom.left) ∧
    (QuasiCompact g.hom.left ∧ QuasiSeparated g.hom.left) ∧
    (QuasiCompact g'.hom.left ∧ QuasiSeparated g'.hom.left) ∧
    (QuasiCompact f'.hom.left ∧ QuasiSeparated f'.hom.left) ∧
    (∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y.obj.left),
      topologicalKrullDim (↑(pullback f.hom.left y) : Type u) ≤ (e : WithBot ℕ∞) ∧
      (IsEmpty (↑(pullback f.hom.left y) : Type u) →
        topologicalKrullDim (↑(pullback f.hom.left y) : Type u) = ⊥)) ∧
    (IsProper f.hom.left → IsProper f'.hom.left) ∧
    (∀ T : Scheme.{u}, (T = X.obj.left ∨ T = Y.obj.left ∨ T = X'.obj.left ∨ T = Y'.obj.left) →
      ∀ (U : Scheme.{u}) (h : U ⟶ T),
        IsSeparated h → LocallyOfFiniteType h → QuasiCompact h →
        ∃ c : Compactification h, QuasiCompact c.i)

/-- Finite torsion exchange and the exact equations for retained etale-origin witnesses.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization). -/
def sfPackageBaseChangeFinite : Prop :=
  (IsProper f.hom.left ∨ Smooth g.hom.left) →
    (∀ L : DerivedCategory.Plus
        (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E
          n))),
      IsIso ((FiniteMateDomain.etaleMate C E n sq).app L) ∧
      (D+(Etale.moduleAbelianForget (FiniteMateDomain.Coefficient C E n) Y'.obj.left).map
          ((FiniteMateDomain.etaleMate C E n sq).app L) ≫
        (Etale.moduleAbelianDerivedExchangeTargetIso (FiniteMateDomain.Coefficient C E n)
          g'.hom.left f'.hom.left L).hom =
      (Etale.moduleAbelianDerivedExchangeSourceIso (FiniteMateDomain.Coefficient C E n)
          f.hom.left g.hom.left L).hom ≫
        (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D+(Etale.moduleAbelianForget (FiniteMateDomain.Coefficient C E n) X.obj.left).obj L)) ∧
      ((FiniteMateDomain.comparison C E n Y'.obj.left).map
          (DerivedCategory.Plus.ι.map ((FiniteMateDomain.etaleMate C E n sq).app L)) ≫
        (FiniteMateDomain.targetIso C E n g'.hom.left f'.hom.left).hom.app L =
      (FiniteMateDomain.sourceIso C E n f.hom.left g.hom.left).hom.app L ≫
        (FiniteMateDomain.ambientMate C E n sq).app ((FiniteMateDomain.comparison C E n
          X.obj.left).obj L.obj))) ∧
    (∀ K : DerivedCategory.Plus
        (Sheaf (ProEt.topology X.obj.left) (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E
          n))),
      ∀ W : FixedEtaleOriginWitness X.obj.left (FiniteMateDomain.Coefficient C E n) K,
      (IsProper f.hom.left ∨
        (Smooth g.hom.left ∧ Etale.DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n)) X.obj.left W.complex.obj)) →
      IsIso ((FiniteMateDomain.ambientMate C E n sq).app K.obj) ∧
      (FiniteMateDomain.ambientMate C E n sq).app K.obj =
        (R(ProEtale.lowerStar (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n)) f.hom.left) ⋙
          L(ProEtale.upperStar (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n))
            g.hom.left)).map
            W.iso.inv ≫
        (FiniteMateDomain.sourceIso C E n f.hom.left g.hom.left).inv.app W.complex ≫
        (FiniteMateDomain.comparison C E n Y'.obj.left).map
          (DerivedCategory.Plus.ι.map ((FiniteMateDomain.etaleMate C E n sq).app W.complex)) ≫
        (FiniteMateDomain.targetIso C E n g'.hom.left f'.hom.left).hom.app W.complex ≫
        (L(ProEtale.upperStar (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n))
          g'.hom.left) ⋙
          R(ProEtale.lowerStar (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n))
            f'.hom.left)).map
            W.iso.hom)

/-- Completed ordinary exchange, its reduction and limit equations, and conditional landing.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization). -/
def sfPackageBaseChangeCompleted : Prop :=
    (IsProper f.hom.left → ∀ K : PbcComplete C.l E X.obj.left,
      PbcHasCompatibleEtaleOrigins X.obj.left (pbcIntegralDatum C.l E) K.obj →
      IsIso (sbcExchangeApp C.l E (exchangeTransposeSquare sq) K) ∧
      (∀ n : ℕ,
        (sbcReduction C.l E Y'.obj.left n).map (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
          K).hom ≫
            sbcPushReduction C.l E f'.hom.left n ((sbcPull C.l E g'.hom.left).obj K) ≫
            (sbcFinitePush C.l E f'.hom.left n).map (sbcPullReduction C.l E g'.hom.left n K) =
          sbcPullReduction C.l E g.hom.left n ((sbcPush C.l E f.hom.left).obj K) ≫
            (sbcFinitePull C.l E g.hom.left n).map (sbcPushReduction C.l E f.hom.left n K) ≫
            sbcFiniteExchangeApp C.l E (exchangeTransposeSquare sq) n
              ((sbcReduction C.l E X.obj.left n).obj K.obj)) ∧
      ((sbcExchangeApp C.l E (exchangeTransposeSquare sq) K).hom =
        (sbcStrictSourceComparison C.l E (exchangeTransposeSquare sq) K).hom ≫
          (completedTowerRlim (pbcIntegralDatum C.l E) Y'.obj.left).map
            (sbcStrictExchange C.l E (exchangeTransposeSquare sq) K) ≫
          (sbcStrictTargetComparison C.l E (exchangeTransposeSquare sq) K).hom) ∧
      ((sbcExchangeApp C.l E (exchangeTransposeSquare sq) K).hom =
        (cbcDatumCompletedTransport (pbcIntegralDatum C.l E) g.hom.left).hom.app
            ((sbcPush C.l E f.hom.left).obj K).obj ≫
          ((pbcIntegralDatum C.l E).completedPull g.hom.left).map
            ((sfCompletedMatePushComparison C.l E f.hom.left).hom.app K.obj) ≫
          (pbcIntegralDatum C.l E).completedExchange sq K.obj ≫
          ((pbcIntegralDatum C.l E).push f'.hom.left).map
            ((cbcDatumCompletedTransport (pbcIntegralDatum C.l E) g'.hom.left).inv.app K.obj) ≫
          (sfCompletedMatePushComparison C.l E f'.hom.left).inv.app ((sbcPull C.l E
            g'.hom.left).obj K).obj) ∧
      (PbcIsBoundedConstructibleComplete X.obj.left (pbcIntegralDatum C.l E) K.obj →
        ∃ (hS : PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E)
          ((sbcPull C.l E g.hom.left).obj ((sbcPush C.l E f.hom.left).obj K)).obj)
        (hT : PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E)
          ((sbcPush C.l E f'.hom.left).obj ((sbcPull C.l E g'.hom.left).obj K)).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E))
          (X := ⟨((sbcPull C.l E g.hom.left).obj ((sbcPush C.l E f.hom.left).obj K)).obj, hS⟩)
          (Y := ⟨((sbcPush C.l E f'.hom.left).obj ((sbcPull C.l E g'.hom.left).obj K)).obj, hT⟩)
          (sbcExchangeApp C.l E (exchangeTransposeSquare sq) K).hom))) ∧
    (Smooth g.hom.left → ∀ K : PbcIntegralConstructible C.l E X.obj.left,
      (∀ n : ℕ, ∃ L : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum C.l E) n) X.obj.left,
        Nonempty ((pbcDerivedFunctionRealization X.obj.left (pbcIntegralDatum C.l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum C.l E) n))
            X.obj.left).mapDerivedCategory.obj L.obj) ≅ (sbcReduction C.l E X.obj.left n).obj
              K.obj)) ∧
      IsIso (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
        ((pbcConstructibleInclusion C.l E X.obj.left).obj K)) ∧
      ((∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
        sfCompletedFiniteProfile C.l E Y.obj.left n
          ((sbcFinitePush C.l E f.hom.left n).obj ((sbcReduction C.l E X.obj.left n).obj K.obj))
            a b ∧
        sfCompletedFiniteProfile C.l E Y'.obj.left n
          ((sbcFinitePull C.l E g.hom.left n).obj
            ((sbcFinitePush C.l E f.hom.left n).obj ((sbcReduction C.l E X.obj.left n).obj
              K.obj))) a b ∧
        sfCompletedFiniteProfile C.l E X'.obj.left n
          ((sbcFinitePull C.l E g'.hom.left n).obj ((sbcReduction C.l E X.obj.left n).obj K.obj))
            a b ∧
        sfCompletedFiniteProfile C.l E Y'.obj.left n
          ((sbcFinitePush C.l E f'.hom.left n).obj
            ((sbcFinitePull C.l E g'.hom.left n).obj ((sbcReduction C.l E X.obj.left n).obj
              K.obj))) a b) →
        ∃ (hS : PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E)
          ((sbcPull C.l E g.hom.left).obj ((sbcPush C.l E f.hom.left).obj
            ((pbcConstructibleInclusion C.l E X.obj.left).obj K))).obj)
        (hT : PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E)
          ((sbcPush C.l E f'.hom.left).obj
            ((sbcPull C.l E g'.hom.left).obj ((pbcConstructibleInclusion C.l E X.obj.left).obj
              K))).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E))
          (X := ⟨((sbcPull C.l E g.hom.left).obj
            ((sbcPush C.l E f.hom.left).obj ((pbcConstructibleInclusion C.l E X.obj.left).obj
              K))).obj, hS⟩)
          (Y := ⟨((sbcPush C.l E f'.hom.left).obj
            ((sbcPull C.l E g'.hom.left).obj ((pbcConstructibleInclusion C.l E X.obj.left).obj
              K))).obj, hT⟩)
          (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
            ((pbcConstructibleInclusion C.l E X.obj.left).obj K)).hom)))

attribute [local irreducible] pbcRationalInclusion
  pbcIntegralDatum pbcUniformizer pbcFiniteField
  HasDerivedCategory.standard CategoryTheory.Limits.limit
attribute [local irreducible] sbcRationalLeft sbcRationalRight sbcRationalExchange
attribute [local irreducible] ScalarLocalization.between ScalarLocalization.betweenNat
attribute [local irreducible] Padic.coefficientExtensionIntegers
  pbcConstructibleInclusion
attribute [local irreducible] ProEtale.canonicalFiniteCoefficientCompactSupportExchange
  completedCompactSupportExchange pbcScalarExtension pbcScalarAssociator
attribute [local irreducible] sbcPull sbcPush sbcExchangeApp sbcAdjunction sbcTheta
attribute [local irreducible] PbcQbarExchangePresentation.exchange
  PbcQbarExchangePresentation.atStage StageSystem.Morphism.functor
  StageSystem.Morphism.functorCompIso StageSystem.Morphism.descNatTrans

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Field exchange on the raw rational and common-stage categories, with exact lattice domains.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization). -/
def sfPackageBaseChangeFields : Prop :=
  ∀ [IsNoetherian X.obj.left] [IsNoetherian Y.obj.left]
    [IsNoetherian X'.obj.left] [IsNoetherian Y'.obj.left]
    [dX : Fact (∃ d : ℕ, topologicalKrullDim X.obj.left ≤ (d : WithBot ℕ∞))]
    [_dY : Fact (∃ d : ℕ, topologicalKrullDim Y.obj.left ≤ (d : WithBot ℕ∞))]
    [_dX' : Fact (∃ d : ℕ, topologicalKrullDim X'.obj.left ≤ (d : WithBot ℕ∞))]
    [_dY' : Fact (∃ d : ℕ, topologicalKrullDim Y'.obj.left ≤ (d : WithBot ℕ∞))]
    [iX : Fact (∀ x : X.obj.left, IsUnit (C.l : X.obj.left.presheaf.stalk x))]
    [_iY : Fact (∀ y : Y.obj.left, IsUnit (C.l : Y.obj.left.presheaf.stalk y))]
    [_iX' : Fact (∀ x : X'.obj.left, IsUnit (C.l : X'.obj.left.presheaf.stalk x))]
    [_iY' : Fact (∀ y : Y'.obj.left, IsUnit (C.l : Y'.obj.left.presheaf.stalk y))]
    (hunit : IsUnit (C.l : Γ(Y.obj.left, ⊤))),
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar X.obj.left i) :=
    fun _i ↦ inferInstance
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar Y.obj.left i) :=
    fun _i ↦ inferInstance
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar X'.obj.left i) :=
    fun _i ↦ inferInstance
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left i) :=
    fun _i ↦ inferInstance
  (IsProper f.hom.left →
    (∀ (K : PbcRationalConstructible C.l E X.obj.left)
      (L : IntegralLattice C.l E X.obj.left dX.out iX.out K),
      IsIso ((sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app
        ((pbcRationalInclusion C.l E X.obj.left).obj K)) ∧
      SbcConstructibleExchangeRepresentation C.l E (exchangeTransposeSquare sq)
        dX.out iX.out L) ∧
    (∃ P : PbcQbarExchangePresentation.{u, u} C.l C.Qbar sq,
      (∀ K : pbcQbarCategory.{u, u} C.l C.Qbar X.obj.left, IsIso (P.exchange.app K)) ∧
      (∀ (M : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K : pbcStageCategory.{u, u} C.l C.Qbar X.obj.left M), @IsIso (pbcStageCategory.{u, u} C.l
          C.Qbar Y'.obj.left M)
          (inferInstance : Category.{u + 2}
            (pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left M)) _ _ ((P.Ex.τ M).app K)) ∧
      (∀ (K : pbcQbarCategory.{u, u} C.l C.Qbar X.obj.left)
        (M : Padic.FiniteCoefficientFields C.l C.Qbar) (h : K.stage ≤ M),
        P.exchange.app K = PbcQbarExchangePresentation.atStage.{u, u} C.l C.Qbar sq P K M h))) ∧
  (∀ [Smooth g.hom.left],
    (∀ (K : PbcRationalConstructible C.l E X.obj.left)
      (L : IntegralLattice C.l E X.obj.left dX.out
        (sbcPrimeUnitOnSource C.l f.hom.left hunit) K),
      L.IsFiniteLevelEtaleAdmissible C.l E X.obj.left dX.out
        (sbcPrimeUnitOnSource C.l f.hom.left hunit) →
    IsIso ((sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app ((pbcRationalInclusion
      C.l E X.obj.left).obj K)) ∧
    (sbcTransportedExchange C.l E (exchangeTransposeSquare sq) dX.out (sbcPrimeUnitOnSource C.l
      f.hom.left hunit) L =
      (sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app ((pbcRationalInclusion C.l E
        X.obj.left).obj K)) ∧
    (∀ L' : IntegralLattice C.l E X.obj.left dX.out (sbcPrimeUnitOnSource C.l f.hom.left hunit) K,
      L'.IsFiniteLevelEtaleAdmissible C.l E X.obj.left dX.out (sbcPrimeUnitOnSource C.l
        f.hom.left hunit) →
      sbcTransportedExchange C.l E (exchangeTransposeSquare sq) dX.out (sbcPrimeUnitOnSource C.l
        f.hom.left hunit) L' =
        sbcTransportedExchange C.l E (exchangeTransposeSquare sq) dX.out (sbcPrimeUnitOnSource
          C.l f.hom.left hunit) L) ∧
    (L.IsSquareConstructiblyAdmissible C.l E X.obj.left dX.out (sbcPrimeUnitOnSource C.l
      f.hom.left hunit) (exchangeTransposeSquare sq) →
      SbcConstructibleExchangeRepresentation C.l E (exchangeTransposeSquare sq) dX.out
        (sbcPrimeUnitOnSource C.l f.hom.left hunit) L) ) ∧
    exchangeCommonStageSmoothAtSquare C.l C.Qbar (exchangeTransposeSquare sq) hunit ∧
    (∀ (M : Padic.FiniteCoefficientFields C.l C.Qbar)
      (K : PbcRationalConstructible C.l (pbcFiniteField.{u} C.l C.Qbar M) X.obj.left)
      (L : IntegralLattice C.l (pbcFiniteField.{u} C.l C.Qbar M) X.obj.left dX.out
        (sbcPrimeUnitOnSource C.l f.hom.left hunit) K),
      L.IsSquareConstructiblyAdmissible C.l (pbcFiniteField.{u} C.l C.Qbar M)
        X.obj.left dX.out (sbcPrimeUnitOnSource C.l f.hom.left hunit)
        (exchangeTransposeSquare sq) →
      SbcConstructibleExchangeRepresentation C.l (pbcFiniteField.{u} C.l C.Qbar M)
        (exchangeTransposeSquare sq) dX.out
        (sbcPrimeUnitOnSource C.l f.hom.left hunit) L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compact support at finite, completed, rational, and common stages; g is unrestricted.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization). -/
def sfPackageBaseChangeCompactSupport : Prop :=
  letI : Finite (FiniteMateDomain.Coefficient C E n) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing C.l E n hn)
  (∀ c : Compactification f.hom.left,
    (∀ K : DerivedCategory.Plus (Sheaf X.obj.left.smallEtaleTopology
      (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n))),
      IsIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (FiniteMateDomain.Coefficient C E n)
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd) c).app K)) ∧
    (∀ K : DerivedCategory.Plus (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (FiniteMateDomain.Coefficient C E n))),
      FixedEtaleOriginWitness X.obj.left (FiniteMateDomain.Coefficient C E n) K →
      IsIso ((ProEtale.canonicalFiniteCoefficientCompactSupportExchange C.l E n hn sq c).app
        K.obj))) ∧
  (∀ (c : Compactification f.hom.left) (c' : Compactification f'.hom.left)
    (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g.hom.left)
    (openSquare : OpenImmersionSquare g'.hom.left c'.i c.i gbar)
    (r : ℕ) (a : Fin r → PbcIntegralRing C.l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum C.l E).ideal)
    (K : (cbcCompleteProperty (pbcIntegralDatum C.l E) X.obj.left r a ha).FullSubcategory),
    PbcHasCompatibleEtaleOrigins X.obj.left (pbcIntegralDatum C.l E) K.obj →
    IsIso (completedCompactSupportExchange (pbcIntegralDatum C.l E)
      c c' gbar properSquare openSquare r a ha K)) ∧
  exchangeRationalSupportLaws C.l E ∧
  exchangeCommonStageSupportLaws.{u, u} C.l C.Qbar ∧
  (∀ (c : Compactification f.hom.left) (c' : Compactification f'.hom.left)
    (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g.hom.left)
    (openSquare : OpenImmersionSquare g'.hom.left c'.i c.i gbar),
    ∀ [IsNoetherian X.obj.left] [IsNoetherian Y.obj.left]
      [IsNoetherian X'.obj.left] [IsNoetherian Y'.obj.left]
      [_dX : Fact (∃ d : ℕ, topologicalKrullDim X.obj.left ≤ (d : WithBot ℕ∞))]
      [_dY' : Fact (∃ d : ℕ, topologicalKrullDim Y'.obj.left ≤ (d : WithBot ℕ∞))]
      [_iX : Fact (∀ x : X.obj.left, IsUnit (C.l : X.obj.left.presheaf.stalk x))]
      [_iY' : Fact (∀ y : Y'.obj.left, IsUnit (C.l : Y'.obj.left.presheaf.stalk y))]
      (dimY : ∃ d : ℕ, topologicalKrullDim Y.obj.left ≤ (d : WithBot ℕ∞))
      (dimX' : ∃ d : ℕ, topologicalKrullDim X'.obj.left ≤ (d : WithBot ℕ∞))
      (invY : ∀ y : Y.obj.left, IsUnit (C.l : Y.obj.left.presheaf.stalk y))
      (invX' : ∀ x : X'.obj.left, IsUnit (C.l : X'.obj.left.presheaf.stalk x)),
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar X.obj.left i) :=
    fun _i ↦ inferInstance
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar Y.obj.left i) :=
    fun _i ↦ inferInstance
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar X'.obj.left i) :=
    fun _i ↦ inferInstance
  letI : ∀ i : Padic.FiniteCoefficientFields C.l C.Qbar,
      Category.{u + 2} (pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left i) :=
    fun _i ↦ inferInstance
  Nonempty (CbcQbarExchangeModel.{u, u} C.l C.Qbar c c' gbar properSquare openSquare) ∧
      ∀ D : CbcQbarExchangeModel.{u, u} C.l C.Qbar c c' gbar properSquare openSquare,
      (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : pbcStageCategory.{u, u} C.l C.Qbar
        X.obj.left E),
        @IsIso (pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left E)
          (inferInstance : Category.{u + 2}
            (pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left E)) _ _ ((D.exchange.τ E).app K)) ∧
      IsIso (StageSystem.Morphism.descNatTrans.{u, u + 2, u + 2, u + 2, u + 2}
          (C := pbcStageCategory.{u, u} C.l C.Qbar X.obj.left)
          (D := pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left) D.exchange) ∧
      (∀ K : pbcQbarCategory.{u, u} C.l C.Qbar X.obj.left,
        IsIso ((StageSystem.Morphism.descNatTrans.{u, u + 2, u + 2, u + 2, u + 2}
          (C := pbcStageCategory.{u, u} C.l C.Qbar X.obj.left)
          (D := pbcStageCategory.{u, u} C.l C.Qbar Y'.obj.left) D.exchange).app K)) ∧
      exchangeCommonStageSupportLawsAtSquare C.l C.Qbar c c' gbar properSquare
        openSquare dimY dimX' invY invX')

end Square

set_option cleanup.letToHave false

/-- All clauses of geometric and coefficient-domain realization for the canonical exchanges.

Proof:
1. Apply lem-sf-bc-geometry-hypotheses: the corners are Noetherian, qcqs and finite
   dimensional, ell is invertible, fibres have a nonnegative uniform bound, properness
   survives base change, and Nagata supplies compactifications with qc open factors.
2. Apply lem-sf-bc-adic-ring-domain to the specified valuation ring and uniformizer;
   its positive quotients are finite, torsion and perfect, with the same completed datum.
3. Apply lem-sf-bc-finite-mate-domain at each quotient. Its coefficient-forgetting
   and comparison equations identify the actual mate with the witnessed etale exchange.
4. Apply lem-sf-bc-completed-mate-domain to the compatible reduction witnesses.
   Retain the strict-limit normalization and the four-family interval for smooth landing.
5. Apply lem-sf-bc-field-mate-domain: localize the specified integral exchange and
   descend its common-stage representatives. Retain the admissible lattice and
   square-constructible hypotheses in the smooth case, including finite overfields.
6. Apply lem-sf-bc-compact-support-domain to the chosen compactification. Proper
   exchange on j_!K followed by the canonical open comparison gives the actual compact
   exchange at each stage; its normalized rational and common-stage images agree
   with the cited compact-support theorem maps. No smoothness of g enters.
7. Apply fix-lem-exchanges to these same named maps, on their stated domains.
   It gives the identity, pasting, refinement and composition equations, and the
   finite-datum and completed-model identifications used above.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4) (blueprint: lem-sf-package-base-change-domain-realization). -/
theorem sfPackageBaseChangeDomainRealization
    (S : SixFunctorOperationDatum D C E n hn) :
    (∀ {X X' Y Y' : SixFunctorSpace D}
      [IsSeparated X.obj.hom] [IsSeparated X'.obj.hom]
      [IsSeparated Y.obj.hom] [IsSeparated Y'.obj.hom]
      (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      [IsSeparated g'.hom.left] [LocallyOfFiniteType g'.hom.left] [QuasiCompact g'.hom.left]
      [IsSeparated f'.hom.left] [LocallyOfFiniteType f'.hom.left] [QuasiCompact f'.hom.left]
      (sq : ChosenCartesianSquare g'.hom.left f'.hom.left f.hom.left g.hom.left),
      sfPackageBaseChangeGeometry C f g g' f' ∧
      sfPackageBaseChangeFinite C E n f g g' f' sq ∧
      sfPackageBaseChangeCompleted C E f g g' f' sq ∧
      sfPackageBaseChangeFields C E f g g' f' sq ∧
      sfPackageBaseChangeCompactSupport C E n hn f g g' f' sq) ∧
    exchangeDatumFiniteIdentification D C E n hn S ∧
    exchangeFiniteStageLaws C.l E n hn ∧
    exchangeFiniteCompactIdentification C.l E n hn ∧
    CompletedOrdinaryExchangeLaws (pbcIntegralDatum C.l E) ∧
    CompletedSupportExchangeLaws (pbcIntegralDatum C.l E) ∧
    exchangeCompletedSupportNaturality (pbcIntegralDatum C.l E) ∧
    exchangeIntegralModelIdentification C.l E ∧
    exchangeCompletedMateLaws C.l E ∧
    exchangeCompletedSquareNaturality C.l E ∧
    exchangeIntegralNormalization C.l E := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨hdatum, hfinite, hfiniteCompact, hord, hsupport, hsupportNat,
      hratSupport, hcommonSupport, _hscalar, hmodel, hmate, hsquare,
      _hcoef, _hscalarSupport, hnormal, _hintSmooth, _hratSmooth, hcommonSmooth⟩ :=
      exchangeFunctoriality.{u, u, u, u} D C E n hn S
    refine ⟨?_, hdatum, hfinite, hfiniteCompact, hord, hsupport, hsupportNat,
      hmodel, hmate, hsquare, hnormal⟩
    intro X X' Y Y' _ _ _ _ f g g' f' _ _ _ _ _ _ _ _ _ _ _ _ sq
    have : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (IsSeparated X.obj.hom)
    have : IsSeparated (Y.obj.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (IsSeparated Y.obj.hom)
    have : IsSeparated (X'.obj.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (IsSeparated X'.obj.hom)
    have : IsSeparated (Y'.obj.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (IsSeparated Y'.obj.hom)
    have : LocallyOfFiniteType X.obj.hom := X.property.1
    have : LocallyOfFiniteType Y.obj.hom := Y.property.1
    have : LocallyOfFiniteType X'.obj.hom := X'.property.1
    have : LocallyOfFiniteType Y'.obj.hom := Y'.property.1
    have : QuasiCompact X.obj.hom := X.property.2
    have : QuasiCompact Y.obj.hom := Y.property.2
    have : QuasiCompact X'.obj.hom := X'.property.2
    have : QuasiCompact Y'.obj.hom := Y'.property.2
    have hgeom : sfPackageBaseChangeGeometry C f g g' f' :=
      sf_baseChange_geometry_hypotheses D C.l C.prime.out C.different
        g'.hom.left f'.hom.left f.hom.left g.hom.left sq
    have hcompleted : sfPackageBaseChangeCompleted C E f g g' f' sq :=
      sfCompletedMateDomain D C.l C.different E X.obj.hom Y.obj.hom
        X'.obj.hom Y'.obj.hom f.hom.left g.hom.left g'.hom.left f'.hom.left
        (Over.w f.hom) (Over.w g.hom) (Over.w g'.hom) (Over.w f'.hom) sq
    refine ⟨hgeom, ?_, hcompleted, ?_, ?_⟩
    · unfold sfPackageBaseChangeFinite
      intro hgeom
      have hf := FiniteMateDomain.finiteMateDomain C E n hn f g g' f' sq hgeom
      with_reducible exact hf
    · intro _ _ _ _ dX dY dX' dY' iX iY iX' iY' hunit
      constructor
      · intro hp
        constructor
        · intro K L
          let K₀ := (pbcConstructibleInclusion C.l E X.obj.left).obj L.integral
          have ho : PbcHasCompatibleEtaleOrigins X.obj.left (pbcIntegralDatum C.l E)
              K₀.obj := L.integral.property.2.2
          have hc := hcompleted.1 hp K₀ ho
          obtain ⟨hiso, _, _, _, hlanding⟩ := hc
          obtain ⟨hB, hD, hγ⟩ := hlanding L.integral.property
          let B : PbcIntegralConstructible C.l E Y'.obj.left :=
            ⟨((sbcPull C.l E g.hom.left).obj ((sbcPush C.l E f.hom.left).obj
              ((pbcConstructibleInclusion C.l E X.obj.left).obj L.integral))).obj, hB⟩
          let J : PbcIntegralConstructible C.l E Y'.obj.left :=
            ⟨((sbcPush C.l E f'.hom.left).obj ((sbcPull C.l E g'.hom.left).obj
              ((pbcConstructibleInclusion C.l E X.obj.left).obj L.integral))).obj, hD⟩
          let γ : B ⟶ J := ObjectProperty.homMk
            (P := PbcIsBoundedConstructibleComplete Y'.obj.left (pbcIntegralDatum C.l E))
            (X := B) (Y := J)
            (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
              ((pbcConstructibleInclusion C.l E X.obj.left).obj L.integral)).hom
          have : IsIso γ := hγ
          have hlocalized : IsIso ((sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app
              ((pbcRationalInclusion C.l E X.obj.left).obj
                ((pbcRationalization X.obj.left (pbcIntegralDatum C.l E)
                  (pbcUniformizer C.l E)).obj L.integral))) := by
            change IsIso ((sbcCompleteRationalize C.l E Y'.obj.left).map
              (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
                ((pbcConstructibleInclusion C.l E X.obj.left).obj L.integral)))
            have := hiso
            infer_instance
          refine ⟨?_, ?_⟩
          · exact (NatTrans.isIso_app_iff_of_iso
              (F := sbcRationalLeft C.l E (f := g.hom.left) (g := f.hom.left))
              (G := sbcRationalRight C.l E (e := g'.hom.left) (h := f'.hom.left))
              (sbcRationalExchange C.l E (exchangeTransposeSquare sq))
              ((pbcRationalInclusion C.l E X.obj.left).mapIso L.rationalization)).mp
                hlocalized
          · let a : (pbcConstructibleInclusion C.l E Y'.obj.left).obj B ≅
                (sbcPull C.l E g.hom.left).obj ((sbcPush C.l E f.hom.left).obj K₀) :=
              Iso.refl _
            let b : (pbcConstructibleInclusion C.l E Y'.obj.left).obj J ≅
                (sbcPush C.l E f'.hom.left).obj ((sbcPull C.l E g'.hom.left).obj K₀) :=
              Iso.refl _
            let β := (pbcRationalization Y'.obj.left (pbcIntegralDatum C.l E)
              (pbcUniformizer C.l E)).mapIso (asIso γ)
            refine ⟨B, J, a, b, β, ?_⟩
            change (pbcRationalInclusion C.l E Y'.obj.left).map
                ((pbcRationalization Y'.obj.left (pbcIntegralDatum C.l E)
                  (pbcUniformizer C.l E)).map γ) ≫
                𝟙 _ ≫ (sbcRationalRight C.l E (e := g'.hom.left) (h := f'.hom.left)).map
                  ((pbcRationalInclusion C.l E X.obj.left).map L.rationalization.hom) =
              (𝟙 _ ≫ (sbcRationalLeft C.l E (f := g.hom.left) (g := f.hom.left)).map
                ((pbcRationalInclusion C.l E X.obj.left).map L.rationalization.hom)) ≫
                (sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app
                  ((pbcRationalInclusion C.l E X.obj.left).obj K)
            have hγmap : (pbcConstructibleInclusion C.l E Y'.obj.left).map γ =
                sbcExchangeApp C.l E (exchangeTransposeSquare sq) K₀ := rfl
            have hmap : (pbcRationalInclusion C.l E Y'.obj.left).map
                ((pbcRationalization Y'.obj.left (pbcIntegralDatum C.l E)
                  (pbcUniformizer C.l E)).map γ) =
                (sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app
                  ((pbcRationalInclusion C.l E X.obj.left).obj
                    ((pbcRationalization X.obj.left (pbcIntegralDatum C.l E)
                      (pbcUniformizer C.l E)).obj L.integral)) := by
              have h := scalarBetween_map_localization (pbcUniformizer C.l E)
                (pbcConstructibleInclusion C.l E Y'.obj.left) γ
              have h' := congrArg (sbcCompleteRationalize C.l E Y'.obj.left).map hγmap
              exact h.trans h'
            exact naturality_representative
              (F := sbcRationalLeft C.l E (f := g.hom.left) (g := f.hom.left))
              (G := sbcRationalRight C.l E (e := g'.hom.left) (h := f'.hom.left))
              (sbcRationalExchange C.l E (exchangeTransposeSquare sq))
              ((pbcRationalInclusion C.l E X.obj.left).mapIso L.rationalization) _ hmap
        · have := hp
          have hcommon := qbar_properBaseChange.{u, u} C.l C.Qbar sq
          refine hcommon.imp ?_
          intro P hP
          exact ⟨hP.1, hP.2.1, hP.2.2.1⟩
      · intro _
        refine ⟨?_, ?_, ?_⟩
        · intro K L hL
          exact eCoefficientSmoothBaseChange C.l E (exchangeTransposeSquare sq)
            dY'.out dX.out hunit K L hL
        · unfold exchangeCommonStageSmooth at hcommonSmooth
          exact hcommonSmooth (exchangeTransposeSquare sq) hunit
        · intro M K L hL
          exact (eCoefficientSmoothBaseChange C.l (pbcFiniteField.{u} C.l C.Qbar M)
            (exchangeTransposeSquare sq) dY'.out dX.out hunit K L hL.1).2.2.2 hL
    · unfold sfPackageBaseChangeCompactSupport
      refine ⟨?_, ?_, hratSupport, hcommonSupport, ?_⟩
      · intro c
        constructor
        · intro K
          infer_instance
        · intro K W
          have hfinite := ProEtale.isIso_csAuxiliaryExchange C.l E n hn sq c K W
          with_reducible exact hfinite
      · intro c c' gbar properSquare openSquare r a ha K origins
        exact (completeCompactSupportProetale_isIso (pbcIntegralDatum C.l E)
          c c' gbar properSquare openSquare r a ha K origins).1
      · intro c c' gbar properSquare openSquare _ _ _ _ _ _ _ _
          dimY dimX' invY invX'
        have hc := qbarCompactSupportBaseChange.{u, u} C.l C.Qbar
          c c' gbar properSquare openSquare dimY dimX' invY invX'
        unfold exchangeCommonStageSupportLaws at hcommonSupport
        have hlaws := hcommonSupport c c' gbar properSquare openSquare
          dimY dimX' invY invX'
        with_reducible exact ⟨hc.1, fun B ↦
          ⟨(hc.2 B).1, (hc.2 B).2.1, (hc.2 B).2.2.1, hlaws⟩⟩

end WeilConjectures
