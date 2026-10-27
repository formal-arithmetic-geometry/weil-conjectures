/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.Paper.ECoefficientSmoothBaseChange
public import Sheaf.Paper.QbarCoefficientSmoothBaseChange
public import Sheaf.Paper.QbarProperBaseChange
import Sheaf.AlgebraicGeometry.SfBaseChangeGeometryHypotheses
import Sheaf.Paper.SbcDatumExchangeComparison
import Sheaf.Paper.CompletedConstructiblePreservation
import Sheaf.Paper.CompleteProetale
import Sheaf.Paper.PbcUniformCompleteTriangulated

/-! # Ordinary exchange on admissible coefficient stages

Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (4)
(blueprint: lem-sf-bc-field-mate-domain).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.QbarCoefficientSmoothBaseChange
namespace WeilConjectures

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] pbcFiniteField
  pbcRationalInclusion sbcRationalLeft sbcRationalRight sbcRationalExchange
  pbcIntegralDatum pbcUniformizer pbcScalarExtension pbcScalarAssociator
  HasDerivedCategory.standard CategoryTheory.Limits.limit CategoryTheory.Limits.colimit.cocone
  sbcPull sbcPush sbcExchangeApp
  sbcCompletedPullbackFunctor sbcCoefficientIso
  AdicCoefficientDatum.completedPull AdicCoefficientDatum.completedExchange
  PbcQbarExchangePresentation.exchange
  PbcQbarExchangePresentation.atStage StageSystem.Morphism.functor
  StageSystem.Morphism.functorCompIso
  sbcTransportedExchange SbcConstructibleExchangeRepresentation
  QbarCoefficientSmoothBaseChange.Presentation.exchange
  QbarCoefficientSmoothBaseChange.Presentation.atStage
  pbcActualCompletedPull

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)

/-- The existing category structure at its prescribed Hom universe.
Source: finite-stage category convention, blueprint clause (4)
(blueprint: lem-sf-bc-field-mate-domain). -/
instance sfFieldMateStageCategory (l : ℕ) [Fact l.Prime] (Ω : Type u)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    Category.{u + 2} (pbcStageCategory.{u, u} l Ω T i) := inferInstance

/-- The existing additive structure at the prescribed finite-stage universe.
Source: finite-stage scalar localization, blueprint clause (4)
(blueprint: lem-sf-bc-field-mate-domain). -/
instance sfFieldMateStagePreadditive (l : ℕ) [Fact l.Prime] (Ω : Type u)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    Preadditive.{u + 2, u + 2} (pbcStageCategory.{u, u} l Ω T i) := inferInstance

/-- The existing ambient Karoubi-stage category at its prescribed universe.
Source: identity-idempotent inclusion, blueprint clause (4)
(blueprint: lem-sf-bc-field-mate-domain). -/
instance sfFieldMateAmbientCategory (l : ℕ) [Fact l.Prime] (Ω : Type u)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    Category.{u + 2} (pbcAmbientCompleteKaroubiStage.{u, u} l Ω T i) := inferInstance

/-- The clauses of ordinary rational and common-stage base change. The initial fields
are consequences of the finite-type geometry, supplied by the theorem rather than
assumed. All subsequent fields are assertions about the existing canonical maps.
Source: blueprint clause (4) (blueprint: lem-sf-bc-field-mate-domain). -/
structure SfFieldMateDomain : Prop where
  [noetherianX : IsNoetherian X]
  [noetherianY : IsNoetherian Y]
  [noetherianX' : IsNoetherian X']
  [noetherianY' : IsNoetherian Y']
  [dimX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dimY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [dimX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n)]
  [dimY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n)]
  [invX : Fact (∀ x : X, IsUnit (C.l : X.presheaf.stalk x))]
  [invY : Fact (∀ x : Y, IsUnit (C.l : Y.presheaf.stalk x))]
  [invX' : Fact (∀ x : X', IsUnit (C.l : X'.presheaf.stalk x))]
  [invY' : Fact (∀ x : Y', IsUnit (C.l : Y'.presheaf.stalk x))]
  invGlobal : IsUnit (C.l : Γ(Y, ⊤))
  properRational : IsProper f → ∀ K : PbcRationalConstructible C.l E X,
    ∃ (hS : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum C.l E)
        ((sbcPull C.l E g).obj ((sbcPush C.l E f).obj
        ((pbcConstructibleInclusion C.l E X).obj K.obj))).obj)
      (hT : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum C.l E)
        ((sbcPush C.l E f').obj ((sbcPull C.l E g').obj
          ((pbcConstructibleInclusion C.l E X).obj K.obj))).obj),
      IsIso ((pbcRationalization Y' (pbcIntegralDatum C.l E) (pbcUniformizer C.l E)).map
        (ObjectProperty.homMk
          (X := ⟨_, hS⟩) (Y := ⟨_, hT⟩)
          (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
            ((pbcConstructibleInclusion C.l E X).obj K.obj)).hom))
  properCommon : IsProper f → ∃ P : PbcQbarExchangePresentation C.l C.Qbar sq,
    (∀ K : pbcQbarCategory C.l C.Qbar X,
      IsIso ((PbcQbarExchangePresentation.exchange C.l C.Qbar sq P).app K)) ∧
    (∀ (M : Padic.FiniteCoefficientFields C.l C.Qbar)
      (J : pbcStageCategory.{u, u} C.l C.Qbar X M), IsIso ((P.Ex.τ M).app J)) ∧
    (∀ (K : pbcQbarCategory C.l C.Qbar X)
      (M : Padic.FiniteCoefficientFields C.l C.Qbar) (a : K.stage ≤ M),
      (PbcQbarExchangePresentation.exchange C.l C.Qbar sq P).app K =
        PbcQbarExchangePresentation.atStage C.l C.Qbar sq P K M a) ∧
    (∀ (K J : pbcQbarCategory C.l C.Qbar X) (a : K ≅ J),
      (P.Rf.base.functor ⋙ P.Lg.base.functor).map a.hom ≫
          (PbcQbarExchangePresentation.exchange C.l C.Qbar sq P).app J =
        (PbcQbarExchangePresentation.exchange C.l C.Qbar sq P).app K ≫
          (P.Lg'.base.functor ⋙ P.Rf'.base.functor).map a.hom)
  smoothRational : ∀ [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (K : PbcRationalConstructible C.l E X)
    (L : IntegralLattice C.l E X dimX.out (sbcPrimeUnitOnSource C.l f invGlobal) K),
    L.IsFiniteLevelEtaleAdmissible C.l E X dimX.out
      (sbcPrimeUnitOnSource C.l f invGlobal) →
    IsIso ((sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app
      ((pbcRationalInclusion C.l E X).obj K)) ∧
    (sbcTransportedExchange C.l E (exchangeTransposeSquare sq) dimX.out
        (sbcPrimeUnitOnSource C.l f invGlobal) L =
      (sbcRationalExchange C.l E (exchangeTransposeSquare sq)).app
        ((pbcRationalInclusion C.l E X).obj K)) ∧
    (∀ L' : IntegralLattice C.l E X dimX.out (sbcPrimeUnitOnSource C.l f invGlobal) K,
      L'.IsFiniteLevelEtaleAdmissible C.l E X dimX.out
        (sbcPrimeUnitOnSource C.l f invGlobal) →
      sbcTransportedExchange C.l E (exchangeTransposeSquare sq) dimX.out
          (sbcPrimeUnitOnSource C.l f invGlobal) L' =
        sbcTransportedExchange C.l E (exchangeTransposeSquare sq) dimX.out
          (sbcPrimeUnitOnSource C.l f invGlobal) L) ∧
    (L.IsSquareConstructiblyAdmissible C.l E X dimX.out
        (sbcPrimeUnitOnSource C.l f invGlobal) (exchangeTransposeSquare sq) →
      SbcConstructibleExchangeRepresentation C.l E (exchangeTransposeSquare sq) dimX.out
        (sbcPrimeUnitOnSource C.l f invGlobal) L)
  smoothCommon : ∀ [Smooth g] [QuasiCompact f] [QuasiSeparated f],
    ∃ P : Presentation
        (iX := ⟨sbcPrimeUnitOnSource C.l g invGlobal⟩)
        (iS := ⟨sbcPrimeUnitOnSource C.l (𝟙 Y) invGlobal⟩)
        (iT := ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩)
        (iY := ⟨sbcPrimeUnitOnSource C.l (g' ≫ f) invGlobal⟩) C.l C.Qbar (exchangeTransposeSquare
          sq),
      (∀ (K : @pbcQbarCategory C.l _ C.Qbar _ _ _ X _ dimX
          ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩),
        (∃ (E : Padic.FiniteCoefficientFields C.l C.Qbar)
          (J : pbcStageCategory C.l C.Qbar X E)
          (L : IntegralLattice C.l (pbcFiniteField.{u} C.l C.Qbar E) X dimX.out
            (sbcPrimeUnitOnSource C.l f invGlobal) J),
          L.IsFiniteLevelEtaleAdmissible C.l (pbcFiniteField.{u} C.l C.Qbar E) X dimX.out
            (sbcPrimeUnitOnSource C.l f invGlobal) ∧
          Nonempty ((⟨E, J⟩ : @pbcQbarCategory C.l _ C.Qbar _ _ _ X _ dimX
            ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩) ≅ K) ∧
          (∀ (M : Padic.FiniteCoefficientFields C.l C.Qbar) (a : E ≤ M),
            ∃ LM : IntegralLattice C.l (pbcFiniteField.{u} C.l C.Qbar M) X dimX.out
                (sbcPrimeUnitOnSource C.l f invGlobal)
                (((pbcScalarSystem C.l C.Qbar X dimX.out (sbcPrimeUnitOnSource C.l f invGlobal)).T
                  a).obj
                  J),
              LM.IsFiniteLevelEtaleAdmissible C.l (pbcFiniteField.{u} C.l C.Qbar M) X dimX.out
                (sbcPrimeUnitOnSource C.l f invGlobal))) →
        IsIso ((Presentation.exchange
          (iX := ⟨sbcPrimeUnitOnSource C.l g invGlobal⟩)
          (iS := ⟨sbcPrimeUnitOnSource C.l (𝟙 Y) invGlobal⟩)
          (iT := ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩)
          (iY := ⟨sbcPrimeUnitOnSource C.l (g' ≫ f) invGlobal⟩) C.l C.Qbar (exchangeTransposeSquare
            sq) P).app K)) ∧
      (∀ (Q : (pbcAmbientCompleteSystem C.l C.Qbar X
          (hInv := ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩)).PairCategory)
        (M : Padic.FiniteCoefficientFields C.l C.Qbar) (a : Q.stage ≤ M),
        (StageSystem.Morphism.descNatTrans (Presentation.alpha
          (iX := ⟨sbcPrimeUnitOnSource C.l g invGlobal⟩)
          (iS := ⟨sbcPrimeUnitOnSource C.l (𝟙 Y) invGlobal⟩)
          (iT := ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩)
          (iY := ⟨sbcPrimeUnitOnSource C.l (g' ≫ f) invGlobal⟩) P)).app Q =
          Presentation.atStage
            (iX := ⟨sbcPrimeUnitOnSource C.l g invGlobal⟩)
            (iS := ⟨sbcPrimeUnitOnSource C.l (𝟙 Y) invGlobal⟩)
            (iT := ⟨sbcPrimeUnitOnSource C.l f invGlobal⟩)
            (iY := ⟨sbcPrimeUnitOnSource C.l (g' ≫ f) invGlobal⟩) C.l C.Qbar
              (exchangeTransposeSquare sq) P Q M a) ∧
      (∀ (E : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K : PbcRationalConstructible C.l (pbcFiniteField.{u} C.l C.Qbar E) X)
        (L L' : IntegralLattice C.l (pbcFiniteField.{u} C.l C.Qbar E) X dimX.out
          (sbcPrimeUnitOnSource C.l f invGlobal) K),
        L.IsFiniteLevelEtaleAdmissible C.l (pbcFiniteField.{u} C.l C.Qbar E) X dimX.out
          (sbcPrimeUnitOnSource C.l f invGlobal) →
        L'.IsFiniteLevelEtaleAdmissible C.l (pbcFiniteField.{u} C.l C.Qbar E) X dimX.out
          (sbcPrimeUnitOnSource C.l f invGlobal) →
        sbcTransportedExchange C.l (pbcFiniteField.{u} C.l C.Qbar E) (exchangeTransposeSquare sq)
          dimX.out
            (sbcPrimeUnitOnSource C.l f invGlobal) L =
          sbcTransportedExchange C.l (pbcFiniteField.{u} C.l C.Qbar E) (exchangeTransposeSquare sq)
            dimX.out
            (sbcPrimeUnitOnSource C.l f invGlobal) L')
  smoothCommonConstructible : ∀ [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (M : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K : pbcStageCategory.{u, u} C.l C.Qbar X M)
    (L : IntegralLattice C.l (pbcFiniteField.{u} C.l C.Qbar M) X dimX.out
      (sbcPrimeUnitOnSource C.l f invGlobal) K),
    L.IsSquareConstructiblyAdmissible C.l (pbcFiniteField.{u} C.l C.Qbar M) X dimX.out
      (sbcPrimeUnitOnSource C.l f invGlobal) (exchangeTransposeSquare sq) →
    SbcConstructibleExchangeRepresentation C.l (pbcFiniteField.{u} C.l C.Qbar M)
      (exchangeTransposeSquare sq) dimX.out (sbcPrimeUnitOnSource C.l f invGlobal) L ∧
    ∀ (J J' : pbcStageCategory.{u, u} C.l C.Qbar Y' M) (β : J ≅ J'),
    ∃ gamma : ((pbcScalarSystem C.l C.Qbar Y' dimY'.out invY'.out).ι M).obj
          J ≅
        ((pbcScalarSystem C.l C.Qbar Y' dimY'.out invY'.out).ι M).obj
          J',
      gamma.hom = ((pbcScalarSystem C.l C.Qbar Y' dimY'.out invY'.out).ι M).map β.hom ∧
      ∀ (N : Padic.FiniteCoefficientFields C.l C.Qbar) (a : M ≤ N),
        gamma.hom = StageSystem.PairCategory.mkHom N a a
          (((pbcScalarSystem C.l C.Qbar Y' dimY'.out invY'.out).T a).map β.hom)


/-- Ordinary exchange on the proper domain and the admissible smooth domain, with
raw rationalization and common finite-field representatives.
Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (4)
(blueprint: lem-sf-bc-field-mate-domain).

Proof:
1. Apply lem-sf-bc-geometry-hypotheses to obtain Noetherian finite-dimensional
corners, invertibility of the coefficient prime, qcqs arrows and one fibre bound.
Properness of f implies properness of f'.
2. Use lem-sbc-completed-operations-linear-natural-exchange: its specified
unit/comparison/counit mate reduces to the finite ambient mates. The four-arrows
and completed-base-change-map definitions identify their derived-limit exchange
with the map in cor-weil-pbc-constructible-complete. Thus all coefficient theorems
below concern this specified map of def-exchange-projection.
3. For proper f, thm-weil-pbc-finite-extension rationalizes that integral exchange.
The full integral subcategory reflects isomorphisms. thm-weil-pbc-qbar descends
these maps and gives their representatives over every common finite overfield;
naturality gives independence of isomorphic pair representatives.
4. For smooth g, transpose the square to (f_s,g_s,h_s,e_s)=(g,f,f',g').
Apply sbc-thm-e-coefficient-smooth-base-change to each supplied admissible lattice.
Its transported arrow equals the canonical rational mate, hence is independent
of the lattice and its isomorphism. Square admissibility supplies one interval
for all four operation families and all positive levels and gives constructible
landing. Only integral lattices, never rational objects, are reduced.
5. Apply sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch to the stipulated
representatives and their overfields. Its normalized presentation includes raw
maps through the identity projectors of def-sbc-ambient-complete-coefficient-categories.
Its atStage equation, including the identity extension, and naturality give
field and representative independence; the finite-E equality gives lattice independence.
6. On the conditional square-constructible domain use the preceding finite-E
representation, then prop-weil-pbc-scalar-extension and prop-weil-pbc-descent-functors.
The finite-stage isomorphism and its inverse give inverse common-stage classes.
prop-weil-pbc-common-stage-calculus identifies these after every further overfield.
-/
theorem sf_fieldMateDomain
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (hn : 1 ≤ n) (_operations : SixFunctorOperationDatum D C E n hn)
    (X Y X' Y' : SixFunctorSpace D)
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated X'.obj.hom] [IsSeparated Y'.obj.hom]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated g'.hom.left] [LocallyOfFiniteType g'.hom.left] [QuasiCompact g'.hom.left]
    [IsSeparated f'.hom.left] [LocallyOfFiniteType f'.hom.left] [QuasiCompact f'.hom.left]
    (sq : ChosenCartesianSquare g'.hom.left f'.hom.left f.hom.left g.hom.left) :
    SfFieldMateDomain D C E sq := by
  let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) := inferInstanceAs
    (IsSeparated X.obj.hom)
  let : IsSeparated (Y.obj.left ↘ Spec (.of D.k)) := inferInstanceAs
    (IsSeparated Y.obj.hom)
  let : IsSeparated (X'.obj.left ↘ Spec (.of D.k)) := inferInstanceAs
    (IsSeparated X'.obj.hom)
  let : IsSeparated (Y'.obj.left ↘ Spec (.of D.k)) := inferInstanceAs
    (IsSeparated Y'.obj.hom)
  have geom := sf_baseChange_geometry_hypotheses D C.l (Fact.out : C.l.Prime) C.different
    g'.hom.left f'.hom.left f.hom.left g.hom.left sq
  have hX := geom.1 X.obj.left (Or.inl rfl)
  have hY := geom.1 Y.obj.left (Or.inr (Or.inl rfl))
  have hX' := geom.1 X'.obj.left (Or.inr (Or.inr (Or.inl rfl)))
  have hY' := geom.1 Y'.obj.left (Or.inr (Or.inr (Or.inr rfl)))
  let := hX.1
  let := hY.1
  let := hX'.1
  let := hY'.1
  let dX : Fact (∃ n : ℕ, topologicalKrullDim X.obj.left ≤ n) := ⟨hX.2.2.2.1⟩
  let dY : Fact (∃ n : ℕ, topologicalKrullDim Y.obj.left ≤ n) := ⟨hY.2.2.2.1⟩
  let dX' : Fact (∃ n : ℕ, topologicalKrullDim X'.obj.left ≤ n) := ⟨hX'.2.2.2.1⟩
  let dY' : Fact (∃ n : ℕ, topologicalKrullDim Y'.obj.left ≤ n) := ⟨hY'.2.2.2.1⟩
  let iX : Fact (∀ x : X.obj.left, IsUnit (C.l : X.obj.left.presheaf.stalk x)) :=
    ⟨hX.2.2.2.2⟩
  let iY : Fact (∀ x : Y.obj.left, IsUnit (C.l : Y.obj.left.presheaf.stalk x)) :=
    ⟨hY.2.2.2.2⟩
  let iX' : Fact (∀ x : X'.obj.left, IsUnit (C.l : X'.obj.left.presheaf.stalk x)) :=
    ⟨hX'.2.2.2.2⟩
  let iY' : Fact (∀ x : Y'.obj.left, IsUnit (C.l : Y'.obj.left.presheaf.stalk x)) :=
    ⟨hY'.2.2.2.2⟩
  have hu : IsUnit (C.l : Γ(Y.obj.left, ⊤)) := by
    apply Y.obj.left.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using iY.out y
  refine { invGlobal := hu
           properRational := ?_
           properCommon := ?_
           smoothRational := ?_
           smoothCommon := ?_
           smoothCommonConstructible := ?_ }
  · intro hf K
    let := hf
    let : IsProper f'.hom.left := geom.2.2.2.2.2.2.1 hf
    have unit (T : Scheme.{u}) (h : ∀ t : T, IsUnit (C.l : T.presheaf.stalk t)) :
        IsUnit (C.l : Γ(T, ⊤)) := by
      apply T.toRingedSpace.isUnit_of_isUnit_germ
      intro t ht
      simpa only [map_natCast] using h t
    have hann : (C.l : PbcIntegralRing C.l E ⧸ (pbcIntegralDatum C.l E).ideal) = 0 := by
      unfold pbcIntegralDatum
      have hd := (Padic.extension_integers_dvr C.l E
        (Padic.coefficientExtensionAbsoluteValue C.l E)
        (spectralNorm_extends (K := Padic C.l) (L := E))).choose_spec.choose_spec
      have hgen : Ideal.span {Padic.coefficientExtensionUniformizer C.l E} =
          Padic.coefficientExtensionMaximalIdeal C.l E :=
        hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
      have hl : (C.l : Padic.coefficientExtensionIntegers C.l E) ∈
          Ideal.span {Padic.coefficientExtensionUniformizer C.l E} := by
        rw [hgen]
        apply (hd.2.1 _).mpr
        change spectralNorm (Padic C.l) E (C.l : E) < 1
        rw [← map_natCast (algebraMap (Padic C.l) E), spectralNorm_extends]
        exact Padic.norm_p_lt_one
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      change (C.l : PbcIntegralRing C.l E) ∈ Ideal.span {pbcUniformizer C.l E}
      rw [Ideal.mem_span_singleton] at hl ⊢
      have h := map_dvd ULift.ringEquiv.symm hl
      change ULift.up (Padic.coefficientExtensionUniformizer C.l E) ∣
        (C.l : PbcIntegralRing C.l E) at h
      unfold pbcUniformizer
      exact h
    obtain ⟨e, he⟩ := geom.2.2.2.2.2.1
    have hmem := (pbcIntegralDatum C.l E).constructible_preservation sq
      dX.out dY.out dX'.out dY'.out C.l (Fact.out : C.l.Prime).pos hann
      (unit _ iX.out) hu (unit _ iX'.out) (unit _ iY'.out) e
      (fun Ω _ _ y ↦ (he Ω y).1) K.obj.obj K.obj.property
    obtain ⟨source, target, hex⟩ := sbcDatumExchangeComparison C.l E sq
      ((pbcConstructibleInclusion C.l E X.obj.left).obj K.obj)
    let := (pbcIntegralUniformComplete_isTriangulated C.l E Y'.obj.left
      dY'.out iY'.out).1
    have hs := ObjectProperty.prop_of_iso _ source.symm hmem.2.1
    have ht := ObjectProperty.prop_of_iso _ target.symm hmem.2.2.2
    refine ⟨hs, ht, ?_⟩
    have hi := completeProetale_isIso (pbcIntegralDatum C.l E) sq K.obj.obj
      K.obj.property.1 K.obj.property.2.2
    have : IsIso ((pbcIntegralDatum C.l E).completedExchange sq
        ((pbcConstructibleInclusion C.l E X.obj.left).obj K.obj).obj) := hi
    have : IsIso source.hom := source.isIso_hom
    have : IsIso target.hom := target.isIso_hom
    have hb : IsIso ((sbcExchangeApp C.l E (exchangeTransposeSquare sq)
        ((pbcConstructibleInclusion C.l E X.obj.left).obj K.obj)).hom) := by
      have : IsIso ((sbcExchangeApp C.l E (exchangeTransposeSquare sq)
          ((pbcConstructibleInclusion C.l E X.obj.left).obj K.obj)).hom ≫ target.hom) := by
        rw [hex]
        exact IsIso.comp_isIso' source.isIso_hom hi
      exact IsIso.of_isIso_comp_right _ target.hom
    have : IsIso (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
        (sbcExchangeApp C.l E (exchangeTransposeSquare sq)
          ((pbcConstructibleInclusion C.l E X.obj.left).obj K.obj)).hom) :=
      (ObjectProperty.isIso_hom_iff _).mp hb
    infer_instance
  · intro hf
    let := hf
    exact qbar_properBaseChange C.l C.Qbar sq
  · intro _ _ _ K L hL
    exact eCoefficientSmoothBaseChange C.l E (exchangeTransposeSquare sq)
      dY'.out dX.out hu K L hL
  · intro _ _ _
    exact qbarCoefficientSmoothBaseChange C.l C.Qbar (exchangeTransposeSquare sq) hu
  · intro _ _ _ M K L hL
    refine ⟨(eCoefficientSmoothBaseChange C.l (pbcFiniteField C.l C.Qbar M)
      (exchangeTransposeSquare sq) dY'.out dX.out hu K L hL.1).2.2.2 hL, ?_⟩
    intro J J' β
    refine ⟨((pbcScalarSystem C.l C.Qbar Y'.obj.left dY'.out iY'.out).ι M).mapIso β,
      rfl, ?_⟩
    intro N a
    exact StageSystem.ι_map_eq a β.hom

end WeilConjectures
