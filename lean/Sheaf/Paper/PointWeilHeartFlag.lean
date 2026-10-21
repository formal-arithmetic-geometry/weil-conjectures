/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.PointFibreEquivalence
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Full flags in the raw constructible Weil heart at a point

Source: main-20261015, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 7, dimension-zero Jordan filtration
(blueprint: lem-zl-point-weil-heart-flag).

## Main declarations

- `zlPointWeilFiber` and `zlPointWeilFrobenius`: the specified point realization.
- `ZlPointWeilFlagDiagram` and `ZlPointWeilHeartFlag`: the full pure-quotient flag.
- `ZlPointWeilFlagFiniteDiagram` and `ZlPointWeilHeartFlagModel`: its finite-stage model.
- `zl_point_weil_heart_flag`: existence of both diagrams and mixedness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The finite-field point, with its identity structure morphism.
Source: paragraph 7, dimension zero (blueprint: lem-zl-point-weil-heart-flag). -/
abbrev zlPointBase : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)

/-- Finite type of the identity point; no extra geometric hypothesis.
Source: paragraph 7 (blueprint: lem-zl-point-weil-heart-flag). -/
instance zlPointBaseLocallyOfFiniteType : LocallyOfFiniteType (zlPointBase D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))

/-- Quasi-compactness of the identity point.
Source: paragraph 7 (blueprint: lem-zl-point-weil-heart-flag). -/
instance zlPointBaseQuasiCompact : QuasiCompact (zlPointBase D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))

/-- Cache the inherited category on the point's common-stage Weil heart.
Source: paragraph 7 (blueprint: lem-zl-point-weil-heart-flag). -/
instance zlPointWeilHeartCategory :
    Category (sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :=
  inferInstance

/-- Cache the inherited category on the finite-stage Weil heart.
Source: paragraph 7 (blueprint: lem-zl-point-weil-heart-flag). -/
instance zlPointFiniteWeilHeartCategory (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    Category (sfWeilSheaf D l hl (zlPointBase D) E) := inferInstance

/-- Cache the inherited category on the underlying common-stage point heart.
Source: paragraph 7 (blueprint: lem-zl-point-weil-heart-flag). -/
instance zlPointRawHeartCategory :
    Category (sfCommonStageHeart l (D.geometricFiber (zlPointBase D)).left Ω) :=
  inferInstance

/-- Cache the inherited category on the underlying finite-stage point heart.
Source: paragraph 7 (blueprint: lem-zl-point-weil-heart-flag). -/
instance zlPointFiniteRawHeartCategory (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    Category (sfRationalHeart l E (D.geometricFiber (zlPointBase D)).left) := inferInstance

variable (y : {y : (zlPointBase D).left // y ∈ closedPoints (zlPointBase D).left})
  (ι : (zlPointBase D).left.residueField y.val →+* D.k)
  (hι : ι.comp ((zlPointBase D).hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

/-- The prescribed geometric H^0 fibre, on arrows as well as objects.
Source: paragraph 7 and the local-Frobenius stalk convention
(blueprint: lem-zl-point-weil-heart-flag). -/
def zlPointWeilFiber : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω ⥤ ModuleCat.{u} Ω :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl (zlPointBase D)
  ((sfCommonStageHeartProperty l (D.geometricFiber (zlPointBase D)).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl (zlPointBase D) Ω)).ι ⋙
    sfCommonStageWeilForget D l hl (zlPointBase D) Ω ⋙
    commonStageDerivedPullback l Ω (localClosedPoint D (zlPointBase D) y ι hι) ⋙
    pointQbarFibre D l hl Ω ⋙ DerivedCategory.coefficientQbarCohomology l Ω 0

/-- The actual local geometric Frobenius, including the specified point transport.
Source: paragraph 7 and the local-operator composite
(blueprint: lem-zl-point-weil-heart-flag). -/
def zlPointWeilFrobenius (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :
    (zlPointWeilFiber D l hl Ω y ι hι).obj F ⟶
      (zlPointWeilFiber D l hl Ω y ι hι).obj F :=
  localQbarClosedFrobeniusStalk l Ω D hl (zlPointBase D) F.obj y ι hι

/-- Forget a finite-stage Weil structure while retaining the actual rational heart.
Source: paragraph 7, exact heart lifting (blueprint: lem-zl-point-weil-heart-flag). -/
def zlPointFiniteHeart (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfWeilSheaf D l hl (zlPointBase D) E ⥤
      sfRationalHeart l E (D.geometricFiber (zlPointBase D)).left where
  obj M := ⟨M.obj.carrier, M.property⟩
  map f := ⟨f.hom.hom.f⟩

/-- Forget a common-stage Weil structure into its raw constructible heart.
Source: paragraph 7, exact heart lifting (blueprint: lem-zl-point-weil-heart-flag). -/
def zlPointCommonHeart : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω ⥤
    sfCommonStageHeart l (D.geometricFiber (zlPointBase D)).left Ω where
  obj M := ⟨M.obj.carrier, M.property⟩
  map f := ⟨f.hom.hom.f⟩

/-- The prescribed finite-stage stalk; its Frobenius is localClosedFrobeniusCohomology.
Source: paragraph 7, simultaneous coefficient descent
(blueprint: lem-zl-point-weil-heart-flag). -/
def zlPointFiniteFiber (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (M : sfWeilSheaf D l hl (zlPointBase D) E) :
    ModuleCat.{u} E :=
  (DerivedCategory.coefficientFdCohomology E 0).obj
    (localPointComplex l E D hl (zlPointBase D) M.obj
      (localClosedPoint D (zlPointBase D) y ι hι))

/-- The finite-stage local geometric Frobenius on the specified H^0 fibre.
Source: paragraph 7 and the local-Frobenius composite
(blueprint: lem-zl-point-weil-heart-flag). -/
def zlPointFiniteFrobenius (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (M : sfWeilSheaf D l hl (zlPointBase D) E) :
    zlPointFiniteFiber D l hl y ι hι E M ⟶ zlPointFiniteFiber D l hl y ι hι E M :=
  localClosedFrobeniusCohomology l E D hl (zlPointBase D) M.obj y ι hι 0

attribute [irreducible] zlPointWeilFiber zlPointWeilFrobenius zlPointFiniteFiber
  zlPointFiniteFrobenius zlPointCommonHeart zlPointFiniteHeart

/-- The actual Weil objects and arrows of a finite point flag, with its zero composites.
Source: paragraph 7, Jordan filtration (blueprint: lem-zl-point-weil-heart-flag). -/
structure ZlPointWeilFlagDiagram
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) where
  d : ℕ
  G : Fin (d + 1) → sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω
  step : ∀ j : Fin d, G j.castSucc ⟶ G j.succ
  into : ∀ j, G j ⟶ F
  Q : Fin d → sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω
  projection : ∀ j : Fin d, G j.succ ⟶ Q j
  zero : ∀ j : Fin d,
    (zlPointCommonHeart D l hl Ω).map (step j) ≫
      (zlPointCommonHeart D l hl Ω).map (projection j) = 0
  α : Fin d → Ωˣ

/-- Fullness, exactness, scalar Frobenius and purity of the actual point-flag diagram.
All fibres and operators use the recorded local composite, including point transport.
Source: paragraph 7, Jordan filtration (blueprint: lem-zl-point-weil-heart-flag). -/
def ZlPointWeilHeartFlag (iota : Ω ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω)
    (H : ZlPointWeilFlagDiagram D l hl Ω F) : Prop :=
  -- dimension
  (Module.finrank Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj F) = H.d) ∧
  -- finite
  (FiniteDimensional Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj F)) ∧
  -- into_mono
  (∀ j, Mono ((zlPointCommonHeart D l hl Ω).map (H.into j))) ∧
  -- into_step
  (∀ j : Fin H.d, H.step j ≫ H.into j.succ = H.into j.castSucc) ∧
  -- initial
  (IsZero (H.G 0)) ∧
  -- terminal
  (IsIso (H.into (Fin.last H.d))) ∧
  -- rank
  (∀ j, Module.finrank Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj (H.G j)) = j.val) ∧
  -- shortExact
  (∀ j : Fin H.d,
    (ShortComplex.mk ((zlPointCommonHeart D l hl Ω).map (H.step j))
      ((zlPointCommonHeart D l hl Ω).map (H.projection j)) (H.zero j)).ShortExact) ∧
  -- quotient_rank
  (∀ j, Module.finrank Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj (H.Q j)) = 1) ∧
  -- quotient_scalar
  (∀ (j : Fin H.d) (v : (zlPointWeilFiber D l hl Ω y ι hι).obj (H.Q j)),
    (zlPointWeilFrobenius D l hl Ω y ι hι (H.Q j)).hom v = (H.α j : Ω) • v) ∧
  -- pure
  (∀ j : Fin H.d,
    SfIsPunctuallyPureOfWeight D l hl Ω (zlPointBase D) iota.toRingHom (H.Q j)
      (2 * Real.log ‖iota (H.α j : Ω)‖ / Real.log (D.q : ℝ))) ∧
  -- flag_monotone
  (Monotone (fun j ↦
    LinearMap.range ((zlPointWeilFiber D l hl Ω y ι hι).map (H.into j)).hom)) ∧
  -- flag_invariant
  (∀ j,
    (LinearMap.range ((zlPointWeilFiber D l hl Ω y ι hι).map (H.into j)).hom).map
      (zlPointWeilFrobenius D l hl Ω y ι hι F).hom =
        LinearMap.range ((zlPointWeilFiber D l hl Ω y ι hι).map (H.into j)).hom) ∧
  -- frobenius_bijective
  (Function.Bijective (zlPointWeilFrobenius D l hl Ω y ι hι F).hom) ∧
  -- flag_bijective
  (∀ j,
    Function.Bijective (zlPointWeilFrobenius D l hl Ω y ι hι (H.G j)).hom) ∧
  -- quotient_bijective
  (∀ j,
    Function.Bijective (zlPointWeilFrobenius D l hl Ω y ι hι (H.Q j)).hom)

/-- One finite coefficient field and Weil-heart representatives for the entire diagram.
The comparison isomorphisms are in the actual fixed-pair category; their images under
point realization are the specified fibre identifications H^0(C_E) tensor_E Ω, including
the canonical Shrink coefficient change and the specified local point transports.
Source: paragraph 7, finite-stage descent (blueprint: lem-zl-point-weil-heart-flag). -/
structure ZlPointWeilFlagFiniteDiagram
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω)
    (H : ZlPointWeilFlagDiagram D l hl Ω F) where
  E : Padic.FiniteCoefficientFields l Ω
  M : Fin (H.d + 1) → sfWeilSheaf D l hl (zlPointBase D)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
  N : Fin H.d → sfWeilSheaf D l hl (zlPointBase D)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
  stepE : ∀ j : Fin H.d, M j.castSucc ⟶ M j.succ
  projectionE : ∀ j : Fin H.d, M j.succ ⟶ N j
  intoE : ∀ j, M j ⟶ M (Fin.last H.d)
  zeroE : ∀ j : Fin H.d,
    (zlPointFiniteHeart D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).map (stepE j) ≫
    (zlPointFiniteHeart D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).map (projectionE j) = 0
  e : ∀ j, (H.G j).obj ≅ sfWeilStageObject D l hl (zlPointBase D) Ω E (M j).obj
  eQ : ∀ j, (H.Q j).obj ≅ sfWeilStageObject D l hl (zlPointBase D) Ω E (N j).obj
  eF : F.obj ≅ sfWeilStageObject D l hl (zlPointBase D) Ω E (M (Fin.last H.d)).obj
  αE : Fin H.d → (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)ˣ

/-- All arrows, exact sequences, ranks and Frobenius scalars descend to the same field.
The three descent equations compare actual raw morphisms through the Weil isomorphisms.
Source: paragraph 7, finite-stage descent (blueprint: lem-zl-point-weil-heart-flag). -/
def ZlPointWeilHeartFlagModel
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω)
    (H : ZlPointWeilFlagDiagram D l hl Ω F)
    (T : ZlPointWeilFlagFiniteDiagram D l hl Ω F H) : Prop :=
  -- initialE
  (IsZero ((zlPointFiniteHeart D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E)).obj (T.M 0))) ∧
  -- terminalE
  (T.intoE (Fin.last H.d) = 𝟙 _) ∧
  -- into_stepE
  (∀ j : Fin H.d, T.stepE j ≫ T.intoE j.succ = T.intoE j.castSucc) ∧
  -- into_monoE
  (∀ j, Mono ((zlPointFiniteHeart D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E)).map (T.intoE j))) ∧
  -- shortExactE
  (∀ j : Fin H.d,
    (ShortComplex.mk ((zlPointFiniteHeart D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E)).map (T.stepE j))
      ((zlPointFiniteHeart D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E)).map (T.projectionE j))
      (T.zeroE j)).ShortExact) ∧
  -- step_descends
  (∀ j : Fin H.d,
    (H.step j).hom.hom.f ≫ (T.e j.succ).hom.hom.f =
      (T.e j.castSucc).hom.hom.f ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber (zlPointBase D)).left) T.E).map
          (T.stepE j).hom.hom.f) ∧
  -- projection_descends
  (∀ j : Fin H.d,
    (H.projection j).hom.hom.f ≫ (T.eQ j).hom.hom.f =
      (T.e j.succ).hom.hom.f ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber (zlPointBase D)).left) T.E).map
          (T.projectionE j).hom.hom.f) ∧
  -- into_descends
  (∀ j,
    (H.into j).hom.hom.f ≫ T.eF.hom.hom.f = (T.e j).hom.hom.f ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber (zlPointBase D)).left) T.E).map
        (T.intoE j).hom.hom.f) ∧
  -- rankE
  (∀ j, Module.finrank (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E)
    (zlPointFiniteFiber D l hl y ι hι
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) (T.M j)) = j.val) ∧
  -- quotient_rankE
  (∀ j,
    Module.finrank (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E)
      (zlPointFiniteFiber D l hl y ι hι
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) (T.N j)) = 1) ∧
  -- α_descends
  (∀ j,
    T.E.val.subtype (Shrink.algEquiv (Padic l) T.E.val (T.αE j)) = (H.α j : Ω)) ∧
  -- quotient_scalarE
  (∀ (j : Fin H.d) (v : zlPointFiniteFiber D l hl y ι hι
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) (T.N j)),
    (zlPointFiniteFrobenius D l hl y ι hι
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) (T.N j)).hom v = (T.αE j :
        AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) • v) ∧
  -- flag_bijectiveE
  (∀ j,
    Function.Bijective (zlPointFiniteFrobenius D l hl y ι hι
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) (T.M j)).hom) ∧
  -- quotient_bijectiveE
  (∀ j,
    Function.Bijective (zlPointFiniteFrobenius D l hl y ι hι
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω T.E) (T.N j)).hom)

/-- Every raw constructible Weil sheaf at a finite-field point admits a full Frobenius
flag, with one-dimensional pure quotients and a single finite coefficient-heart model.
The datum D is arbitrary, so this includes every finite extension of the base, with
its own cardinality. No reality, semisimplicity or diagonalizability is assumed.

Source: main-20261015, thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-point-weil-heart-flag).

Proof: (1) Descend the given heart object by constructible truncations. Represent its
Weil map, inverse, and identification with the original object at finite stages. The
Hom-colimit equality rule makes all finitely many equations hold at one larger stage.
(2) Restrict point_fibre_equivalence to hearts using the standard-cohomology comparison:
H^0 of a preimage of W[0] is a heart preimage. Full faithfulness transfers kernels,
cokernels and exact sequences, compatibly with coefficient extension.
(3) Apply Module.End.exists_complete_invariant_flag over Ω. Injectivity and equal finite
dimension make Frobenius bijective on each invariant subspace and quotient. Choose an
adapted basis; the quotient scalars are nonzero. This allows nontrivial Jordan blocks.
(4) Adjoin the finitely many entries of this basis change, its inverse, and Frobenius
and inverse matrices to the initial finite coefficient field. The adapted spaces,
quotients, maps and exact sequences are all defined over this one finite field E.
(5) Lift each restricted Frobenius by full faithfulness after composing with inverse
point transport. Lift its inverse too. On the terminal object this recovers the
original Weil structure by the defining local-Frobenius composite.
(6) Lift inclusions and quotient projections by the exact heart equivalence. Naturality
of point transport proves their Weil equivariance. Extend the entire finite diagram
to Ω and identify its endpoint with the given sheaf. The comparisons are isomorphisms
of Weil pairs and hence use the prescribed fibres and local operators.
(7) For each quotient set w=2 log|iota(alpha)|/log(q). The scalar is nonzero and q>1,
so q^(w/2)=|iota(alpha)|. The quotient is pure; the finite filtration proves mixedness,
with any common upper bound for its finitely many weights.
(8) For dimension zero take the singleton zero endpoint and no quotient terms. The
same proof works for every finite-field datum, including finite base extensions. -/
theorem zl_point_weil_heart_flag (iota : Ω ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :
    ∃ H : ZlPointWeilFlagDiagram D l hl Ω F,
      ZlPointWeilHeartFlag D l hl Ω y ι hι iota F H ∧
      ∃ T : ZlPointWeilFlagFiniteDiagram D l hl Ω F H,
        ZlPointWeilHeartFlagModel D l hl Ω y ι hι F H T ∧
        ∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Ω (zlPointBase D) iota.toRingHom F w := by
  sorry

end WeilConjectures
