# Point Weil flag data module

## Reason

The new algebraic flag and scalar-spectrum lemmas must use the existing flag data
without importing the existence theorem they help prove. Move the existing data
prefix verbatim to `Sheaf.Paper.PointWeilHeartFlagData` and publicly reexport it from
the original module. This resolves the dependency cycle required for genuine split
statements; it is not a compile-time split. Every definition body and signature,
instance, universe and irreducibility attribute is preserved. Only documentation
ownership tags change to the new owning data node. No source-library module changes.

## Old

`Sheaf.Paper.PointWeilHeartFlag` declares `zlPointBase`, its cached instances,
`zlPointWeilFiber`, `zlPointWeilFrobenius`, `zlPointFiniteHeart`,
`zlPointCommonHeart`, `zlPointFiniteFiber`, `zlPointFiniteFrobenius`,
`ZlPointWeilFlagDiagram`, `ZlPointWeilHeartFlag`, `ZlPointWeilFlagFiniteDiagram`,
and `ZlPointWeilHeartFlagModel` before the existence theorem. Their verbatim signatures and bodies are:

```lean
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
```

## New

The declarations above, with exactly the same signatures and bodies, are in
`Sheaf.Paper.PointWeilHeartFlagData`; `Sheaf.Paper.PointWeilHeartFlag` starts with
`public import Sheaf.Paper.PointWeilHeartFlagData`. All declarations keep their
original namespace and names, signatures, bodies, universes and visibility.

The new declarations, verbatim:

```lean
/-- The finite-field point, with its identity structure morphism.
Source: paragraph 7, dimension zero (blueprint: def-zl-point-weil-flag-data). -/
abbrev zlPointBase : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)

/-- Finite type of the identity point; no extra geometric hypothesis.
Source: paragraph 7 (blueprint: def-zl-point-weil-flag-data). -/
instance zlPointBaseLocallyOfFiniteType : LocallyOfFiniteType (zlPointBase D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))

/-- Quasi-compactness of the identity point.
Source: paragraph 7 (blueprint: def-zl-point-weil-flag-data). -/
instance zlPointBaseQuasiCompact : QuasiCompact (zlPointBase D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))

/-- Cache the inherited category on the point's common-stage Weil heart.
Source: paragraph 7 (blueprint: def-zl-point-weil-flag-data). -/
instance zlPointWeilHeartCategory :
    Category (sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :=
  inferInstance

/-- Cache the inherited category on the finite-stage Weil heart.
Source: paragraph 7 (blueprint: def-zl-point-weil-flag-data). -/
instance zlPointFiniteWeilHeartCategory (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    Category (sfWeilSheaf D l hl (zlPointBase D) E) := inferInstance

/-- Cache the inherited category on the underlying common-stage point heart.
Source: paragraph 7 (blueprint: def-zl-point-weil-flag-data). -/
instance zlPointRawHeartCategory :
    Category (sfCommonStageHeart l (D.geometricFiber (zlPointBase D)).left Ω) :=
  inferInstance

/-- Cache the inherited category on the underlying finite-stage point heart.
Source: paragraph 7 (blueprint: def-zl-point-weil-flag-data). -/
instance zlPointFiniteRawHeartCategory (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    Category (sfRationalHeart l E (D.geometricFiber (zlPointBase D)).left) := inferInstance

variable (y : {y : (zlPointBase D).left // y ∈ closedPoints (zlPointBase D).left})
  (ι : (zlPointBase D).left.residueField y.val →+* D.k)
  (hι : ι.comp ((zlPointBase D).hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

/-- The prescribed geometric H^0 fibre, on arrows as well as objects.
Source: paragraph 7 and the local-Frobenius stalk convention
(blueprint: def-zl-point-weil-flag-data). -/
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
(blueprint: def-zl-point-weil-flag-data). -/
def zlPointWeilFrobenius (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :
    (zlPointWeilFiber D l hl Ω y ι hι).obj F ⟶
      (zlPointWeilFiber D l hl Ω y ι hι).obj F :=
  localQbarClosedFrobeniusStalk l Ω D hl (zlPointBase D) F.obj y ι hι

/-- Forget a finite-stage Weil structure while retaining the actual rational heart.
Source: paragraph 7, exact heart lifting (blueprint: def-zl-point-weil-flag-data). -/
def zlPointFiniteHeart (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfWeilSheaf D l hl (zlPointBase D) E ⥤
      sfRationalHeart l E (D.geometricFiber (zlPointBase D)).left where
  obj M := ⟨M.obj.carrier, M.property⟩
  map f := ⟨f.hom.hom.f⟩

/-- Forget a common-stage Weil structure into its raw constructible heart.
Source: paragraph 7, exact heart lifting (blueprint: def-zl-point-weil-flag-data). -/
def zlPointCommonHeart : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω ⥤
    sfCommonStageHeart l (D.geometricFiber (zlPointBase D)).left Ω where
  obj M := ⟨M.obj.carrier, M.property⟩
  map f := ⟨f.hom.hom.f⟩

/-- The prescribed finite-stage stalk; its Frobenius is localClosedFrobeniusCohomology.
Source: paragraph 7, simultaneous coefficient descent
(blueprint: def-zl-point-weil-flag-data). -/
def zlPointFiniteFiber (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (M : sfWeilSheaf D l hl (zlPointBase D) E) :
    ModuleCat.{u} E :=
  (DerivedCategory.coefficientFdCohomology E 0).obj
    (localPointComplex l E D hl (zlPointBase D) M.obj
      (localClosedPoint D (zlPointBase D) y ι hι))

/-- The finite-stage local geometric Frobenius on the specified H^0 fibre.
Source: paragraph 7 and the local-Frobenius composite
(blueprint: def-zl-point-weil-flag-data). -/
def zlPointFiniteFrobenius (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (M : sfWeilSheaf D l hl (zlPointBase D) E) :
    zlPointFiniteFiber D l hl y ι hι E M ⟶ zlPointFiniteFiber D l hl y ι hι E M :=
  localClosedFrobeniusCohomology l E D hl (zlPointBase D) M.obj y ι hι 0

attribute [irreducible] zlPointWeilFiber zlPointWeilFrobenius zlPointFiniteFiber
  zlPointFiniteFrobenius zlPointCommonHeart zlPointFiniteHeart

/-- The actual Weil objects and arrows of a finite point flag, with its zero composites.
Source: paragraph 7, Jordan filtration (blueprint: def-zl-point-weil-flag-data). -/
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
Source: paragraph 7, Jordan filtration (blueprint: def-zl-point-weil-flag-data). -/
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
Source: paragraph 7, finite-stage descent (blueprint: def-zl-point-weil-flag-data). -/
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
Source: paragraph 7, finite-stage descent (blueprint: def-zl-point-weil-flag-data). -/
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
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointWeilHeartFlag | J4 | Publicly reexports all original data; unchanged theorem signature. |
| Sheaf.Paper.PointWeilAlgebraicFlag | new in this delivery | Uses the flag data and proves the next construction subproblem. |
| Sheaf.Paper.PointScalarPunctualSpectrum | new in this delivery | Uses the specified local fibre and operator. |

`python3 tools/downstream.py Sheaf.Paper.PointWeilHeartFlag` reports zero current
Lean importers. Its DAG parents still use the same theorem and node. No target
statement or definition body changes, so no target meaning changes. The independent
review should compare the old declaration prefix with the new data module and
verify its public reexport; no consumer adaptation is necessary.

## Status

landed 20261025T123139-L-1837581 2026-10-25 (merge of deliver/J4/Sheaf.Paper.PointWeilHeartFlag)
