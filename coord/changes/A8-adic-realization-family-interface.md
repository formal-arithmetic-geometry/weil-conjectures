# WeilConjectures.AdicQbarRealization.Family

## Reason

The existing isomorphism-normalization theorem imports its Family definitions from
AdicQbarConstructibleRealization, whose proof must invoke that theorem. Move the five
existing definition declarations to their definition-node-owned module
Sheaf.Paper.AdicRealizationFamilyData. The item publicly reexports that module and
privately imports the normalization theorem. The normalization module publicly imports
the new owner instead of the item. This removes the cycle already identified by the
stage-2 reader, without changing any field, binder, universe, equation, or construction.

## Old

In lean/Sheaf/Paper/AdicQbarConstructibleRealization.lean:

```lean
structure GeometricSpace (D : FiniteFieldDatum.{u}) where
  base : Over (Spec (CommRingCat.of D.k))
  [separated : IsSeparated base.hom]
  [finiteType : LocallyOfFiniteType base.hom]
  [quasiCompact : QuasiCompact base.hom]

/-- Realization at one geometric space. Full faithfulness and the displayed essential
image express an equivalence with the full bounded constructible subcategory; exactness
is for the published shifts and triangles. Invertibility of l is supplied, not assumed.
Source: BS 6.8.8, 6.8.14--6.8.15
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
structure SpaceData (D : FiniteFieldDatum.{u}) (T : GeometricSpace D) where
  [units : ∀ x : T.base.left, Invertible (l : T.base.left.residueField x)]
  realization : LocallyFiniteAdicRealization.Realization l T.base.left
  presentation : (sectionFunctor l T.base.left realization).IsEquivalence
  [shift : (ordinary l T.base.left realization).CommShift ℤ]
  exact : (ordinary l T.base.left realization).IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective
    ((ordinary l T.base.left realization).map : (K ⟶ L) → (_ ⟶ _))
  image : ∀ K, boundedConstructible l T.base.left realization K ↔
    ∃ A, Nonempty ((ordinary l T.base.left realization).obj A ≅ K)
  tensor : At l T.base.left realization
  finite : ∀ E, FiniteNormalization l T.base.left realization tensor E
  hom : HomLaws l T.base.left realization tensor

/-- The realized inverse-image comparison on every integral representative is the
canonical scalar base-change composite, including all raw-localization transports.
Source: BS 6.8.14--6.8.15
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
def integralRealizationAgreement {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (integral : IntegralReindex l X g B E)
    (comparison : commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ derivedPull l X g B) : Prop :=
  ∀ K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y,
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E
    let I' := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let Q₀ := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let e : (commonStageDerivedPullback l (PadicAlgCl l) g).obj (I.obj (Q₀.obj K)) ≅
        I'.obj ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj
          (Q₀.obj K)) :=
      eqToIso ((commonStageDerivedPullback_existsUnique l (PadicAlgCl l)
        g).exists.choose_spec.1 (I.obj (Q₀.obj K)))
    let f : (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj (Q₀.obj K) ≅
      (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
        ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K) :=
      eqToIso ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          g).exists.choose_spec.2.1 (Q₀.obj K))
    HEq (comparison.hom.app (I.obj (Q₀.obj K)))
      ((ordinary l X R).map e.hom ≫
        (ordinary l X R).map (I'.map f.hom) ≫
        (R.integral E).hom.app
          ((constructibleIntegralPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K) ≫
        (pbcDerivedExtend (coefficientMap l X R E)).map
          (podCompletedToTowerIso l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K).inv ≫
        integral.derived.inv.app K.obj ≫
        (derivedPull l X g B).map
          ((S.integral E).inv.app K))

/-- A simultaneous normalized realization. Isomorphisms are isomorphisms of schemes,
so this includes semilinear geometric Frobenius. The ordinary identity and composition
maps are fixed on sections before deriving; compatibility uses those very maps.
Source: BS 6.8.14--6.8.15; HRS 5.2, 7.7 and 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
structure FamilyCore (D : FiniteFieldDatum.{u}) where
  data : ∀ T : GeometricSpace D, SpaceData l D T
  ring : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    RingReindex l T.base.left g.hom (data T).realization (data U).realization
  integral : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left) (E),
    IntegralReindex l T.base.left g.hom (ring T U g) E
  moduleId : ∀ T : GeometricSpace D,
    modulePull l T.base.left (𝟙 _) (ring T T (Iso.refl _)) ≅ 𝟭 _
  moduleComp : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left),
    modulePull l T.base.left (g ≪≫ h).hom (ring T V (g ≪≫ h)) ≅
      modulePull l U.base.left h.hom (ring U V h) ⋙
        modulePull l T.base.left g.hom (ring T U g)
  comparison : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    commonStageDerivedPullback l (PadicAlgCl l) g.hom ⋙
        ordinary l T.base.left (data T).realization ≅
      ordinary l U.base.left (data U).realization ⋙
        derivedPull l T.base.left g.hom (ring T U g)
  sourceId : ∀ T : GeometricSpace D,
    letI := (data T).units
    commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left) ≅ 𝟭 _
  pullTensor : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    ReindexTensor l T.base.left g.hom (data T).tensor (data U).tensor (ring T U g)
  unit_spec : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    canonicalCommonStagePullbackTensor_unit l (PadicAlgCl l) g.hom

/-- Identity, composition and tensor/Hom laws for the actual comparison data.
Source: BS 6.8.14--6.8.15; HRS 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
structure Family (D : FiniteFieldDatum.{u}) extends FamilyCore l D where
  moduleId_sections : ∀ (T : GeometricSpace D) (M : modules l T.base.left (data T).realization)
      (U : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (𝟙 _) (ring T T (Iso.refl _))).obj M).val.obj U),
    HEq (((moduleId T).hom.app M).val.app U x) x
  moduleComp_sections : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : modules l V.base.left (data V).realization) (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (ring T V (g ≪≫ h))).obj M).val.obj W),
    HEq (((moduleComp T U V g h).hom.app M).val.app W x) x
  integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
    letI := (data T).units
    letI := (data U).units
    integralRealizationAgreement l g.hom (data T).realization (data U).realization
      (ring T U g) E (integral T U g E) (comparison T U g)
  /-- The source identity is the unit for the fixed common-stage composition.
  HEq retains the transport along (id ≫ id) = id in the source object. -/
  sourceId_unit : ∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (data T).units
    HEq
      ((pullbackTensorCommonComposition l (PadicAlgCl l)
          (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
        (sourceId T).hom.app
          ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
      (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
  identity : ∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (data T).units
    (comparison T T (Iso.refl _)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (moduleId T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((ordinary l T.base.left (data T).realization).obj M) =
    (ordinary l T.base.left (data T).realization).map ((sourceId T).hom.app M)
  composition : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) V.base.left),
    letI := (data T).units
    letI := (data U).units
    letI := (data V).units
    (comparison T V (g ≪≫ h)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((ordinary l V.base.left (data V).realization).obj M) =
    (ordinary l T.base.left (data T).realization).map
        (pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom M).hom ≫
      (comparison T U g).hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M) ≫
      (derivedPull l T.base.left g.hom (ring T U g)).map ((comparison U V h).hom.app M)
  tensor_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
    letI := (data T).units
    letI := (data U).units
    (derivedPull l T.base.left g.hom (ring T U g)).map ((data U).tensor.tensor.hom.app (M, N)) ≫
      (comparison T U g).inv.app ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
        (M, N)) ≫
      (ordinary l T.base.left (data T).realization).map
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom =
    (pullTensor T U g).tensor.hom.app
        ((ordinary l U.base.left (data U).realization).obj M,
         (ordinary l U.base.left (data U).realization).obj N) ≫
      (data T).tensor.closed.tensor.map (Prod.mkHom
        ((comparison T U g).inv.app M) ((comparison T U g).inv.app N)) ≫
      (data T).tensor.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N)
  unit_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    (derivedPull l T.base.left g.hom (ring T U g)).map (data U).tensor.unit.hom ≫
      (comparison T U g).inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left) ≫
      (ordinary l T.base.left (data T).realization).map
        (unit_spec T U g).exists.choose.hom =
    (pullUnit l T.base.left g.hom (pullTensor T U g)).hom ≫ (data T).tensor.unit.hom
  hom_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) U.base.left).FullSubcategory),
    letI := (data T).units
    letI := (data U).units
    (comparison T U g).hom.app
        ((commonStageDerivedInternalHom l (PadicAlgCl l) U.base.left).obj P) ≫
      (derivedPull l T.base.left g.hom (ring T U g)).map
        (homComparison l U.base.left (data U).realization (data U).tensor P) ≫
      pullHom l T.base.left g.hom (pullTensor T U g)
        ((ordinary l U.base.left (data U).realization).obj P.obj.1.unop)
        ((ordinary l U.base.left (data U).realization).obj P.obj.2) ≫
      (ambientHom l T.base.left (data T).realization).map
        (Prod.mkHom ((comparison T U g).hom.app P.obj.1.unop).op
          ((comparison T U g).inv.app P.obj.2)) =
    (ordinary l T.base.left (data T).realization).map
        (podCommonHomComparison l (PadicAlgCl l) g.hom P) ≫
      homComparison l T.base.left (data T).realization (data T).tensor
        ((podPairPullback (commonStageDerivedPullback l (PadicAlgCl l) g.hom)
      (commonStageHomPairs l (PadicAlgCl l) U.base.left)
      (commonStageHomPairs l (PadicAlgCl l) T.base.left)
      (podCommonPairs_pullback l (PadicAlgCl l) g.hom)).obj P)
```

The normalization module publicly imported
Sheaf.Paper.AdicQbarConstructibleRealization.

## New

The exact declarations above, with their existing docstrings, are now in
lean/Sheaf/Paper/AdicRealizationFamilyData.lean, unchanged:

```lean
structure GeometricSpace (D : FiniteFieldDatum.{u}) where
  base : Over (Spec (CommRingCat.of D.k))
  [separated : IsSeparated base.hom]
  [finiteType : LocallyOfFiniteType base.hom]
  [quasiCompact : QuasiCompact base.hom]

/-- Realization at one geometric space. Full faithfulness and the displayed essential
image express an equivalence with the full bounded constructible subcategory; exactness
is for the published shifts and triangles. Invertibility of l is supplied, not assumed.
Source: BS 6.8.8, 6.8.14--6.8.15
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
structure SpaceData (D : FiniteFieldDatum.{u}) (T : GeometricSpace D) where
  [units : ∀ x : T.base.left, Invertible (l : T.base.left.residueField x)]
  realization : LocallyFiniteAdicRealization.Realization l T.base.left
  presentation : (sectionFunctor l T.base.left realization).IsEquivalence
  [shift : (ordinary l T.base.left realization).CommShift ℤ]
  exact : (ordinary l T.base.left realization).IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective
    ((ordinary l T.base.left realization).map : (K ⟶ L) → (_ ⟶ _))
  image : ∀ K, boundedConstructible l T.base.left realization K ↔
    ∃ A, Nonempty ((ordinary l T.base.left realization).obj A ≅ K)
  tensor : At l T.base.left realization
  finite : ∀ E, FiniteNormalization l T.base.left realization tensor E
  hom : HomLaws l T.base.left realization tensor

/-- The realized inverse-image comparison on every integral representative is the
canonical scalar base-change composite, including all raw-localization transports.
Source: BS 6.8.14--6.8.15
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
def integralRealizationAgreement {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (integral : IntegralReindex l X g B E)
    (comparison : commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ derivedPull l X g B) : Prop :=
  ∀ K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y,
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E
    let I' := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let Q₀ := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let e : (commonStageDerivedPullback l (PadicAlgCl l) g).obj (I.obj (Q₀.obj K)) ≅
        I'.obj ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj
          (Q₀.obj K)) :=
      eqToIso ((commonStageDerivedPullback_existsUnique l (PadicAlgCl l)
        g).exists.choose_spec.1 (I.obj (Q₀.obj K)))
    let f : (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj (Q₀.obj K) ≅
      (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
        ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K) :=
      eqToIso ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          g).exists.choose_spec.2.1 (Q₀.obj K))
    HEq (comparison.hom.app (I.obj (Q₀.obj K)))
      ((ordinary l X R).map e.hom ≫
        (ordinary l X R).map (I'.map f.hom) ≫
        (R.integral E).hom.app
          ((constructibleIntegralPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K) ≫
        (pbcDerivedExtend (coefficientMap l X R E)).map
          (podCompletedToTowerIso l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K).inv ≫
        integral.derived.inv.app K.obj ≫
        (derivedPull l X g B).map
          ((S.integral E).inv.app K))

/-- A simultaneous normalized realization. Isomorphisms are isomorphisms of schemes,
so this includes semilinear geometric Frobenius. The ordinary identity and composition
maps are fixed on sections before deriving; compatibility uses those very maps.
Source: BS 6.8.14--6.8.15; HRS 5.2, 7.7 and 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
structure FamilyCore (D : FiniteFieldDatum.{u}) where
  data : ∀ T : GeometricSpace D, SpaceData l D T
  ring : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    RingReindex l T.base.left g.hom (data T).realization (data U).realization
  integral : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left) (E),
    IntegralReindex l T.base.left g.hom (ring T U g) E
  moduleId : ∀ T : GeometricSpace D,
    modulePull l T.base.left (𝟙 _) (ring T T (Iso.refl _)) ≅ 𝟭 _
  moduleComp : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left),
    modulePull l T.base.left (g ≪≫ h).hom (ring T V (g ≪≫ h)) ≅
      modulePull l U.base.left h.hom (ring U V h) ⋙
        modulePull l T.base.left g.hom (ring T U g)
  comparison : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    commonStageDerivedPullback l (PadicAlgCl l) g.hom ⋙
        ordinary l T.base.left (data T).realization ≅
      ordinary l U.base.left (data U).realization ⋙
        derivedPull l T.base.left g.hom (ring T U g)
  sourceId : ∀ T : GeometricSpace D,
    letI := (data T).units
    commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left) ≅ 𝟭 _
  pullTensor : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    ReindexTensor l T.base.left g.hom (data T).tensor (data U).tensor (ring T U g)
  unit_spec : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    canonicalCommonStagePullbackTensor_unit l (PadicAlgCl l) g.hom

/-- Identity, composition and tensor/Hom laws for the actual comparison data.
Source: BS 6.8.14--6.8.15; HRS 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
structure Family (D : FiniteFieldDatum.{u}) extends FamilyCore l D where
  moduleId_sections : ∀ (T : GeometricSpace D) (M : modules l T.base.left (data T).realization)
      (U : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (𝟙 _) (ring T T (Iso.refl _))).obj M).val.obj U),
    HEq (((moduleId T).hom.app M).val.app U x) x
  moduleComp_sections : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : modules l V.base.left (data V).realization) (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (ring T V (g ≪≫ h))).obj M).val.obj W),
    HEq (((moduleComp T U V g h).hom.app M).val.app W x) x
  integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
    letI := (data T).units
    letI := (data U).units
    integralRealizationAgreement l g.hom (data T).realization (data U).realization
      (ring T U g) E (integral T U g E) (comparison T U g)
  /-- The source identity is the unit for the fixed common-stage composition.
  HEq retains the transport along (id ≫ id) = id in the source object. -/
  sourceId_unit : ∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (data T).units
    HEq
      ((pullbackTensorCommonComposition l (PadicAlgCl l)
          (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
        (sourceId T).hom.app
          ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
      (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
  identity : ∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (data T).units
    (comparison T T (Iso.refl _)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (moduleId T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((ordinary l T.base.left (data T).realization).obj M) =
    (ordinary l T.base.left (data T).realization).map ((sourceId T).hom.app M)
  composition : ∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) V.base.left),
    letI := (data T).units
    letI := (data U).units
    letI := (data V).units
    (comparison T V (g ≪≫ h)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((ordinary l V.base.left (data V).realization).obj M) =
    (ordinary l T.base.left (data T).realization).map
        (pullbackTensorCommonComposition l (PadicAlgCl l) h.hom g.hom M).hom ≫
      (comparison T U g).hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) h.hom).obj M) ≫
      (derivedPull l T.base.left g.hom (ring T U g)).map ((comparison U V h).hom.app M)
  tensor_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
    letI := (data T).units
    letI := (data U).units
    (derivedPull l T.base.left g.hom (ring T U g)).map ((data U).tensor.tensor.hom.app (M, N)) ≫
      (comparison T U g).inv.app ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
        (M, N)) ≫
      (ordinary l T.base.left (data T).realization).map
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom =
    (pullTensor T U g).tensor.hom.app
        ((ordinary l U.base.left (data U).realization).obj M,
         (ordinary l U.base.left (data U).realization).obj N) ≫
      (data T).tensor.closed.tensor.map (Prod.mkHom
        ((comparison T U g).inv.app M) ((comparison T U g).inv.app N)) ≫
      (data T).tensor.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N)
  unit_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left),
    letI := (data T).units
    letI := (data U).units
    (derivedPull l T.base.left g.hom (ring T U g)).map (data U).tensor.unit.hom ≫
      (comparison T U g).inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left) ≫
      (ordinary l T.base.left (data T).realization).map
        (unit_spec T U g).exists.choose.hom =
    (pullUnit l T.base.left g.hom (pullTensor T U g)).hom ≫ (data T).tensor.unit.hom
  hom_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) U.base.left).FullSubcategory),
    letI := (data T).units
    letI := (data U).units
    (comparison T U g).hom.app
        ((commonStageDerivedInternalHom l (PadicAlgCl l) U.base.left).obj P) ≫
      (derivedPull l T.base.left g.hom (ring T U g)).map
        (homComparison l U.base.left (data U).realization (data U).tensor P) ≫
      pullHom l T.base.left g.hom (pullTensor T U g)
        ((ordinary l U.base.left (data U).realization).obj P.obj.1.unop)
        ((ordinary l U.base.left (data U).realization).obj P.obj.2) ≫
      (ambientHom l T.base.left (data T).realization).map
        (Prod.mkHom ((comparison T U g).hom.app P.obj.1.unop).op
          ((comparison T U g).inv.app P.obj.2)) =
    (ordinary l T.base.left (data T).realization).map
        (podCommonHomComparison l (PadicAlgCl l) g.hom P) ≫
      homComparison l T.base.left (data T).realization (data T).tensor
        ((podPairPullback (commonStageDerivedPullback l (PadicAlgCl l) g.hom)
      (commonStageHomPairs l (PadicAlgCl l) U.base.left)
      (commonStageHomPairs l (PadicAlgCl l) T.base.left)
      (podCommonPairs_pullback l (PadicAlgCl l) g.hom)).obj P)
```

The item publicly imports Sheaf.Paper.AdicRealizationFamilyData. The normalization
module replaces its public item import with the same new module. The item's original
four public imports remain transitively public through the new definition owner.
Every existing mathematical statement and definition has the same meaning. The
locked Challenge declarations are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicQbarConstructibleRealization | A8 | Publicly reexports unchanged definitions; closes the existence proof. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Its sole import of the parent becomes an import of the definition owner; exact theorem signature and proof retained. |
| Sheaf.Paper.AdicRealizationFamilyData | new, A8 | Owns the five unchanged declarations and their original public imports. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Uses Family and GeometricSpace through the item; exact reexports preserve its interface. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Transitive consumer; all original public declarations remain available. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Transitive consumer; all original public declarations remain available. |

The refreshed downstream.py audit reports the four downstream modules listed above.
AdicProperAdjunctionRealization appeared during this session; its use of Family and
GeometricSpace remains valid through the identical public reexport. The new owner,
the item and the adapted normalization module are compiled in dependency order.
No separately held module is adapted.

## Status

landed 20261025T013854-L-4029309 2026-10-25 (merge of deliver/A8/Sheaf.Paper.AdicQbarConstructibleRealization)
