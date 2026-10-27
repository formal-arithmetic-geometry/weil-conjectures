# Diagonal orientation refinement data relocation

Delivery path: `coord/changes/T8-diagonal-orientation-data-relocation.md`.
For the stage-3 reviewer's `--apply-fixes` directory, the corresponding flat filename is
`T8-diagonal-orientation-data-relocation.change.md`. The landing tool derives this alias
from the delivery path's stem; the ordinary `.md` basename is not an accepted fix alias.

## Reason

Independent lemmas about normal-zero-section normalization and restriction must import the
chart definitions without importing the theorem that assembles those lemmas. Move the existing
data into `Sheaf.Paper.DiagonalOrientationRefinementData` and publicly reexport that module from
the original module. This is an interface relocation to avoid an import cycle, not a split
undertaken to meet a compile time limit. No existing definition, binder, universe, name,
visibility, or theorem statement changes. No source-library module is edited.

## Old

The following definitions were in `lean/Sheaf/Paper/DiagonalOrientationRefinement.lean`:

```lean
/-- The recorded inverse image, at fixed finite coefficients.
Source: derived pullback convention (blueprint: lem-pur-diagonal-orientation-refinement). -/
abbrev pull (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (h : T ⟶ S) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).leftDerivedFunctor

/-- The canonical nu* realization of omega_h, with compactifiability derived by Nagata.
Source: exceptional inverse image and the comparison unit, proof Step 2
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def omega (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (h : T ⟶ S)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS] :=
  letI := Dnc.compactifiable P h aS
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h)

/-- Canonical finite Tate pullback, including the ordered even shifts.
Source: Cartesian coefficient twists and finite Tate site descent, proof Steps 2 and 7
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def tate (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (h : T ⟶ S)
    (aS : S ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  Dnc.pullComparison P h (P.diagonalTwistEtale S d) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates
          (purityTwistTransport P.Coefficient P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
          h (P.diagonalExponent_isUnit aS) d)

/-- The inverse of zero-section restriction of vector purity, characterized by integration.
Only actual pullback, the normalized finite Tate comparison and the Brown adjunct occur.
Source: vector-bundle purity at the unit, proof Step 2
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def vectorBetaInverse (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :=
  letI := P.noetherian aB
  letI := (Etale.vectorIntegration_geometry B d F).1
  letI := (Etale.vectorIntegration_geometry B d F).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  let t := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  let z := VectorBundleZeroSection.zero B d F
  let π := VectorBundleZeroSection.π B d F
  (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t z (P.diagonalExponent_isUnit (π ≫ aB)) d).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient z).map
      ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t π (P.diagonalExponent_isUnit aB) d).inv ≫
        (Etale.rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} P.Coefficient) π).homEquiv _ _
          (Etale.vectorBundleIntegration P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
            P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
            (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom))

/-- The actual diagonal section invariant on one affine target open.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def source (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  Dnc.sourceSection P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))

/-- The normal-bundle zero-section invariant on the same open.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def normal (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  Dnc.normalSection P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
    (pullback.diagonal_fst (f ∣_ V.1))

/-- Ordinary-etale coordinates for the actual normal-section object.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def normalEtale (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  Dnc.normalEtale P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
    (pullback.diagonal_fst (f ∣_ V.1))

/-- The recorded specified diagonal base-change comparison.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def alpha (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  P.affineDiagonalAlpha d (f ∣_ V.1) (V.1.ι ≫ aY)

/-- The recorded specified target-open restriction of the dualizing object.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def rho (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  P.affineDiagonalRho f aY d V.1

/-- The unique normalized DNC comparison, selected by its full family equation.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def delta (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  (Dnc.existsUnique_dncInvariance P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
    (pullback.diagonal_fst (f ∣_ V.1))).exists.choose

/-- The zero-section comparison transported by the recorded canonical site comparison.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def beta (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (b : normalEtale P f aY d V H ≅ P.diagonalTwistEtale (f ⁻¹ᵁ V.1).toScheme d) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  Dnc.normalComparison P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
      (pullback.diagonal_fst (f ∣_ V.1)) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).toScheme).mapDerivedCategory.mapIso b

/-- The specified four-factor local isomorphism rho, alpha inverse, delta, beta.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def theta (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (b : normalEtale P f aY d V H ≅ P.diagonalTwistEtale (f ⁻¹ᵁ V.1).toScheme d) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  rho P f aY d V H ≪≫ (alpha P f aY d V H).symm ≪≫
    delta P f aY d V H ≪≫ beta P f aY d V H b

/-- Beta is restriction of integration-normalized vector purity in every bundle model.
The two section pullbacks are identified by the specified smooth exchange. All models
preserve projection and zero section; existence of a model is asserted separately.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def BetaNormalized (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (b : normalEtale P f aY d V H ≅ P.diagonalTwistEtale (f ⁻¹ᵁ V.1).toScheme d) : Prop :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  let B := (f ⁻¹ᵁ V.1).toScheme
  let g := pullback.fst (f ∣_ V.1) (f ∣_ V.1)
  let s := pullback.diagonal (f ∣_ V.1)
  let q := Scheme.Hom.normalConeProj g s
  letI := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  letI := Dnc.normalCompactifiable P d g ((f ∣_ V.1) ≫ V.1.ι ≫ aY) s
    (pullback.diagonal_fst (f ∣_ V.1))
  letI : SmoothOfRelativeDimension d q :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst (f ∣_ V.1))).smoothOfRelativeDimension_proj
  letI := Dnc.invertibleExponent P (q ≫ (f ∣_ V.1) ≫ V.1.ι ≫ aY)
  ∀ (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (e : VectorBundleZeroSection.scheme B d F ≅ s.ker.normalCone)
    (w : e.hom ≫ q = VectorBundleZeroSection.π B d F)
    (hz : VectorBundleZeroSection.zero B d F ≫ e.hom = s.normalConeZeroSection),
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F)
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
    b.inv ≫
      ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫
        (Dnc.sectionBaseChange P.Coefficient d q
          (IsPullback.of_horiz_isIso ⟨w.trans (Category.comp_id _).symm⟩)
          s.normalConeZeroSection (VectorBundleZeroSection.zero B d F)
          (hz.trans (Category.id_comp _).symm)).hom) =
      vectorBetaInverse P B ((f ∣_ V.1) ≫ V.1.ι ≫ aY) d F

/-- The normal object really is a rank-d vector bundle, with projection and zero.
Source: blueprint proof Steps 1--3
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def HasVectorModel (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) : Prop :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  letI := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  ∃ (F : (f ⁻¹ᵁ V.1).toScheme.Modules) (hF : F.IsFiniteLocallyFreeOfRank d),
    ∃ e : @VectorBundleZeroSection.scheme _ inferInstance d F hF ≅
      (pullback.diagonal (f ∣_ V.1)).ker.normalCone,
      e.hom ≫ Scheme.Hom.normalConeProj (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        (pullback.diagonal (f ∣_ V.1)) = @VectorBundleZeroSection.π _ inferInstance d F hF ∧
      @VectorBundleZeroSection.zero _ inferInstance d F hF ≫ e.hom =
        (pullback.diagonal (f ∣_ V.1)).normalConeZeroSection

/-- The canonical inclusion on inverse images of nested affine target opens.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def inclusion {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Y.Opens} (h : V' ≤ V) :=
  X.homOfLE (f.preimage_mono h)

/-- The canonical pullback of a smooth dualizing object, in comparison coordinates.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def exchange (P : PurityFiniteSetting.{u}) {T S T' S' : Scheme.{u}}
    (d : ℕ) (g : T ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (g' : T' ⟶ S') [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (aS' : S' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS'] [QuasiCompact aS']
    {v : T' ⟶ T} {b : S' ⟶ S} (sq : IsPullback v g' g b) :=
  letI := Dnc.compactifiable P g aS
  letI := Dnc.compactifiable P g' aS'
  letI := Dnc.invertibleExponent P (g ≫ aS)
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient g d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (inferInstanceAs (IsIso
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app (𝟙_ _))))
  Dnc.pullComparison P v (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) g) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T').mapDerivedCategory.mapIso
        (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq))

/-- The section pullback of the same smooth exchange, including all compositors.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def sectionExchange (P : PurityFiniteSetting.{u}) {T S T' S' : Scheme.{u}}
    (d : ℕ) (g : T ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (g' : T' ⟶ S') [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (aS' : S' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS'] [QuasiCompact aS']
    {v : T' ⟶ T} {b : S' ⟶ S} (sq : IsPullback v g' g b)
    (s : S ⟶ T) (s' : S' ⟶ T') (hs : s' ≫ v = b ≫ s) :=
  letI := Dnc.compactifiable P g aS
  letI := Dnc.compactifiable P g' aS'
  letI := Dnc.invertibleExponent P (g ≫ aS)
  Dnc.pullComparison P b (Etale.sectionInvariant P.Coefficient g s) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) S').mapDerivedCategory.mapIso
        (Dnc.sectionBaseChange P.Coefficient d g sq s s' hs)

/-- Canonical source composition from iterated open restriction to direct restriction.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def sourceComposition (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    {V V' : Y.Opens} (h : V' ≤ V) :=
  (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (inclusion f h) (f ⁻¹ᵁ V).ι).symm.app (omega P f aY) ≪≫
    eqToIso (congrArg (fun j ↦ (pull P j).obj (omega P f aY))
      (X.homOfLE_ι (f.preimage_mono h)))

/-- The canonical geometric maps of the two diagonal section pairs under restriction.
The normal map is fixed by its closed-fibre composite with the coefficientwise Rees map.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
structure Geometry {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    {V V' : Y.affineOpens} (h : V'.1 ≤ V.1) where
  product : pullback (f ∣_ V'.1) (f ∣_ V'.1) ⟶ pullback (f ∣_ V.1) (f ∣_ V.1)
  fst_eq : product ≫ pullback.fst (f ∣_ V.1) (f ∣_ V.1) =
    pullback.fst (f ∣_ V'.1) (f ∣_ V'.1) ≫ inclusion f h
  snd_eq : product ≫ pullback.snd (f ∣_ V.1) (f ∣_ V.1) =
    pullback.snd (f ∣_ V'.1) (f ∣_ V'.1) ≫ inclusion f h
  diagonal_eq : pullback.diagonal (f ∣_ V'.1) ≫ product =
    inclusion f h ≫ pullback.diagonal (f ∣_ V.1)
  cartesian : IsPullback product (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
    (pullback.fst (f ∣_ V.1) (f ∣_ V.1)) (inclusion f h)
  normal : (pullback.diagonal (f ∣_ V'.1)).ker.normalCone ⟶
    (pullback.diagonal (f ∣_ V.1)).ker.normalCone
  normal_eq : normal ≫ (pullback.diagonal (f ∣_ V.1)).ker.normalConeToDeformationSpace =
    (pullback.diagonal (f ∣_ V'.1)).ker.normalConeToDeformationSpace ≫
      SectionReesBaseChange.pairMap (pullback.diagonal (f ∣_ V.1))
        (pullback.diagonal (f ∣_ V'.1)) product (inclusion f h) diagonal_eq
  normal_cartesian : IsPullback normal
    (Scheme.Hom.normalConeProj (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
      (pullback.diagonal (f ∣_ V'.1)))
    (Scheme.Hom.normalConeProj (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
      (pullback.diagonal (f ∣_ V.1))) (inclusion f h)
  zero_eq : (pullback.diagonal (f ∣_ V'.1)).normalConeZeroSection ≫ normal =
    inclusion f h ≫ (pullback.diagonal (f ∣_ V.1)).normalConeZeroSection

/-- The recorded canonical site comparison for the section object.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def sourceComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  Dnc.sourceComparison P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))

/-- The recorded canonical site comparison for the section object.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def normalComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  Dnc.normalComparison P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
    (pullback.diagonal_fst (f ∣_ V.1))

/-- Canonical section exchange for the diagonal pair, using its actual Cartesian square.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def eC (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (H : P.AffineDiagonalGeometry f aY d V)
    (H' : P.AffineDiagonalGeometry f aY d V') (h : V'.1 ≤ V.1) (G : Geometry f h) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  letI := H'.separated
  letI := H'.finiteType
  letI := H'.quasiCompact
  letI := H'.smoothDimension
  letI := H'.baseFiniteType
  letI := H'.baseQuasiCompact
  letI := H'.sourceSeparated
  letI := H'.sourceFiniteType
  letI := H'.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  (pull P (inclusion f h)).mapIso (sourceComparison P f aY d V H) ≪≫
    sectionExchange P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
      (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) ((f ∣_ V'.1) ≫ V'.1.ι ≫ aY)
      G.cartesian (pullback.diagonal (f ∣_ V.1)) (pullback.diagonal (f ∣_ V'.1))
      G.diagonal_eq ≪≫ (sourceComparison P f aY d V' H').symm

/-- Canonical section exchange for the actual normal-bundle zero section.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def eN (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (H : P.AffineDiagonalGeometry f aY d V)
    (H' : P.AffineDiagonalGeometry f aY d V') (h : V'.1 ≤ V.1) (G : Geometry f h) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  letI := H'.separated
  letI := H'.finiteType
  letI := H'.quasiCompact
  letI := H'.smoothDimension
  letI := H'.baseFiniteType
  letI := H'.baseQuasiCompact
  letI := H'.sourceSeparated
  letI := H'.sourceFiniteType
  letI := H'.sourceQuasiCompact
  letI := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  letI := Dnc.normalCompactifiable P d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (pullback.diagonal (f ∣_ V.1))
    (pullback.diagonal_fst (f ∣_ V.1))
  letI := Dnc.normalCompactifiable P d (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
    ((f ∣_ V'.1) ≫ V'.1.ι ≫ aY) (pullback.diagonal (f ∣_ V'.1))
    (pullback.diagonal_fst (f ∣_ V'.1))
  letI := Dnc.normalQuasiCompact d (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
    (pullback.diagonal (f ∣_ V.1)) (pullback.diagonal_fst (f ∣_ V.1))
  letI := Dnc.normalQuasiCompact d (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
    (pullback.diagonal (f ∣_ V'.1)) (pullback.diagonal_fst (f ∣_ V'.1))
  letI : SmoothOfRelativeDimension d
      (Scheme.Hom.normalConeProj (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        (pullback.diagonal (f ∣_ V.1))) :=
    (Scheme.Hom.normalConeData d
      (pullback.diagonal_fst (f ∣_ V.1))).smoothOfRelativeDimension_proj
  (pull P (inclusion f h)).mapIso (normalComparison P f aY d V H) ≪≫
    sectionExchange P d
      (Scheme.Hom.normalConeProj (pullback.fst (f ∣_ V.1) (f ∣_ V.1))
        (pullback.diagonal (f ∣_ V.1)))
      (Scheme.Hom.normalConeProj (pullback.fst (f ∣_ V'.1) (f ∣_ V'.1))
        (pullback.diagonal (f ∣_ V'.1)))
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) ((f ∣_ V'.1) ≫ V'.1.ι ≫ aY)
      G.normal_cartesian (pullback.diagonal (f ∣_ V.1)).normalConeZeroSection
      (pullback.diagonal (f ∣_ V'.1)).normalConeZeroSection G.zero_eq ≪≫
    (normalComparison P f aY d V' H').symm

/-- The local normal comparison with its specified vector-purity normalization.
The geometric instances are conclusions from affineTargetDiagonalDnc.
Source: blueprint Step 2 (blueprint: lem-pur-diagonal-orientation-refinement). -/
structure Chart (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens) where
  geometry : P.AffineDiagonalGeometry f aY d V
  vectorModel : HasVectorModel P f aY d V geometry
  betaEtale : normalEtale P f aY d V geometry ≅ P.diagonalTwistEtale (f ⁻¹ᵁ V.1).toScheme d
  normalized : BetaNormalized P f aY d V geometry betaEtale

/-- The canonical smooth exchange on the restricted map f_V itself.
Source: blueprint combining paragraph, proof Step 5
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def eF (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (H : P.AffineDiagonalGeometry f aY d V)
    (H' : P.AffineDiagonalGeometry f aY d V') (h : V'.1 ≤ V.1)
    (sq : IsPullback (inclusion f h) (f ∣_ V'.1) (f ∣_ V.1) (Y.homOfLE h)) :=
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H'.separated
  letI := H'.finiteType
  letI := H'.quasiCompact
  letI := H'.smoothDimension
  letI := H'.baseFiniteType
  letI := H'.baseQuasiCompact
  exchange P d (f ∣_ V.1) (f ∣_ V'.1) (V.1.ι ≫ aY) (V'.1.ι ≫ aY) sq

/-- Equality of the specified local composite after canonical source and Tate restriction.
Source: blueprint combining paragraph, proof Step 8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def Agrees (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (D : Chart P f aY d V) (D' : Chart P f aY d V') (h : V'.1 ≤ V.1) : Prop :=
  sourceComposition P f aY h ≪≫ theta P f aY d V' D'.geometry D'.betaEtale =
    (pull P (inclusion f h)).mapIso (theta P f aY d V D.geometry D.betaEtale) ≪≫
      tate P (inclusion f h) ((f ∣_ V.1) ≫ V.1.ι ≫ aY) d

/-- The four individual comparison equations on a smaller affine open.
Every arrow is the actual exchange or comparison constructed above.
Source: blueprint combining paragraph, proof Steps 4--8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def Compatible (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (D : Chart P f aY d V) (D' : Chart P f aY d V') (h : V'.1 ≤ V.1) : Prop :=
  ∃ (sq : IsPullback (inclusion f h) (f ∣_ V'.1) (f ∣_ V.1) (Y.homOfLE h))
    (G : Geometry f h),
    (pull P (inclusion f h)).mapIso (rho P f aY d V D.geometry) ≪≫
        eF P f aY d D.geometry D'.geometry h sq =
      sourceComposition P f aY h ≪≫ rho P f aY d V' D'.geometry ∧
    (pull P (inclusion f h)).mapIso (alpha P f aY d V D.geometry) ≪≫
        eF P f aY d D.geometry D'.geometry h sq =
      eC P f aY d D.geometry D'.geometry h G ≪≫ alpha P f aY d V' D'.geometry ∧
    (pull P (inclusion f h)).mapIso (delta P f aY d V D.geometry) ≪≫
        eN P f aY d D.geometry D'.geometry h G =
      eC P f aY d D.geometry D'.geometry h G ≪≫ delta P f aY d V' D'.geometry ∧
    (pull P (inclusion f h)).mapIso (beta P f aY d V D.geometry D.betaEtale) ≪≫
        tate P (inclusion f h) ((f ∣_ V.1) ≫ V.1.ι ≫ aY) d =
      eN P f aY d D.geometry D'.geometry h G ≪≫
        beta P f aY d V' D'.geometry D'.betaEtale

/-- Restrict a specified local orientation using the canonical source and Tate maps.
Source: blueprint combining paragraph, proof Step 8
(blueprint: lem-pur-diagonal-orientation-refinement). -/
def restricted (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V : Y.affineOpens}
    (D : Chart P f aY d V) {V' : Y.affineOpens} (h : V'.1 ≤ V.1) :=
  (sourceComposition P f aY h).symm ≪≫
    (pull P (inclusion f h)).mapIso (theta P f aY d V D.geometry D.betaEtale) ≪≫
      tate P (inclusion f h) ((f ∣_ V.1) ≫ V.1.ι ≫ aY) d
```

## New

The same text, verbatim, is now in
`lean/Sheaf/Paper/DiagonalOrientationRefinementData.lean`. The original module has:

```lean
public import Sheaf.Paper.DiagonalOrientationRefinementData
```

The public import makes every existing declaration available to every original consumer.
The existing two definition-node Lean attachments point to the new owner module; the main
statement node retains only its assembly theorem. The new data node records the other
relocated declarations. The new proof lemmas are private imports of the original module.
Every original public dependency is still publicly reachable through the data module.
Only unused private proof imports are removed. A text comparison confirmed all definition
bodies and the original theorem signature are byte-for-byte identical. Therefore no target
meaning changes and no target statement re-review is requested.

## Users

`tools/downstream.py Sheaf.Paper.DiagonalOrientationRefinement --uses
WeilConjectures.PurityFiniteSetting.OrientationRefinement` finds the following consumers.
The claim files for the downstream modules were checked in the current shared snapshot
on 2026-10-26. The table also includes the new modules that directly import the relocated API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Publicly reexports unchanged data; proves assembly. |
| Sheaf.Paper.DiagonalOrientationRefinementData | T8, new in this packet | Owns the unchanged definitions. |
| Sheaf.Paper.ComparedSmoothExchangeComposition | T8, new in this packet | Imports the data API for proved exchange equations. |
| Sheaf.Paper.VectorZeroSectionIntegrationBaseChange | T8, new in this packet | Imports the data API for the isolated integration statement. |
| Sheaf.Paper.DiagonalOrientationChartExistence | T8, new in this packet | Imports the data API for the proved chart construction. |
| Sheaf.Paper.DiagonalOrientationCompatibility | T8, new in this packet | Imports the data API for the proved comparison equations. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same public declarations and definitions; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same public declarations and definitions; no adaptation. |

Complete list of downstream modules that mention a relocated name (computed by the
delivery packet at head 8202d841b9a7; reviewer addition, 2026-10-26). Each still sees every
relocated declaration under the same name, binders and visibility through the public import of
`Sheaf.Paper.DiagonalOrientationRefinementData` by `Sheaf.Paper.DiagonalOrientationRefinement`;
none needs an adaptation. The direct importers `DiagonalAffineCounitRestriction`,
`DiagonalOrdinaryChartLift`, `DiagonalOrdinaryOrientationGluing`,
`DiagonalOrdinaryOrientationNormalization`, `NormalSectionIntegrationBaseChange`,
`SectionDncIntegrationSquare` and `VectorBundleFrameOrientationRestriction` were compiled
unchanged against the delivered modules.

| module | group holding it |
| --- | --- |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed |
| Sheaf.Paper.AffineCoefficientCounitNormalization | C1 |
| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | unclaimed |
| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | B3 |
| Sheaf.Paper.AffineDiagonalSectionCoordinates | unclaimed |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed |
| Sheaf.Paper.AffineLinePuritySource | unclaimed |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | C1 |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed |
| Sheaf.Paper.CentredDiagonalSourcePasting | D3 |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed |
| Sheaf.Paper.ChartDncNaturality | unclaimed |
| Sheaf.Paper.ChartDncSquare | unclaimed |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed |
| Sheaf.Paper.CompositionComparisons | unclaimed |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed |
| Sheaf.Paper.CoordinateAdjunctionComposition | E4 |
| Sheaf.Paper.CoordinateLineAdjunction | G9 |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | K6 |
| Sheaf.Paper.DiagonalAffineCounitRestriction | unclaimed |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | J3 |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 |
| Sheaf.Paper.DiagonalOrdinaryChartLift | unclaimed |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed |
| Sheaf.Paper.DiagonalOrdinaryOverlap | R3 |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed |
| Sheaf.Paper.FieldPuritySystemTranspose | C1 |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed |
| Sheaf.Paper.FiniteOrientationReduction | E3 |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed |
| Sheaf.Paper.GeneralChartComparisons | unclaimed |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 |
| Sheaf.Paper.LineZeroClassExchange | unclaimed |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed |
| Sheaf.Paper.LocalizedTopChern | unclaimed |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed |
| Sheaf.Paper.OrderedAffineTransposeData | unclaimed |
| Sheaf.Paper.OrderedIntegrationComparison | unclaimed |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed |
| Sheaf.Paper.PurityCompositionCoherence | F3 |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | H3 |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | J1 |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed |
| Sheaf.Paper.RationalSmoothPurityCanonical | U7 |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed |
| Sheaf.Paper.SupportedCartierDerivedPullback | unclaimed |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed |
| Sheaf.Paper.TwistFrobeniusScalar | T8 |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed |
| Sheaf.Paper.VectorBundleThomClass | unclaimed |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed |


## Status

landed 20261026T024055-L-635898 2026-10-26 (merge of deliver/T8/Sheaf.Paper.DiagonalOrientationRefinement)
