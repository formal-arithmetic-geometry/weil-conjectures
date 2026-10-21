# AlgebraicGeometry.Scheme trace data declarations

## Reason

Move the sixteen supporting data declarations from FiniteEtaleTraceImage to
FiniteEtaleTraceDefinitions so the independent section-descent and sheet-lifting
lemmas can use them without an import cycle. FiniteEtaleTraceImage publicly
reexports the definitions module. Every signature and definition body is unchanged;
only the blueprint ownership annotations move to the new data node. The target
statements and the meaning of their definitions are unchanged.

## Old

In `lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceImage.lean`:

```lean
/-- Continuous ring coefficients on the existing small model, by precomposition.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceModelRing (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Sheaf (proEtaleModelTopology X) RingCat.{u + 1} :=
  ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The canonical continuous coefficient ring map on the small models.
Its component is precomposition with the actual fibre-product projection.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceContinuousRingMap (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] {V S : Scheme.{u}} (p : V ⟶ S) :
    traceModelRing S (continuousCoefficientSheaf S T) ⟶
      ((proEtaleModelBaseChange p).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology S) (proEtaleModelTopology V)).obj
          (traceModelRing V (continuousCoefficientSheaf V T)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (Functor.whiskerRight (continuousCoefficientDirectMap T p).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩

/-- The rational continuous ring sheaf in the equivalent small model.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
abbrev traceFieldRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  traceModelRing X (rationalCoefficientSheaf l X E)

/-- The integral continuous ring sheaf in the equivalent small model.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
abbrev traceIntegerRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  traceModelRing X (integralCoefficientSheaf l X E)

/-- The actual valuation-ring inclusion, on the equivalent small site.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceIntegerToField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    traceIntegerRing l E X ⟶ traceFieldRing l E X :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (Functor.whiskerRight (integralRationalCoefficientMap l E X).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩

/-- Pullback of rational coefficients is precomposition on continuous functions.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceFieldRingMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}} (p : V ⟶ S) :
    traceFieldRing l E S ⟶
      ((proEtaleModelBaseChange p).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology S) (proEtaleModelTopology V)).obj (traceFieldRing l E V) := by
  letI := coefficientExtensionNormedField l E
  exact traceContinuousRingMap (ULift.{u + 1, u} E) p

/-- Canonical coefficient pullback: the module Kan extension followed by sheafification.
Its adjunction unit fixes the generator maps used in the sheet formula below.
Source: blueprint, stratified-lattice proof, trace paragraph; Stacks Tag 03D2
(blueprint: lem-sfb-finite-etale-trace-image). -/
abbrev traceModulePullback (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}} (p : V ⟶ S) :=
  SheafOfModules.pullback.{u + 1} (traceFieldRingMap l E p)

/-- Direct image of rational modules, sectionwise at the chosen fibre product.
Source: blueprint, stratified-lattice proof, trace paragraph; Stacks Tag 03D1
(blueprint: lem-sfb-finite-etale-trace-image). -/
abbrev traceModuleDirectImage (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}} (p : V ⟶ S) :=
  SheafOfModules.pushforward.{u + 1} (traceFieldRingMap l E p)

/-- A splitting over U, presented by its sheets and their coproduct universal property.
The etaleness of each sheet map to V is automatic for a splitting over an etale U.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
structure TraceImageSplitting {V S : Scheme.{u}} (p : V ⟶ S) (U : S.ProEt)
    (J : Type u) where
  sheet : J → (U.left ⟶ V)
  over : ∀ j, sheet j ≫ p = U.hom
  etale : ∀ j, Etale (sheet j)
  coproduct : IsColimit (Cofan.mk (pullback U.hom p)
    (fun j ↦ pullback.lift (𝟙 U.left) (sheet j) (by simp only [Category.id_comp, over])))

attribute [instance] TraceImageSplitting.etale

/-- The j-th sheet above B → U, viewed as an object of V's pro-etale site.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceImageSheetObject {V S : Scheme.{u}} {p : V ⟶ S} {U : S.ProEt}
    {J : Type u} (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J) :
    V.ProEt := by
  letI : WeaklyEtale h.left := ProEt.weaklyEtale_slice S U (Over.mk h)
  exact ProEt.mk (h.left ≫ σ.sheet j)

/-- The canonical inclusion of a sheet into V ×_S B.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceImageSheetArrow {V S : Scheme.{u}} {p : V ⟶ S} {U : S.ProEt}
    {J : Type u} (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J) :
    traceImageSheetObject σ h j ⟶ (proEtaleBaseChange p).obj B :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 B.left) (h.left ≫ σ.sheet j)
      (by
        change 𝟙 B.left ≫ B.hom = (h.left ≫ σ.sheet j) ≫ p
        simp [Category.assoc, σ.over]))
    (pullback.lift_snd _ _ _)

/-- Restrict a section on V ×_S B to its j-th sheet.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceImageSheetRestriction {V S : Scheme.{u}} {p : V ⟶ S} {U : S.ProEt}
    {J : Type u} (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J)
    {R : Sheaf (proEtaleModelTopology V) RingCat.{u + 1}}
    (P : SheafOfModules.{u + 1} R)
    (s : P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    P.val.obj (op (AsSmall.up.obj (traceImageSheetObject σ h j))) :=
  P.val.map (AsSmall.up.map (traceImageSheetArrow σ h j)).op s

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V S : Scheme.{u}} (p : V ⟶ S)
  (L : SheafOfModules.{u + 1} (traceFieldRing l E S))

/-- The adjunction unit restricted to a sheet: the canonical identification with L there.
Source: blueprint, stratified-lattice proof, trace paragraph; Stacks Tag 03D2
(blueprint: lem-sfb-finite-etale-trace-image). -/
def traceImageSheetUnit {U : S.ProEt} {J : Type u} (σ : TraceImageSplitting p U J)
    {B : S.ProEt} (h : B ⟶ U) (j : J) (s : L.val.obj (op (AsSmall.up.obj B))) :
    ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj (traceImageSheetObject σ h j))) :=
  traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
    (((SheafOfModules.pullbackPushforwardAdjunction (traceFieldRingMap l E p)).unit.app
      L).val.app (op (AsSmall.up.obj B)) s)

/-- The sum formula on every splitting, tested on every object over its base.
The unit comparison fixes the sheet coordinates, without choosing any isomorphism.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def TraceImageLocalSums
    (τ : (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L) ⟶ L) :
    Prop :=
  ∀ (U : S.ProEt) (_ : Etale U.hom) (J : Type u) [Fintype J]
    (σ : TraceImageSplitting p U J) (B : S.ProEt) (h : B ⟶ U)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B))))
    (t : J → L.val.obj (op (AsSmall.up.obj B))),
    (∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L) s =
      traceImageSheetUnit l E p L σ h j (t j)) →
      τ.val.app (op (AsSmall.up.obj B)) s = ∑ j, t j

variable
  (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
    ((traceModulePullback l E p).obj L)).val.Submodule)

/-- Local trace representatives, the sheaf image rather than the image on global sections.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def TraceImageLocalRepresentatives
    (τ : (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L) ⟶ L)
    (B : S.ProEt) (s : L.val.obj (op (AsSmall.up.obj B))) : Prop :=
  ∃ R : Sieve B, R ∈ ProEt.topology S B ∧
    ∀ (C : S.ProEt) (a : C ⟶ B), R a →
      ∃ m : M.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C))),
        τ.val.app (op (AsSmall.up.obj C)) m.val = L.val.map (AsSmall.up.map a).op s

/-- The sheaf sum of the sheet submodules, expressed by local finite sums.
Membership of t_j in the j-th sheet is tested after the canonical pullback unit.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: lem-sfb-finite-etale-trace-image). -/
def TraceImageLocalSheetSum {U : S.ProEt} {J : Type u} [Fintype J]
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U)
    (s : L.val.obj (op (AsSmall.up.obj B))) : Prop :=
  ∃ R : Sieve B, R ∈ ProEt.topology S B ∧
    ∀ (C : S.ProEt) (a : C ⟶ B), R a →
      ∃ t : J → L.val.obj (op (AsSmall.up.obj C)),
        (∑ j, t j) = L.val.map (AsSmall.up.map a).op s ∧
          ∀ j, traceImageSheetUnit l E p L σ (a ≫ h) j (t j) ∈
            M.obj (op (AsSmall.up.obj (traceImageSheetObject σ (a ≫ h) j)))
```

## New

In `lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceDefinitions.lean`:

```lean
/-- Continuous ring coefficients on the existing small model, by precomposition.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceModelRing (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Sheaf (proEtaleModelTopology X) RingCat.{u + 1} :=
  ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The canonical continuous coefficient ring map on the small models.
Its component is precomposition with the actual fibre-product projection.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceContinuousRingMap (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] {V S : Scheme.{u}} (p : V ⟶ S) :
    traceModelRing S (continuousCoefficientSheaf S T) ⟶
      ((proEtaleModelBaseChange p).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology S) (proEtaleModelTopology V)).obj
          (traceModelRing V (continuousCoefficientSheaf V T)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (Functor.whiskerRight (continuousCoefficientDirectMap T p).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩

/-- The rational continuous ring sheaf in the equivalent small model.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
abbrev traceFieldRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  traceModelRing X (rationalCoefficientSheaf l X E)

/-- The integral continuous ring sheaf in the equivalent small model.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
abbrev traceIntegerRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  traceModelRing X (integralCoefficientSheaf l X E)

/-- The actual valuation-ring inclusion, on the equivalent small site.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceIntegerToField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    traceIntegerRing l E X ⟶ traceFieldRing l E X :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (Functor.whiskerRight (integralRationalCoefficientMap l E X).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))⟩

/-- Pullback of rational coefficients is precomposition on continuous functions.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceFieldRingMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}} (p : V ⟶ S) :
    traceFieldRing l E S ⟶
      ((proEtaleModelBaseChange p).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology S) (proEtaleModelTopology V)).obj (traceFieldRing l E V) := by
  letI := coefficientExtensionNormedField l E
  exact traceContinuousRingMap (ULift.{u + 1, u} E) p

/-- Canonical coefficient pullback: the module Kan extension followed by sheafification.
Its adjunction unit fixes the generator maps used in the sheet formula below.
Source: blueprint, stratified-lattice proof, trace paragraph; Stacks Tag 03D2
(blueprint: def-sfb-finite-etale-trace-data). -/
abbrev traceModulePullback (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}} (p : V ⟶ S) :=
  SheafOfModules.pullback.{u + 1} (traceFieldRingMap l E p)

/-- Direct image of rational modules, sectionwise at the chosen fibre product.
Source: blueprint, stratified-lattice proof, trace paragraph; Stacks Tag 03D1
(blueprint: def-sfb-finite-etale-trace-data). -/
abbrev traceModuleDirectImage (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}} (p : V ⟶ S) :=
  SheafOfModules.pushforward.{u + 1} (traceFieldRingMap l E p)

/-- A splitting over U, presented by its sheets and their coproduct universal property.
The etaleness of each sheet map to V is automatic for a splitting over an etale U.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
structure TraceImageSplitting {V S : Scheme.{u}} (p : V ⟶ S) (U : S.ProEt)
    (J : Type u) where
  sheet : J → (U.left ⟶ V)
  over : ∀ j, sheet j ≫ p = U.hom
  etale : ∀ j, Etale (sheet j)
  coproduct : IsColimit (Cofan.mk (pullback U.hom p)
    (fun j ↦ pullback.lift (𝟙 U.left) (sheet j) (by simp only [Category.id_comp, over])))

attribute [instance] TraceImageSplitting.etale

/-- The j-th sheet above B → U, viewed as an object of V's pro-etale site.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceImageSheetObject {V S : Scheme.{u}} {p : V ⟶ S} {U : S.ProEt}
    {J : Type u} (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J) :
    V.ProEt := by
  letI : WeaklyEtale h.left := ProEt.weaklyEtale_slice S U (Over.mk h)
  exact ProEt.mk (h.left ≫ σ.sheet j)

/-- The canonical inclusion of a sheet into V ×_S B.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceImageSheetArrow {V S : Scheme.{u}} {p : V ⟶ S} {U : S.ProEt}
    {J : Type u} (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J) :
    traceImageSheetObject σ h j ⟶ (proEtaleBaseChange p).obj B :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 B.left) (h.left ≫ σ.sheet j)
      (by
        change 𝟙 B.left ≫ B.hom = (h.left ≫ σ.sheet j) ≫ p
        simp [Category.assoc, σ.over]))
    (pullback.lift_snd _ _ _)

/-- Restrict a section on V ×_S B to its j-th sheet.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceImageSheetRestriction {V S : Scheme.{u}} {p : V ⟶ S} {U : S.ProEt}
    {J : Type u} (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U) (j : J)
    {R : Sheaf (proEtaleModelTopology V) RingCat.{u + 1}}
    (P : SheafOfModules.{u + 1} R)
    (s : P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B)))) :
    P.val.obj (op (AsSmall.up.obj (traceImageSheetObject σ h j))) :=
  P.val.map (AsSmall.up.map (traceImageSheetArrow σ h j)).op s

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V S : Scheme.{u}} (p : V ⟶ S)
  (L : SheafOfModules.{u + 1} (traceFieldRing l E S))

/-- The adjunction unit restricted to a sheet: the canonical identification with L there.
Source: blueprint, stratified-lattice proof, trace paragraph; Stacks Tag 03D2
(blueprint: def-sfb-finite-etale-trace-data). -/
def traceImageSheetUnit {U : S.ProEt} {J : Type u} (σ : TraceImageSplitting p U J)
    {B : S.ProEt} (h : B ⟶ U) (j : J) (s : L.val.obj (op (AsSmall.up.obj B))) :
    ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj (traceImageSheetObject σ h j))) :=
  traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
    (((SheafOfModules.pullbackPushforwardAdjunction (traceFieldRingMap l E p)).unit.app
      L).val.app (op (AsSmall.up.obj B)) s)

/-- The sum formula on every splitting, tested on every object over its base.
The unit comparison fixes the sheet coordinates, without choosing any isomorphism.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def TraceImageLocalSums
    (τ : (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L) ⟶ L) :
    Prop :=
  ∀ (U : S.ProEt) (_ : Etale U.hom) (J : Type u) [Fintype J]
    (σ : TraceImageSplitting p U J) (B : S.ProEt) (h : B ⟶ U)
    (s : ((traceModulePullback l E p).obj L).val.obj
      (op (AsSmall.up.obj ((proEtaleBaseChange p).obj B))))
    (t : J → L.val.obj (op (AsSmall.up.obj B))),
    (∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L) s =
      traceImageSheetUnit l E p L σ h j (t j)) →
      τ.val.app (op (AsSmall.up.obj B)) s = ∑ j, t j

variable
  (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
    ((traceModulePullback l E p).obj L)).val.Submodule)

/-- Local trace representatives, the sheaf image rather than the image on global sections.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def TraceImageLocalRepresentatives
    (τ : (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L) ⟶ L)
    (B : S.ProEt) (s : L.val.obj (op (AsSmall.up.obj B))) : Prop :=
  ∃ R : Sieve B, R ∈ ProEt.topology S B ∧
    ∀ (C : S.ProEt) (a : C ⟶ B), R a →
      ∃ m : M.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C))),
        τ.val.app (op (AsSmall.up.obj C)) m.val = L.val.map (AsSmall.up.map a).op s

/-- The sheaf sum of the sheet submodules, expressed by local finite sums.
Membership of t_j in the j-th sheet is tested after the canonical pullback unit.
Source: blueprint, stratified-lattice proof, trace paragraph
(blueprint: def-sfb-finite-etale-trace-data). -/
def TraceImageLocalSheetSum {U : S.ProEt} {J : Type u} [Fintype J]
    (σ : TraceImageSplitting p U J) {B : S.ProEt} (h : B ⟶ U)
    (s : L.val.obj (op (AsSmall.up.obj B))) : Prop :=
  ∃ R : Sieve B, R ∈ ProEt.topology S B ∧
    ∀ (C : S.ProEt) (a : C ⟶ B), R a →
      ∃ t : J → L.val.obj (op (AsSmall.up.obj C)),
        (∑ j, t j) = L.val.map (AsSmall.up.map a).op s ∧
          ∀ j, traceImageSheetUnit l E p L σ (a ≫ h) j (t j) ∈
            M.obj (op (AsSmall.up.obj (traceImageSheetObject σ (a ≫ h) j)))
```

The original module contains a public import of
`Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions`, preserving every old name.

## Users

The repository downstream scan reports zero modules downstream of
FiniteEtaleTraceImage. Searches for the sixteen names find only the original
module. Its unfinished DAG parent still needs the trace-image statement;
that statement and the unit route are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage | S2 | Publicly reexports the data; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions | new, S2 | Holds the unchanged data. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceSheetLifting | new, S2 | Proves sheet coordinates and integral gluing. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent | new, S2 | Proves per-section descent using the data. |

No modules held by other groups are adapted. The unique trace section is chosen
only from a theorem asserting existence and uniqueness. No arbitrary data witness
is chosen from a theorem with a hole.

## Status

landed 20261021T111606-L-368636 2026-10-21 (merge of deliver/S2/Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage)
