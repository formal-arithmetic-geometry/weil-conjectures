# WeilConjectures.CoefFiniteHomStrong and finite Hom site descent data

## Reason

The three smaller source obligations need the fixed predicates and canonical arrows,
while the item theorem needs to import those obligations. Extracting the definitions
prevents an import cycle. Their declarations, universes, attributes and bodies are
verbatim. The original module publicly reexports the new data module, which retains
all original public imports. No target statement, mathematical definition, instance,
or global attribute changes. The right-closed tensor-square bridge is proved in a
new proof-only imported module; it does not require a braiding or a unit axiom.

## Old

In lean/Sheaf/Paper/CoefFiniteHomSiteDescent.lean:

```lean
/-- Strong monoidality for a specified tensor comparison, including unit and associativity.
The unit is determined by this tensorator and the two unit axioms, so it is not extra
unconstrained comparison data. Source: blueprint final paragraph; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomStrong
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :=
  letI := SA.monoidal
  letI := SB.monoidal
  {s : F.CoreMonoidal // ∀ P Q : A, s.μIso P Q = (μ.app (P, Q)).symm}

/-- The monoidal square equations for the fixed tensorators and their coherent units.
Source: blueprint final site-comparison sentence; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomMonoidalSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G) : Prop :=
  ∃ sF : CoefFiniteHomStrong SA SB F μF,
    ∃ sG : CoefFiniteHomStrong SC SD G μG,
      ∃ sU : CoefFiniteHomStrong SA SC U μU,
        ∃ sV : CoefFiniteHomStrong SB SD V μV,
          (∀ K M : A,
            h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
                μG.hom.app (U.obj K, U.obj M) =
              V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
                SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M))) ∧
          h.hom.app SA.monoidal.tensorUnit ≫
              G.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SC.monoidal U sU.val).inv ≫
              (@Functor.CoreMonoidal.εIso _ _ SC.monoidal _ _ SD.monoidal G sG.val).inv =
            V.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SB.monoidal F sF.val).inv ≫
              (@Functor.CoreMonoidal.εIso _ _ SB.monoidal _ _ SD.monoidal V sV.val).inv

/-- Naturality, evaluation/transpose and internal composition at finite-Tor pairs.
This is the restriction of the existing coefficient evaluation equations to the stated
constructible domain. Source: blueprint final paragraph, equations transported by the square
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomLawsOn
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P : ObjectProperty A) : Prop :=
  (∀ K M K' M' : A, P K → P M → P K' → P M' →
    ∀ (f : K' ⟶ K) (g : M ⟶ M'),
      F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ K' M' =
        coefficientBaseChangeHom SA SB F μ K M ≫
          HB.map (Prod.mkHom (F.map f).op (F.map g))) ∧
  (∀ K M : A, P K → P M → ∀ (T : A) (f : SA.tensor.obj (T, K) ⟶ M),
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f)) ∧
  (∀ K L M : A, P K → P L → P M →
    F.map (SA.composition K L M) ≫ coefficientBaseChangeHom SA SB F μ K M =
      μ.hom.app (HA.obj (op L, M), HA.obj (op K, L)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ L M)
          (coefficientBaseChangeHom SA SB F μ K L)) ≫
        SB.composition (F.obj K) (F.obj L) (F.obj M))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The specified coefficient/site isomorphism h, inverse to the scalar-restriction mate.
Source: blueprint final site-comparison sentence
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomSiteIso {n m : ℕ} (h : m ≤ n) :
    finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m ≅
      finiteHomNu l E X n ⋙ coefficientFiniteQuotientDerived l E X h :=
  (asIso (finiteHomSiteBeta l E X h)).symm

/-- Bounded constructibility in the existing positive-level etale category.
Source: blueprint constructible descent clause
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomEtaleConstructible (n : ℕ) : ObjectProperty (finiteHomEtale l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- Descent, reflection for every bounded constructible witness, and interval preservation.
Source: blueprint site-comparison sentence; proof step 1
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomDescent (n : ℕ) : Prop :=
  PreservesFiniteLimits (finiteHomNuOrdinary l E X n) ∧
  PreservesFiniteColimits (finiteHomNuOrdinary l E X n) ∧
  (∀ P : normalizedDVRDerived l E X n,
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P →
    ∃ P' : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X P' ∧
      Nonempty ((finiteHomNu l E X n).obj P' ≅ P)) ∧
  (∀ (P : normalizedDVRDerived l E X n) (P' : finiteHomEtale l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P →
    coefFiniteHomEtaleConstructible l E X n P' →
    Nonempty ((finiteHomNu l E X n).obj P' ≅ P) → ∀ a b : ℤ, a ≤ b →
      (Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b P' ↔
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) P a b)) ∧
  (∀ P' : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X P' →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
      ((finiteHomNu l E X n).obj P') ∧
    ∀ a b : ℤ, a ≤ b → Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b P' →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((finiteHomNu l E X n).obj P') a b)

/-- The actual canonical square, with the inverse h in the contravariant Hom input.
Source: blueprint final site-comparison sentence; proof step 6
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSquare {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ K M : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    IsIso (finiteHomSiteHom l E X n K M) ∧
    IsIso (finiteHomSiteHom l E X m
      ((finiteHomEtaleReduction l E X h).obj K)
      ((finiteHomEtaleReduction l E X h).obj M)) ∧
    (coefFiniteHomSiteIso l E X h).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
      (coefficientFiniteQuotientDerived l E X h).map (finiteHomSiteHom l E X n K M) ≫
      proEtaleFiniteHomCanonical l E X h
        ((finiteHomNu l E X n).obj K) ((finiteHomNu l E X n).obj M) =
    (finiteHomNu l E X m).map (etaleFiniteHomCanonical l E X h K M) ≫
      finiteHomSiteHom l E X m
        ((finiteHomEtaleReduction l E X h).obj K)
        ((finiteHomEtaleReduction l E X h).obj M) ≫
      (coefficientFiniteInternalHom l E X m).map
        (Prod.mkHom ((coefFiniteHomSiteIso l E X h).inv.app K).op
          ((coefFiniteHomSiteIso l E X h).hom.app M))

/-- Coherence for the actual scalar/site isomorphisms under successive quotients.
Source: blueprint final paragraph; proof step 4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomQuotientCoherence {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ (r : ℕ) (k : r ≤ m) (T : finiteHomEtale l E X n),
    (finiteHomNu l E X r).map ((finiteHomEtaleAssoc l E X h k).hom.app T) ≫
      (coefFiniteHomSiteIso l E X (k.trans h)).hom.app T =
    (coefFiniteHomSiteIso l E X k).hom.app ((finiteHomEtaleReduction l E X h).obj T) ≫
      (coefficientFiniteQuotientDerived l E X k).map
        ((coefFiniteHomSiteIso l E X h).hom.app T) ≫
      (finiteHomIntrinsicAssoc l E X h k).hom.app ((finiteHomNu l E X n).obj T)

/-- The fixed intrinsic scalar tensorator, projected from the published quotient calculus.
Source: blueprint scalar tensor convention; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomProTensor {n m : ℕ} (h : m ≤ n) :=
  (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h

/-- Symmetry of a specified tensor comparison, using the supplied canonical symmetries.
Source: blueprint monoidal clause; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSymmetry
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (βA : @SymmetricCategory A _ SA.monoidal)
    (βB : @SymmetricCategory B _ SB.monoidal)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q : A,
    F.map (βA.toBraidedCategory.braiding P Q).hom ≫ μ.hom.app (Q, P) =
      μ.hom.app (P, Q) ≫ (βB.toBraidedCategory.braiding (F.obj P) (F.obj Q)).hom

/-- The canonical identity-quotient scalar associator, adjoint to identity restriction.
Source: blueprint identity quotient convention
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomProUnit (n : ℕ) :
    coefficientFiniteQuotientDerived l E X (Nat.le_refl n) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (Nat.le_refl n)) (normalizedDVRResUnit l E X n)

/-- Transport of successive quotient and identity equations from the etale transposes
to the intrinsic transposes, on finite-Tor constructible pairs.
Source: blueprint final paragraph; proof step 7
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSuccessive {n m : ℕ} (h : m ≤ n) : Prop :=
  ((∀ (r : ℕ) (k : r ≤ m) (K M : finiteHomEtale l E X n),
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    (finiteHomEtaleAssoc l E X h k).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
      etaleFiniteHomCanonical l E X (k.trans h) K M =
    (finiteHomEtaleReduction l E X k).map
        (etaleFiniteHomCanonical l E X h K M) ≫
      etaleFiniteHomCanonical l E X k
        ((finiteHomEtaleReduction l E X h).obj K)
        ((finiteHomEtaleReduction l E X h).obj M) ≫
      (finiteHomEtaleInternalHom l E X r).map
        (Prod.mkHom ((finiteHomEtaleAssoc l E X h k).inv.app K).op
          ((finiteHomEtaleAssoc l E X h k).hom.app M))) ∧
  (∀ K M : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    etaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
      (finiteHomEtaleInternalHom l E X n).map
        (Prod.mkHom
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
            (finiteHomQuotient l E (Nat.le_refl n))
            (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
              (S := Padic.coefficientExtensionIdeal l E (n + 1))))).inv.app K).op
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
            (finiteHomQuotient l E (Nat.le_refl n))
            (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
              (S := Padic.coefficientExtensionIdeal l E (n + 1))))).hom.app M)) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
        (finiteHomQuotient l E (Nat.le_refl n))
        (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
          (S := Padic.coefficientExtensionIdeal l E (n + 1))))).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)))) →
  (∀ (r : ℕ) (k : r ≤ m) (K M : normalizedDVRDerived l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    (finiteHomIntrinsicAssoc l E X h k).hom.app
        ((coefficientFiniteInternalHom l E X n).obj (op K, M)) ≫
      proEtaleFiniteHomCanonical l E X (k.trans h) K M =
    (coefficientFiniteQuotientDerived l E X k).map
        (proEtaleFiniteHomCanonical l E X h K M) ≫
      proEtaleFiniteHomCanonical l E X k
        ((coefficientFiniteQuotientDerived l E X h).obj K)
        ((coefficientFiniteQuotientDerived l E X h).obj M) ≫
      (coefficientFiniteInternalHom l E X r).map
        (Prod.mkHom ((finiteHomIntrinsicAssoc l E X h k).inv.app K).op
          ((finiteHomIntrinsicAssoc l E X h k).hom.app M))) ∧
  (∀ K M : normalizedDVRDerived l E X n,
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    proEtaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom ((coefFiniteHomProUnit l E X n).inv.app K).op
          ((coefFiniteHomProUnit l E X n).hom.app M)) =
      (coefFiniteHomProUnit l E X n).hom.app
        ((coefficientFiniteInternalHom l E X n).obj (op K, M)))
```

## New

The entire block above occurs verbatim in
lean/Sheaf/Paper/CoefFiniteHomSiteDescentData.lean. It ends with the same namespace;
the original module replaces the block and its statement imports with:

```lean
public import Sheaf.Paper.CoefFiniteHomSiteDescentData
```

All declaration names and exact signatures remain identical. The original module's
three public theorems retain their signatures. The original one remaining hole is
reduced to three strictly smaller source obligations, each in its own new module.
The new public theorem coefficientHomTensorSquare is a proved right-adjoint form
of the monoidal-square evaluation calculation; its complete signature and proof
are in lean/Sheaf/Paper/CoefficientHomTensorSquare.lean.

## Users

| module | group holding it | effect |
|---|---|---|
| Comparator.Weil.Solution | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenRefinementAlphaPlusInclusion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.FourierTransform.FourierDeligneTransform | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicActualSystemsNormalized | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicCommonStageHomTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicCompletedProjectionShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicNormalizedPullbackRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicNormalizedPuritySystems | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicProjectionShiftCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicProjectionShiftData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicProperAdjunctionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicProperOrdinaryPushPreservation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensorComponents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityObjects | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPuritySourceFiniteness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPuritySourceNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicPurityTwistRestrictionComponents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicQbarConstructibleRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicTraceTensorShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicTraceTransposeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AdmissibleVerdierExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineCoefficientCounitMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineCounitMateUnitChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalDncNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalPowerCoefficient | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalPresentedBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalRawTransposePower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalRestrictedTransposes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalSectionCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineDiagonalTransposePower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineIntegrationExponentTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineLineComparisonNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineLineCompositeTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineLinePurityComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineLinePuritySource | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineLineStandingTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedCounitData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedCounitDescentComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedCounitSuccessor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedCounitZero | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedEvaluationContraction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedFirstLineCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedIntegrationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedIntegrationSuccessor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineOrderedTransposeCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceProductDomain | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpacePurityComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpacePurityComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpacePurityCompositionMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpacePurityCoordinateInvariance | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpacePurityOrderedBlocks | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceThomMap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceTraceFactorization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceTraceProductData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceZeroSectionConstructions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineTargetDiagonalDnc | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineTranslationTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AffineVectorTracePresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.AnchoredPureCurveCriterion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ArithmeticRoots | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BasicOperationCoefficientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BasicOperationReductionAndEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryFiniteEvaluationRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryFiniteSiteData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryFiniteTorDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryQFoundation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryQMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundaryQTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CartesianSectionAdjointMates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CartesianSectionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CartierClassAgreement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CartierRelativeKummerRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CartierSupportedComparisonSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CentredDiagonalSourcePasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDiagonalAssemblyData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDiagonalSourceMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDiagonalSourceSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDncNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDncSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDncVectorFactorData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartDncVectorFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartEpsilonPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartExceptionalCounitEquation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartExceptionalMateCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartIntegrationAdjoints | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartNormalIntegrationSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChartTargetOpenDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ChernFlagFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalFrontierExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenCounitAdjointComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenExceptionalActionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenSystemFiniteRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenSystemIntegralRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenSystemRealizationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClosedScalarDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ClosedSupportExceptionalMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CochainLocalizationTensorIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientFirstCompactSupportSiteSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientMapGeometricSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientPresentationIntegralMapIndependence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientTensorNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientTensorNormalizationFinite | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientTensorNormalizationQuotient | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientTensorNormalizationScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientTensorNormalizationTower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoefficientTensorNormalizationUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CohomologicalSmoothComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CommonStageWeilShriek | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportCondensedRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportCondensedRealizationSetup | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportLimitEquationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportPathReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportProjectionRightUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportRealizationCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportRealizationFactorization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportRealizationSquareExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportScalarGammaIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportStrictScalarCompositionPrelude | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportStrictScalarCompositionSupportRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactificationBProjectionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactificationBProjectionDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactificationBProjectionReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompactifiedTowerComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ComparedSmoothExchangeComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ComparisonImageClosedSectionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ComparisonPullbackRestrictionCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompleteProjectionDescentMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompleteProjectionMateDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompleteProjectionReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositeProjectionCoefficients | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositionIteratedMateExpansion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositionModelOrientationDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositionSingleMatePresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CompositionTensorMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedCompositorIntegralLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedCompositorIntegralRefinement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedCompositorRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedCompositorRealizationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedCompositorRealizationSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedCompositorSystemIndependence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedIntegralEndpoints | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedOpenCoefficientModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedOpenCounitComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedOpenCounitUnits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedOpenUnitComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedTateIntegralTower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CondensedTateIntegralTowerData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstantExtensionMixedDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCompositorData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleLeftCompositorCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleMateCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ConstructibleTensorComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateAdjunctionComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateCartierBoundarySign | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateLineAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateLineAugmentationRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateLineConjugateExponents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateLineCounitTensor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateProductPresentations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSectionArrows | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSectionProductRecursion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSectionProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSectionSiteTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSectionTensorTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateTowerNormalizationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoordinateZeroBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CoprojectionCompositionMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveClassicalPullbackExists | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveRestrictionFiltrationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.CurveRestrictionLocalPowers | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DerivedPoincarePairing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DerivedWeilOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineCounitRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineRankZeroActual | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineTraceMapAgreement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalAffineTraceSiteData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalCounitComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncAffineModel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncChartNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncEtaleBeta | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncEtaleDualizing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncEtaleFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncEtaleNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncEtaleNaturalityLocalInverse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalDncEtaleNaturalityTwist | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleAlphaSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleFactorization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleInverseDeformation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleLocalityUnitChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleNormalEndpoint | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleNormalTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleRestrictedDualizingData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleRhoUnitSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleSourceDualizing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleSourceEndpoint | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalEtaleSourceTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrdinaryChartLift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrdinaryOverlap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrdinaryRealizeRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrientationChartExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrientationCharts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrientationCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrientationRefinement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DiagonalOrientationRefinementData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DifferenceFirstInputRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DifferenceSecondInputRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DualBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DualizingCocycleSourceEtale | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DualizingObjectPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DualizingPrimitiveOpenRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.DualizingUnitComposite | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EtaleCompositeEComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EtaleMiddleTensorAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EtaleOrientationLocality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EtaleRhoMonoidalMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EtaleTensorSourceTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExactProperOpenProjectionMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalFiniteRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalFiniteSupportProperComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalProEtaleRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRealizationNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalReconstructionComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalReconstructionContext | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRefinementMates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRefinementSystemData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRefinementSystemRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingOperationsExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingScalarMates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingStageAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCoreData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCoreLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCorePostData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportCoreReconstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalRingTransportFamily | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExceptionalSiteRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ExchangeFunctoriality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionIntegralDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionIntegralModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionLimitEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionRationalComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionRationalDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionRationalModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionReductionDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionReductionLimits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionSourceNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionStrictLimits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldExtensionTowers | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemHeart | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientationSystemRigidity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldOrientedExchangeSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldProjectionRefinementSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldPuritySystemTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldPurityTransposeArrows | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FilteredCondensedCounitBijective | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteBundleSectionAdjointScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteClopenCommonExceptional | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCoefficientHomChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCoefficientTensorFactorization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDiagonalDncReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteEtaleDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteEtaleSectionIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteEtaleSpecializationCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFirstRootChart | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteForwardCompactifiedSwap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteForwardProductCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteForwardProductSymmetry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCompactComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCompactScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteFreeScalarProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGeometricPurityFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGeometricPurityMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteGeometricTensorExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteHorizontalShriekMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteIndHeartAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteIntrinsicProjectionCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteIntrinsicProjectionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteNormalizedOrientationScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePositiveChartFrameExt | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePositiveChartRecursion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePositiveRootChartPower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePositiveRootCharts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProCoefficientCounitTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProductCompactification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProductReductionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProductScalarPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionBinarySquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionBinaryTriangleSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionCompactificationSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionCompactificationTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionCompositionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionCompositionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionFromDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionOperationPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteProjectionTensorSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePublishedRootChartPower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePurityCounitSystem | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteRankZeroNormalIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionLineChartScalars | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionReassociation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionTensorFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionTensorPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionTensorSource | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteReductionThetaFactor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteRefinementAmbientNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteRefinementProjectionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteRootLinePowerTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteRootTensorPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteScalarTensorData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteScalarTensorSource | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSectionIntegratedScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSignedTwistProducts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSiteTensorProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothProQuotientTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSmoothZeroOrientationCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteSupportedReductionEquation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTargetChangeCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTateSourceMap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorComparisonEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorFixedComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorLineChartReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorPresentationReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorProductFrameExt | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorProductMap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorReductionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorShiftCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorShiftFirst | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorShiftSecond | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorSignedReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTorStability | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTripleProductDefinitions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTripleProductNormalForms | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteVectorIntegrationScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FiniteWeilIndPushExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FixProjectionCompactificationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FixedPairTruncationCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FlagLocalComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FlagPullbackInjective | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ForwardProductCoordinateTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FourierKernelConvolution | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FourierTraceFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FrobeniusCompactIntegralAmbientNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FrobeniusCompactIntegralNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.FrobeniusFixesUnitSection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeneralChartComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeneralHomComparisonCocycles | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeometricComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeometricOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GlobalIdentityNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.GlobalVerdierDualityData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.HigherTensorIdentityComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralAdjunctionBijection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralCoefficientModelComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralCompositorLimitRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralEquivarianceMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralEquivarianceNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralExceptionalInverseImage | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralGeometricComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralGeometricPurityRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralGeometricSupportRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralHomPresentationEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionFiniteEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionOpenFactorReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionProperFactorReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionReductionCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionReductionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionSupportEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionSupportFactorCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionSystemCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProjectionSystemEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProperProjectionSystemNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralProperSupportReductionIdentity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralPurityCounitReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralSemilinearGermSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralStageProjectionReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralSupportReductionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegralTowerProjectionMates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegrationAffineExponentTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegrationCoefficientProjectionNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegrationExponentTransposeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IntegrationProjectiveExponentSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.InverseContravariantBidual | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IteratedPurityScalarPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.IteratedTateSourceComposite | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LineCounitComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LineKummerFieldRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LineZeroClassEtaleRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LineZeroClassExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LisseExtensionInertia | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LocalizedTopChern | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.LocallyFiniteCompactSupportStageAction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCompactSupportExchangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupCoefficientChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupCoefficientData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupCoefficientSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupFieldCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupFieldNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupFieldOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupOperationComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupRingedNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupTensorClosure | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupTensorComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupTensorElementary | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.MixedCupTensorNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ModelChartOrientationAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ModelOrientationChartDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ModelOrientationSourceNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ModelOrientationTateDetection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeAdicCompactSupportSums | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportFiniteComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportGeometry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportIntegralLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompactSupportScalarMateInvertible | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompletedCoefficientChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompletedCoefficientChangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompletedCoefficientChangePresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeCompletedCoefficientChangeSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeDirectImageSections | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeProperCoefficientOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeProperProjectionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeProperProjectionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeProperScalarMateBoundedBelow | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeProperTensorComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilComparisonStructure | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilFreeCoproduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilHeartProperties | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilInductionComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilInductionSummands | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilProperNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalModelSectionOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalSectionIntegrationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedEtaleComparisonComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedEtaleRestrictionComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedFiniteFibreModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedIntegralTraceData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedTateTensorTower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedTateTensorTowerCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedTateTensorTowerProperties | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.NormalizedTateTensorTowerZero | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OmegaProperCoefficientProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OmegaProperCoefficientProjectionHomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OperationCoefficientActionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OperationScalarTransportNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedAffineComparisonNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedAffineLineTransposeNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedAffineTransposeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedAffineTransposeProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedAffineTransposeSuccessor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedIntegrationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedLineLevelBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedTateTowerCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrderedTowerOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientationGroundFieldRetagging | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientationLocalResidue | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientationScalarPropagation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientationScalarTowerTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.OrientedPerfectDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.P1KummerTraceSiteTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PerfectDualPairAndTateStability | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PfReductionProperOpenIdentities | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PfRefinementCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PodCtfAdjunctions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PodCtfPairingMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PodHomChainCounitFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PodHomChainCtfDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PodHomChainUncurriedTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PoincareDualityConventions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointIdentityExchangeRecipe | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointWeilPairingCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointWeilPairingRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointWeilTensorRepresentatives | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PointWeilTransportUnitShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleAffineLineCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleFrameIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleOrderedIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleProjectionIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductCompositionCoordinateComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductExchangeCoordinateDefinitions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductHorizontalExchangeFactorization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductOpenAdjunctionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductOpenCounitNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductOpenSupportNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductOpenTensorProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProductOpenTensorProjectionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFactorCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFiniteReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionFormulaCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionIdentityAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionIdentityProperCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionIdentityTensorUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionPurityCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionReductionPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionScalarSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionTensorIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionUnitIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectionUnitPresentationNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProperProductCounitTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ProperWeilIterateGermFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PulledOrderedLineSingle | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurAdicReconstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurIntegralRepresentingPair | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurIntegralRepresentingPairData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurIntegralSupportComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurIntegralSupportComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurSupportPresentationAlpha | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineLineOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityAffineLineSupportStalk | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityChernClasses | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityCompactSupportTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityCompositionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityConstantFamilyBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityCoprojection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityFiniteReductionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityGysinStructure | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityKappaStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityOrientationDatum | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityPullbackLevelBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityPullbackReductionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityRankZeroFamilyReadings | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionBaseComparisonLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionConstantTrivialization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionEtaleRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionFibreSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionNormalizedSpecialization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionRestrictionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityTateDatum | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityTensorMapNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityTowerReductionComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityTwistCancellation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityWitnessedMateNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.QuotientInverseOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RankZeroBundleSectionCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalStalkExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalTensorSymmetry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedBrownMateLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedPairRefinementData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedRefinementCommon | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ReducedFrontierMixedGluing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RegularImmersionPurityComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RelativeKunneth | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RelativeProductInputDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RelativeSupportCoordinateModel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RestrictedAffineDiagonalDncTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RestrictedAffineDiagonalDncVectorCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RestrictedAffineDiagonalSectionTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RestrictedAffineDiagonalVectorIntegration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RetaggingCoordinateOrientations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RingCanonicalScalarInvertibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.RingEndpointScalarRestrictions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SbcDatumExchangeComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ScalarExchangeConstituents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ScalarHomPresentationEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SectionDncIntegrationSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SectionEtaleOpenCancellation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SemilinearExchangeDescentData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SemilinearExchangeReindexing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SemilinearExchangeReindexingData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SemilinearGermIterationDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfBcCompletedMateDomain | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfBidualityClass | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfCompletedExchangeTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfFieldMateDomain | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfIntegralLocalizationConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfLocalizationAllStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageCoefficientDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageFieldOperationRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageIntegralSupportTowerNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfPositiveFiniteLocalizationConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SfRecollementReductionBoundary | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SitePerfectCoefficientDual | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothClopenComponentInverse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothClopenResidueLine | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOrientationPuritySquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOrientationStageExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOrientationTransportSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityCompositionFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityMap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityTensorUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothPurityTowerGammaData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SmoothTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SpecifiedTowerAdjunctionCharts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictProperRestrictionComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictScalarTowerAssociator | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictTateTensorTowerLift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictTateTensorTowerLiftCocycle | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictTateTensorTowerLiftData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictTateTensorTowerLiftEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.StrictTateTensorTowerLiftPre | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SupportedCartierDerivedPullback | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SupportedProjectiveChern | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SupportedProjectiveChernComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemClopenMateIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemCompositorRefinementSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteCompositorCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteEvaluationCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteRefinementMateCanonical | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteRefinementMateCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteRefinementMateLhsNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteRefinementMateRhsCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemIdentityOpenEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemProperIdentityOpenProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemRefinementFiniteCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemScalarBasisDistributivity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemScalarProjectionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemScalarProjectionIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemScalarRefinementRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemScalarTensorConstituents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemTensorPresentationCoreExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemTensorPresentationData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemTensorPresentationIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.SystemTensorSemilinearRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorBalancedTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorFiniteTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorFiniteTransitionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorIsIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorLocalIsIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorMap | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorOne | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorStep | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorGeneratorZero | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorNormalizedSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorNormalizedSquarePair | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorPairFiniteSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTensorQuotientBalancing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorAdjunctionExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorHomExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorMapPresentationIndependent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorMateBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorMateInvertibleInput | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TensorTransposeTowerNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerFactorOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerFactorTensor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerGeometricPurityAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerGeometricPurityData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerGeometricPurityMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerIsomorphismPullback | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerMuEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerNormalizationPreservation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerOrientationEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerOrientationWordNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerPurityAdjointTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerPurityPresentationRetagging | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerPurityRealizedData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerPurityRealizedNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerSemilinearPurityFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTateSplitNormalized | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTensorAdjointDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTensorPresentationRetagging | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTensorTransposeWords | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTracePurityComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTracePurityComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TowerTraceScalarCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TraceCorrespondences | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportCondensedStageRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportIntegralBaseChangeRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportIntegralChartRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportIntegralCompositionRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportIntegralCounitData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportIntegralCounitRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TransportIntegralStageConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionSign | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackCofinalModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackLineMembership | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackReductionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackReductionTower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackTateReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackTowerBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomain | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.UniformTowerTensorClosure | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorBundleThom | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorBundleThomClass | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorBundleThomMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorBundleThomProduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorIntegrationChartComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorIntegrationChartTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorIntegrationIdentityAdjunct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorIntegrationSiteComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorModelChartDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorNormalizedTraceCartesian | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorTensorOrdinaryNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorTensorProjectionComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorTensorSiteEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VectorZeroSectionIntegrationBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierCompositionMateNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierHomChainComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierHomChainCompositionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierIdentityProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierPairingThreeTransposes | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilChosenExchangeConstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilChosenTransposeNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilFourierInversion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilPullbackFibreReturn | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilPurityEquivarianceData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlFrameworkOpenExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlShriekComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceExponent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientationSupport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingScalarUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingScalarUnitFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingSiteScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.ReductionOrientation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientExactClopenData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientSystemBetaLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientSystemClopenLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CanonicalShiftSynchronization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CartesianCandidateSiteSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CartesianTowerRestriction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionBetaReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionDeltaSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomMapInvertibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityE | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityL | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionPureTensor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUInvertibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReconstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionVInvertibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteScalarCocycles | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarRationalScalarCocycles | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierBiduality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierBidualityDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierCoreEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierDualInclusion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationRepresentatives | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierExactness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationScalar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationStage | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFunctor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierScalars | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierTensorDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierTensorInclusion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefScalarReductionExchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompositionProjectionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.CompositionProjectionMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteExceptionalData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicTensorRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteScalarMateData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.GeneratorReductionStatement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralBasicGeneratorSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCanonicalRealizationSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingCoefficientHomTowerLimit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingMappingTower | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalLimitConstructible | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExpressionCanonicalEquations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExpressionCanonicalSupport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExpressionRecursionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralExpressionTransposeIsIso | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOpenRealizationNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryExpressionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralRefinementTransposeRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralSupportCounitProjection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralSupportRealizationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdierModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.KappaGeometricComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.KappaMixedCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenAdjunctionShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenBaseChangeReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenSupportStepBounds | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OpenTensorReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OrdinaryAmbientAlphaPasting | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OrdinaryAmbientAlphaUnits | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OrdinaryBasicSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementComparisons | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementInputs | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenInterchangeFromLambda | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportOpen | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportPull | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportPush | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaCompletionTransportTensor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaFourFactorSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaOrdinarySquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaReductionSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenLambdaReductionSquareUnbounded | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.PublishedSystemAmbientCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.PublishedSystemTensorComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalDualFormulaAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalDualFormulaScalarCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalDualizingIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalHomAdjunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalHomIdentifications | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalHomScalarCounitNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalHomScalarEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalHomScalarEvaluationCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalOperationsData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdier | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierComparisonBiduality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierComparisonEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierComparisonEvaluationIntegral | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierComparisonNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierCompletion | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierCompositionEquation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierCompositionNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierDatum | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierDatumFromIntegral | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierDatumNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierEvaluationDetection | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierIntegralCocycle | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierIntegralCompNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierLocalizedCore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierLocalizedEvaluation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierLocalizedExact | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierPairingCalculus | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierScalarInterchange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierSignedKFlat | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RationalVerdierUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RealizationTreeShiftData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RefinementProjectionCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RefinementProjectionLocalTensor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RefinementProjectionProperComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.RefinementProjectionWords | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionOpenCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionOpenUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionPullComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionPullPushCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionPullPushUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionPushComposition | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionTensorAssociator | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionTensorLeftUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionTensorRightUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.StructuralReductionWordSubstitution | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SupportedWeilMateLift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemProperOpenSupport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.SystemTotalEnrichedTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TensorExchangePresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TensorHomTranspositionData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.ThreeCellCompositor | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.VerdierExchangeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SixFunctors.WeilChosenDualityHom | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Targets.PoincareUncurry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.Targets.SmoothPurityQbar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.CoefficientCohomologyComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.DualRealizationComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalHomTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.SmoothCoefficientVanishing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.SmoothDualizingCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.SmoothDualizingConcentration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.SmoothDualizingVanishing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.StructuralBidualInvertible | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.StructuralDualizingIdentification | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| TargetsCheck | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.PoincareDuality.Poincare | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.SmoothPurity.Defs | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.Statement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.BorelMoore | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.CoefficientMorphism | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.Correspondence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.CorrespondencePair | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.CurvePieces | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.Dualizing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.GenericQuotient | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.HomologyUnit | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.KunnethVerdier | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.LefschetzVerdier | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.LocalTerm | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.LocalTermLocality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.Main | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.PointNormalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.Product | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ProperCompatibility | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ProperCurve | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ProperPushforward | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.PullbackFamily | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.Statement | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.SupportedPairing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.TraceClass | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.TraceClassCorrespondenceClass | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.TraceClassCorrespondenceClassApply | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.TraceClassCorrespondenceClassNaturality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.WeilBaseChange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.TraceFormula.WeilTrace | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRange | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.Curve | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.Karoubian | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.KaroubianPointer | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.LFunction | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.VerdierDual | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.Examples | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.Rationality | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.Weights | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | no adaptation; holder not queried | Verbatim declarations and public dependencies by reexport; unchanged. |

The data extraction preserves every existing declaration body byte for byte and
publicly reexports every original public import, so indirect consumers have the
same interfaces. The delivery tool additionally computes related consumers and
compiles them. No other existing Lean module is adapted.

## Status

landed 20261028T020341-L-2498181 2026-10-28 (merge of deliver/F1/Sheaf.Paper.CoefFiniteHomSiteDescent)
