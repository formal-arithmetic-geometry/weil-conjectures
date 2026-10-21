# AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre (module location)

## Reason

The geometric subresults use the existing fibre, lattice and chart definitions. Extracting
those definitions avoids an import cycle when the original theorem imports its subresults.
Every existing declaration, binder, body, attribute and instance is retained verbatim. The
original module publicly re-exports the data module, so users see the same declarations.
No target statement or definition meaning changes.

## Old

The following public declarations were defined in
`Sheaf.Paper.AdicNormalizedFibreExactness`, following these imports:

```lean
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
```

The complete unchanged declaration block is:

```lean
/-- The continuous coefficient map, defined by adjunction from precomposition of functions.
Source: BS 6.8.1--6.8.2 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def coefficient {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicTowerInverseImage f).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) f

/-- Constant field sections at the final object of the geometric point.
Source: BS 6.8.1 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def pointConstants (κ : Type u) [Field κ] : E →+*
    (rationalCoefficientSheaf l (Spec (.of κ)) E).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of κ))))) where
  toFun a := (scalarSections l E (Spec (.of κ)) a).val
    (op (ProEt.mk (𝟙 (Spec (.of κ)))))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Intrinsic fibre: module inverse image, final-object sections, and constant E-action.
No stratification, lattice, or exchange of a stalk with a limit enters this construction.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def ambient {X : Scheme.{u}} (κ : Type u) [Field κ] (x : Spec (.of κ) ⟶ X) :
    pbcModules X (rationalCoefficientSheaf l X E) ⥤ ModuleCat.{u + 1} E :=
  modulePull x (coefficient l E x) ⋙
    SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 (Spec (.of κ))))) ⋙
      ModuleCat.restrictScalars (pointConstants l E κ)

/-- The localized heart, with its already recorded raw category and standard t-structure.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
abbrev Heart (X : Base.{u} l) := (localizedT l E X).heart.FullSubcategory

/-- Degree-zero sheaf realization of the raw rational heart.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def realize (X : Base.{u} l) (a : At l E X) :
    Heart l E X ⥤ pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E) :=
  (localizedT l E X).heart.ι ⋙ a.J ⋙ DerivedCategory.homologyFunctor _ 0

/-- The sheaf realization inherits additivity from the inclusion, J, and H⁰.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
instance realizeAdditive (X : Base.{u} l) (a : At l E X) :
    (realize l E X a).Additive := by
  unfold realize
  infer_instance

/-- The desired fibre on the heart, obtained from the intrinsic sheaf fibre.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def omega (X : Base.{u} l) (a : At l E X) (κ : Type u) [Field κ]
    (x : Spec (.of κ) ⟶ X.scheme) : Heart l E X ⥤ ModuleCat.{u + 1} E :=
  realize l E X a ⋙ ambient l E κ x

/-- Multiplication by a constant integer on an integral continuous module.
Source: BS 6.8.2 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def integerScalar (T : Scheme.{u})
    (M : pbcModules T (integralCoefficientSheaf l T E))
    (a : Padic.coefficientExtensionIntegers l E) : M ⟶ M := by
  letI := coefficientExtensionNormedField l E
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro U
    exact ModuleCat.ofHom
      { toFun := fun m ↦ ContinuousMap.const U.unop.left (ULift.up a) • m
        map_add' := smul_add _
        map_smul' := fun r m ↦ by
          change _ • (r • m) = r • (_ • m)
          rw [smul_smul, smul_smul, mul_comm] }
  · intro U V f
    ext m
    exact (M.val.map_smul f (ContinuousMap.const U.unop.left (ULift.up a)) m).symm

/-- Forget only the integral coefficient action.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
abbrev forgetIntegral (T : Scheme.{u}) :=
  SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj (integralCoefficientSheaf l T E))

/-- The normalized etale system on the pro-etale site, with its underlying additive groups.
Source: BS 5.1.5 and 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def proSystem (T : Scheme.{u}) (N : AdicIntegralDiagramOfUniverses l E T) :=
  N ⋙ sheafCompose _
    (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat) ⋙
      supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T

/-- A local lattice and its normalized finite free etale reductions. The limit and quotient
universal properties retain the actual lattice; scalar compatibility fixes its integral action.
This is local chart data, and is never assumed to exist globally on a lisse stratum.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Lattice (T : Scheme.{u}) where
  integral : pbcModules T (integralCoefficientSheaf l T E)
  locallyFree : integral.IsFiniteLocallyFree
  system : AdicIntegralDiagramOfUniverses l E T
  lisse : IsLisseIntegralDiagramOfUniverses l E T system
  finiteFree : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ T) (n : ℕ), ∃ r : ℕ, Nonempty
        ((((pointSmallEtale x).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          (system.obj (op n))) ≃ₗ[Padic.coefficientExtensionIntegers l E]
            (Fin r → Padic.coefficientExtensionRing l E (n + 1)))
  reduction : (Functor.const ℕᵒᵖ).obj ((forgetIntegral l E T).obj integral) ⟶
    proSystem l E T system
  complete : IsLimit (Cone.mk _ reduction)
  quotient : ∀ n : ℕ, ∃ h :
      (forgetIntegral l E T).map (integerScalar l E T integral
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) ≫ reduction.app (op n) = 0,
    Nonempty (IsColimit (CokernelCofork.ofπ (reduction.app (op n)) h))
  scalar : ∀ (a : Padic.coefficientExtensionIntegers l E) (n : ℕ),
    (forgetIntegral l E T).map (integerScalar l E T integral a) ≫ reduction.app (op n) =
      reduction.app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T).map
          ((sheafCompose _
            (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
              AddCommGrpCat)).map (a • 𝟙 (system.obj (op n))))

/-- Rationalize this actual lattice by the actual continuous coefficient inclusion.
Source: BS 6.8.4(4) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Lattice.rational {T : Scheme.{u}} (N : Lattice l E T) :=
  (pbcExtend (integralRationalCoefficientMap l E T)).obj N.integral

/-- The integral fibre is the recorded inverse limit of etale stalks.
Source: Weil II (1.1.1)b), BS 6.8.4(1)
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Lattice.fiber {T : Scheme.{u}} (N : Lattice l E T)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ T) :=
  adicIntegralFiberOfUniverses l E T N.system κ x

/-- Its rational fibre uses balanced scalar extension, so it is E tensor_A lim N_n,x.
Source: Weil II (1.1.1)c), BS 6.8.4(4)
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Lattice.rationalFiber {T : Scheme.{u}} (N : Lattice l E T)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ T) :=
  (ModuleCat.extendScalars (Padic.coefficientExtensionIntegers l E).subtype).obj
    (N.fiber l E κ x)

/-- A geometric chart on a stratum; the affine chart is etale, rather than pro-etale.
Source: BS 6.8.4(6) and 6.8.6 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Chart (X : Base.{u} l) where
  strata : FiniteLocallyClosedStratification X.scheme
  index : Fin strata.n
  scheme : Scheme.{u}
  [affine : IsAffine scheme]
  etale : scheme ⟶ strata.domain index
  [isEtale : Etale etale]

attribute [instance] Chart.affine Chart.isEtale

/-- The chart's actual map to X.
Source: BS 6.8.6 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Chart.map {X : Base.{u} l} (C : Chart l X) := C.etale ≫ C.strata.immersion C.index

/-- An adapted stratification means precisely lissity on every stratum.
Source: BS 6.8.6 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Chart.Adapted {X : Base.{u} l} (a : At l E X) (C : Chart l X)
    (F : Heart l E X) : Prop :=
  ∀ i : Fin C.strata.n,
    ((modulePull (C.strata.immersion i) (coefficient l E (C.strata.immersion i))).obj
      ((realize l E X a).obj F)).IsFiniteLocallyFree

/-- Restriction to the chart uses the canonical continuous coefficient map.
Source: BS 6.8.2 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Chart.restrict {X : Base.{u} l} (a : At l E X) (C : Chart l X) :=
  realize l E X a ⋙ modulePull C.map (coefficient l E C.map)

/-- A system map induces its actual inverse-limit stalk map followed by balanced localization.
Source: BS 6.8.4(1),(4) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def rationalLimitMap {T : Scheme.{u}} (N M : Lattice l E T)
    (uN : N.system ⟶ M.system) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ T) : N.rationalFiber l E κ x ⟶ M.rationalFiber l E κ x :=
  (ModuleCat.extendScalars (Padic.coefficientExtensionIntegers l E).subtype).map
    (limMap (Functor.whiskerRight uN ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))))

/-- An integral map represents a specified compatible map of normalized systems.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Represents {T : Scheme.{u}} (N M : Lattice l E T)
    (f : N.integral ⟶ M.integral) (uN : N.system ⟶ M.system) : Prop :=
  ∀ n : ℕ, (forgetIntegral l E T).map f ≫ M.reduction.app (op n) =
    N.reduction.app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T).map
        ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
            AddCommGrpCat)).map (uN.app (op n)))

/-- A finite-dimensional E-linear fibre, naturally identified with the intrinsic construction.
The exact structure is measured after the specified realization into all continuous modules.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Point (X : Base.{u} l) (a : At l E X) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme) where
  functor : Heart l E X ⥤ ModuleCat.{u + 1} E
  [additive : functor.Additive]
  [linear : functor.Linear E]
  intrinsic : functor ≅ omega l E X a κ x
  finite : ∀ F, FiniteDimensional E (functor.obj F)
  exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).ShortExact → (S.map functor).ShortExact

attribute [instance] Point.additive Point.linear

/-- All normalized local lattice comparisons and joint detection assertions, for one E-stage.
The chart and presentation are universally quantified, so the same fibre is used for every
choice of stratification, etale chart, lattice and fractional representative.
Source: BS 6.8.4(1),(4),(6), 6.8.5 and 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Assertions (X : Base.{u} l) (a : At l E X) where
  point : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    Point l E X a κ x
  local_chart : ∀ (F : Heart l E X) (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme),
    ∃ (C : Chart l X) (t : Spec (.of κ) ⟶ C.scheme) (N : Lattice l E C.scheme),
      t ≫ C.map = x ∧ C.Adapted l E a F ∧
        Nonempty ((C.restrict l E a).obj F ≅ N.rational l E)
  integral_finite_free : ∀ (C : Chart l X) (N : Lattice l E C.scheme)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    Module.Finite (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ t) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ t)
  normalization : ∀ (C : Chart l X) (F : Heart l E X) (_hF : C.Adapted l E a F)
      (N : Lattice l E C.scheme) (_φ : (C.restrict l E a).obj F ≅ N.rational l E)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    (point κ (t ≫ C.map)).functor.obj F ≅ N.rationalFiber l E κ t
  fractions : ∀ (C : Chart l X) (F G : Heart l E X)
      (hF : C.Adapted l E a F) (hG : C.Adapted l E a G)
      (N M : Lattice l E C.scheme)
      (φ : (C.restrict l E a).obj F ≅ N.rational l E)
      (ψ : (C.restrict l E a).obj G ≅ M.rational l E)
      (f : F ⟶ G) (u : N.integral ⟶ M.integral) (uN : N.system ⟶ M.system)
      (_hu : Represents l E N M u uN) (b : ℕ)
      (_hf : (C.restrict l E a).map f ≫ ψ.hom = φ.hom ≫
        (((Padic.coefficientExtensionUniformizer l E : E) ^ b)⁻¹ •
          (pbcExtend (integralRationalCoefficientMap l E C.scheme)).map u))
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    (point κ (t ≫ C.map)).functor.map f ≫ (normalization C G hG M ψ κ t).hom =
      (normalization C F hF N φ κ t).hom ≫
        (((Padic.coefficientExtensionUniformizer l E : E) ^ b)⁻¹ •
          rationalLimitMap l E N M uN κ t)
  detects_zero : ∀ F : Heart l E X,
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsZero ((point κ x).functor.obj F)) → IsZero F
  detects_iso : ∀ (F G : Heart l E X) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsIso ((point κ x).functor.map f)) → IsIso f
  detects_zero_map : ∀ (F G : Heart l E X) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      (point κ x).functor.map f = 0) → f = 0
  detects_exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).Exact ↔
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        (S.map (point κ x).functor).Exact
  detects_short_exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).ShortExact ↔
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        (S.map (point κ x).functor).ShortExact
```

## New

The declaration block above is verbatim in `Sheaf.Paper.AdicNormalizedFibreData` with the
same public imports, namespace, universes and options. The original module instead has:

```lean
public import Sheaf.Paper.AdicNormalizedFibreData
```

The data module additionally defines `LocalLattices`, the local chart/normalization/fraction
part of `Assertions` using the intrinsic functor directly, and `GeometricPoint`, bundling
an algebraically closed field and its scheme map. Neither asserts existence or changes any
existing definition. Their full declarations are in the new module and their node is
`def-per-adic-normalized-fibre-data`.

## Users

`tools/downstream.py Sheaf.Paper.AdicNormalizedFibreExactness` reports zero downstream
Lean modules. `--uses Assertions` reports only the original item. DAG parents still use
the original theorem; none is withdrawn or bypassed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicNormalizedFibreExactness | B9 | Public re-export; theorem statement unchanged |
| Sheaf.Paper.AdicNormalizedFibreData | B9, new | Verbatim declarations and two record types |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | B9, new | Uses existing definitions |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | B9, new | Uses existing definitions |
| Sheaf.Paper.NormalizedLatticeFiniteFree | B9, new | Proves finite freeness and dimension |
| Sheaf.Paper.NormalizedHeartRealization | B9, new | Proves faithful exact realization |

## Status

landed 20261021T192917-L-762138 2026-10-21 (merge of deliver/B9/Sheaf.Paper.AdicNormalizedFibreExactness)
