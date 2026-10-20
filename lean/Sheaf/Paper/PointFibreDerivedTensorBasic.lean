/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace

/-! # Derived tensor and the geometric-point fibre

Source: Stacks Project, Tag 07A4, `lemma-pullback-tensor-product`;
(blueprint: def-sf-point-fibre-tensor-system).

The definitions record genuine strong symmetric monoidal data for all four
coefficient stages, with prescribed tensor bifunctors and coefficient objects.
Canonical representative normalizations and coefficient-change diagrams are
specified by the other helper definitions; this data alone asserts no canonicity.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- The coefficient prime is invertible on the spectrum of the geometric point field.
Source: blueprint def-weil-finite-field-fiber and the coefficient convention l ≠ p
(blueprint: def-sf-point-fibre-tensor-system).
Proof: the specified cardinality gives characteristic D.p for k₀, hence for k
and its residue fields; a distinct prime is nonzero and thus invertible. -/
theorem finiteFieldSpecCoefficientPrimeInvertible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    Nonempty (∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w)) := by
  sorry

/-! The following named functors keep the four displayed stage constructions
opaque while retaining their definitions. This avoids repeatedly unfolding
the large coefficient-category terms while elaborating the theorem below. -/

/-- Finite-stage fibre functor, exactly the finite clause. Source: Stacks Tag 07A4
(blueprint: def-sf-point-fibre-tensor-system). -/
noncomputable def finitePointFibreTensorSource
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :=
  (ObjectProperty.ι (finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))) ⋙
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory)

/-- Finite-stage derived tensor bifunctor. Source: Stacks Tag 07A4 (blueprint:
def-sf-point-fibre-tensor-system). -/
noncomputable def finitePointFibreTensorBifunctor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :=
  (((ObjectProperty.ι (finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))).prod
      (ObjectProperty.ι (finiteTorConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))))) ⋙
    finiteIntrinsicDerivedTensor l E (Spec (.of D.k)) n)

/-- Integral completed derived tensor bifunctor. Source: Stacks Tag 07A4 (blueprint:
def-sf-point-fibre-tensor-system). -/
noncomputable def integralPointFibreTensorBifunctor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :=
  letI : ∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  (((ObjectProperty.lift (sfIntegralConstructible l E (Spec (.of D.k)))
      (ObjectProperty.ι (finiteTorConstructibleIntegral l E (Spec (.of D.k))))
      (fun K : (finiteTorConstructibleIntegral l E (Spec (.of D.k))).FullSubcategory ↦
        K.property.1)).prod
    (ObjectProperty.lift (sfIntegralConstructible l E (Spec (.of D.k)))
      (ObjectProperty.ι (finiteTorConstructibleIntegral l E (Spec (.of D.k))))
      (fun K : (finiteTorConstructibleIntegral l E (Spec (.of D.k))).FullSubcategory ↦
        K.property.1)) ⋙
    constructibleIntegralTensor l E (Spec (.of D.k))) ⋙
    ObjectProperty.ι (sfIntegralConstructible l E (Spec (.of D.k))))

/-- Rational derived tensor bifunctor. Source: Stacks Tag 07A4 (blueprint:
def-sf-point-fibre-tensor-system). -/
noncomputable def rationalPointFibreTensorBifunctor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :=
  letI : ∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  rationalDerivedTensor l E (Spec (.of D.k))

/-- A strong symmetric monoidal fibre functor on the specified tensor subcategory.
The source tensor and coefficient unit are fixed by `tensor_eq` and `unit_eq`.
`strong` includes the actual associator and both unitor diagrams, and `symmetry`
is the braiding square. Canonical representative normalizations are imposed below;
this structure alone does not claim canonicity.
Source: Stacks 07A4 and the tensor constraints in the node's final sentence
(blueprint: def-sf-point-fibre-tensor-system). -/
structure PointFibreDerivedTensorComparisonData
    {C : Type c} {A : Type e} {B : Type d}
    [Category.{hc} C] [Category.{he} A] [Category.{hd} B]
    (I : C ⥤ A) (F : A ⥤ B) (T : C × C ⥤ A) (unit : A)
    [MonoidalCategory B] (β : BraidedCategory B) where
  /-- The derived tensor constraints on the source subcategory. -/
  monoidal : MonoidalCategory C
  /-- Its tensor is exactly the recorded derived tensor after inclusion. -/
  tensor_eq : @MonoidalCategory.tensor C _ monoidal ⋙ I = T
  /-- Its unit is the coefficient object specified by the coefficient construction. -/
  unit_eq : I.obj monoidal.tensorUnit = unit
  /-- Strong monoidality includes naturality, associativity and both unit diagrams. -/
  strong : @Functor.Monoidal C _ monoidal B _ _ (I ⋙ F)
  /-- The source has symmetric derived tensor, including the hexagon and involution. -/
  symmetric : @SymmetricCategory C _ monoidal
  /-- The comparison intertwines the actual source and target braidings. -/
  symmetry : ∀ X Y : C,
    (@Functor.LaxMonoidal.μ C _ monoidal B _ _ (I ⋙ F) strong.toLaxMonoidal X Y) ≫
        (I ⋙ F).map (symmetric.toBraidedCategory.braiding X Y).hom =
      (β.braiding ((I ⋙ F).obj X) ((I ⋙ F).obj Y)).hom ≫
        (@Functor.LaxMonoidal.μ C _ monoidal B _ _ (I ⋙ F) strong.toLaxMonoidal Y X)

/-- The tensor comparison extracted from the strong structure, in the node's direction.
Source: Stacks 07A4 (blueprint: def-sf-point-fibre-tensor-system). -/
def PointFibreDerivedTensorComparisonData.tensorIso
    {C : Type c} {A : Type e} {B : Type d}
    [Category.{hc} C] [Category.{he} A] [Category.{hd} B]
    [MonoidalCategory B] {β : BraidedCategory B}
    {I : C ⥤ A} {F : A ⥤ B} {T : C × C ⥤ A} {unit : A}
    (S : PointFibreDerivedTensorComparisonData I F T unit β) (X Y : C) :
    F.obj (T.obj (X, Y)) ≅ F.obj (I.obj X) ⊗ F.obj (I.obj Y) :=
  F.mapIso (eqToIso (congrArg (fun G : C × C ⥤ A ↦ G.obj (X, Y)) S.tensor_eq).symm) ≪≫
    (@Functor.Monoidal.μIso C _ S.monoidal B _ _ (I ⋙ F) S.strong X Y).symm

/-- The coefficient-unit comparison, not the inverse identity of a tensor component.
Source: Stacks 07A4 (blueprint: def-sf-point-fibre-tensor-system). -/
def PointFibreDerivedTensorComparisonData.unitIso
    {C : Type c} {A : Type e} {B : Type d}
    [Category.{hc} C] [Category.{he} A] [Category.{hd} B]
    [MonoidalCategory B] {β : BraidedCategory B}
    {I : C ⥤ A} {F : A ⥤ B} {T : C × C ⥤ A} {unit : A}
    (S : PointFibreDerivedTensorComparisonData I F T unit β) : F.obj unit ≅ 𝟙_ B :=
  F.mapIso (eqToIso S.unit_eq.symm) ≪≫
    (@Functor.Monoidal.εIso C _ S.monoidal B _ _ (I ⋙ F) S.strong).symm

/-- The standard Koszul braiding on coefficient-module derived categories.
Source: Stacks 06YN, signed total tensor
(blueprint: def-sf-point-fibre-tensor-system). -/
@[instance_reducible] def pointModuleDerivedBraiding (R : Type v) [CommRing R]
    [HasDerivedCategory.{v} (ModuleCat.{v} R)] :
    BraidedCategory (DerivedCategory (ModuleCat.{v} R)) :=
  DerivedCategory.perfectTraceCanonicalBraiding (ModuleCat.{v} R)

/-- The actual integral finite-Tor inclusion into the constructible category.
Source: blueprint integral coefficient construction
(blueprint: def-sf-point-fibre-tensor-system). -/
def pointIntegralCtfToConstructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  ObjectProperty.lift (sfIntegralConstructible l E (Spec (.of D.k)))
    (finiteTorConstructibleIntegral l E (Spec (.of D.k))).ι
    (fun K ↦ K.property.1)

/-- The finite-stage strong tensor comparison, with the prescribed ambient unit.
Source: Stacks 07A4 (blueprint: def-sf-point-fibre-tensor-system). -/
def PointFiniteTensorData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  PointFibreDerivedTensorComparisonData
    (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Spec (.of D.k))).ι
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
    (finitePointFibreTensorBifunctor D l E n)
    (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit
    (pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The integral coefficient object in degree zero.
Source: blueprint completed integral coefficients
(blueprint: def-sf-point-fibre-tensor-system). -/
def pointIntegralTensorUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).obj
    (SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))

/-- The integral strong tensor comparison for the completed tensor product.
Source: blueprint integral clause (blueprint: def-sf-point-fibre-tensor-system). -/
def PointIntegralTensorData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  PointFibreDerivedTensorComparisonData
    (finiteTorConstructibleIntegral l E (Spec (.of D.k))).ι
    (pointFibreIntegralAmbient D l E) (integralPointFibreTensorBifunctor D l hl E)
    (pointIntegralTensorUnit D l E)
    (pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))

/-- The rational unit is the localization of the integral coefficient unit.
Source: blueprint rational coefficient construction
(blueprint: def-sf-point-fibre-tensor-system). -/
def pointRationalTensorUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : PointIntegralTensorData D l hl E) :=
  (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
    ((pointIntegralCtfToConstructible D l E).obj S.monoidal.tensorUnit)

/-- The rational strong tensor comparison, using the recorded localization unit.
Source: blueprint rational clause (blueprint: def-sf-point-fibre-tensor-system). -/
def PointRationalTensorData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : PointIntegralTensorData D l hl E) :=
  PointFibreDerivedTensorComparisonData (𝟭 _)
    (pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι)
    (rationalPointFibreTensorBifunctor D l hl E)
    (pointRationalTensorUnit D l hl E S) (pointModuleDerivedBraiding E)

/-- The common-stage tensor before applying its recorded fibre realization.
Source: blueprint common-stage coefficient construction
(blueprint: def-sf-point-fibre-tensor-system). -/
def pointQbarSourceTensor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :=
  letI : ∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStageDerivedTensor l Ω (Spec (.of D.k))

/-- A simultaneous comparison family. The fields below record genuine monoidal data;
its canonical model and coefficient-change conditions are separate predicates.
Source: Stacks 07A4 and the four coefficient constructions
(blueprint: def-sf-point-fibre-tensor-system). -/
structure PointFibreDerivedTensorSystem
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] where
  /-- Every positive finite coefficient level. -/
  finite : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ), PointFiniteTensorData D l E n
  /-- Completed integral coefficients. -/
  integral : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
    PointIntegralTensorData D l hl E
  /-- Rational coefficients, with the unit inherited from the integral stage. -/
  rational : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
    PointRationalTensorData D l hl E (integral E)
  /-- Algebraically closed coefficients, with the unit from the base finite field. -/
  qbar : PointFibreDerivedTensorComparisonData (𝟭 _)
    (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω)
    (pointQbarSourceTensor D l hl Ω)
    (⟨Padic.finiteCoefficientBase l Ω, (rational
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω))).monoidal.tensorUnit⟩)
    (pointModuleDerivedBraiding Ω)


/-- Termwise finite sections, retaining the coefficient universe of the recorded fibre.
Source: Stacks 07A4, flat-term computation
(blueprint: def-sf-point-fibre-tensor-system). -/
def pointFiniteComplexSections
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
    (ComplexShape.up ℤ)


/-- The finite tensorator with its source category and fibre endpoints explicit.
Source: Stacks 07A4 (blueprint: def-sf-point-fibre-tensor-system). -/
@[no_expose] def pointFiniteTensorComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (S : PointFiniteTensorData D l E n)
    (M N : finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
      ((finitePointFibreTensorBifunctor D l E n).obj (M, N)) ≅
    (finitePointFibreTensorSource D l E n).obj M ⊗
      (finitePointFibreTensorSource D l E n).obj N :=
  @PointFibreDerivedTensorComparisonData.tensorIso
    (finiteTorConstructibleCategory l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)))
    (proEtaleDerivedCategory (Spec (.of D.k)) (Padic.coefficientExtensionRing l E (n + 1)))
    (DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    inferInstance inferInstance inferInstance inferInstance
    (pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ _ _ S M N

/-- The integral tensorator with the finite-Tor source and completed tensor endpoints explicit.
Source: Stacks 07A4 and the completed coefficient construction
(blueprint: def-sf-point-fibre-tensor-system). -/
@[no_expose] def pointIntegralTensorComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : PointIntegralTensorData D l hl E)
    (M N : finiteTorConstructibleIntegralCategory l E (Spec (.of D.k))) :
    (pointFibreIntegralAmbient D l E).obj
      ((integralPointFibreTensorBifunctor D l hl E).obj (M, N)) ≅
    (pointFibreIntegralAmbient D l E).obj M.obj ⊗
      (pointFibreIntegralAmbient D l E).obj N.obj :=
  @PointFibreDerivedTensorComparisonData.tensorIso
    (finiteTorConstructibleIntegralCategory l E (Spec (.of D.k)))
    (DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))))
    (DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
    inferInstance inferInstance inferInstance inferInstance
    (pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
    _ _ _ _ S M N

end WeilConjectures
