# AlgebraicGeometry.ProEtale.FiniteModelQuotient.LocalCalculation

## Reason

The original LocalCalculation is one universal proposition with seven nested conjuncts.
It repeats concrete derived categories and encoding terms in several large field types.
Replace that proposition by two records: ChartCalculation has exactly the seven original
conjuncts, and LocalCalculationAt has the original universal chart property as its sole field,
indexed by the complex being calculated. LocalCalculation specializes it to the actual
reduction. Indexing makes that complex explicit when the proof generalizes it.
This is logically equivalent, including the empty scheme, empty covers and zero ranks.

The quotient inverse-image interface also exposed two definitionally equal coefficient
presentations. A diagnostic specialization of encoding_pullback_fixed to its native
FiniteDiscreteOrdinary.coefficient (R l E n) expression checked immediately; using
DerivedNakayama.quotientRing l E (n+1) instead reached the kernel deterministic timeout.
Use the native coefficient expression in the named quotient category and pullbacks, and
provide small names for the existing category, abelian, derived, encoding and homology
structures. Every named structure is constructed from the existing instance, and every
functor is the existing functor. No ring, topology, quotient map, encoding or reduction
object is replaced by an arbitrary choice. The norm topology remains the recorded
coefficientExtensionAbsoluteValue topology.

The public cohomology_descent signature is preserved verbatim. A proved private conversion
introduces the definitionally equal named homology and encoding coordinates in its proof. A separate original-
signature check compiled in 6.4 seconds (e000152b683c451fa8121eba).
The parent proof constructs the two records and uses the same encoding in their fields.
These are proof coordinates; no Challenge declaration is edited. The independent reader
must verify equivalence of the records and definitional equality of the named structures.

## Old

Coordinate definitions and item signature, verbatim before this delivery:

```lean
abbrev A := Padic.coefficientExtensionIntegers l E

/-- The recorded positive-level scalar quotient. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev R (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- The normalized encoding with exactly the recorded quotient topology.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev Encoding (n : ℕ) (T : Scheme.{u}) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (R l E n) T

/-- The recorded scalar-extension model, with the induced norm topology on A.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def model (T : Scheme.{u}) (P : ModuleCat.{u + 1} (A l E)) :
    AdicCompletion.Modules l E T :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (FiniteConstantModel.modelFunctor (A l E) T).obj P

/-- Derived reduction of a sheaf in degree zero along the actual quotient homomorphism.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def reduction (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    AdicCompletion.FiniteDerived l E T n :=
  (AdicCompletion.derivedReduction l E T n).obj ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Reduce every entry of the given scalar matrix by the actual quotient homomorphism.
The lift only puts the scalar coordinates in the site's coefficient universe.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def matrix (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    Matrix (Fin b) (Fin a) (ULift.{u + 1} (R l E n)) :=
  fun i j ↦ ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (v i j))

/-- The specified reduced scalar linear map, including ranks zero.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def differential (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin a → ULift.{u + 1} (R l E n)) ⟶
      ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin b → ULift.{u + 1} (R l E n)) :=
  ModuleCat.ofHom (matrix l E n a b v).mulVecLin

/-- The literal complex of free quotient modules in degrees -1 and 0.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def scalarComplex (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) ℤ :=
  HomologicalComplex.double (differential l E n a b v)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- Constant realization of that literal two-term scalar complex in ordinary coordinates.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def ordinaryComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  DerivedCategory.Q.obj
    (((constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (scalarComplex l E n a b v))

/-- The original integral scalar matrix in the lifted coordinates of the finite free modules.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def integralDifferential (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (A l E) (Fin a → ULift.{u + 1} (A l E)) ⟶
      ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) :=
  ModuleCat.ofHom
    (((LinearEquiv.piCongrRight fun _ : Fin b ↦
        (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).symm.toLinearMap).comp
      (v.mulVecLin.comp
        (LinearEquiv.piCongrRight fun _ : Fin a ↦
          (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).toLinearMap))

/-- Internal coordinates for the literal two-term quotient complex, transported by
exactly the normalized finite coefficient equivalence (not an arbitrary equivalence).
Source: blueprint specified scalar resolution and ordinary coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def internalComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T) :
    AdicCompletion.FiniteDerived l E T n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.fixedDerived.inverse.obj (ordinaryComplex l E T n a b v)

/-- The chart calculation for every specified scalar resolution on every member of
any chosen stratification and pro-etale covers. The two cohomology identifications
retain the quotient coefficient action. Source: blueprint Local models and Locality
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def LocalCalculation (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ∀ (S : Scheme.Stratification V)
    (C : ∀ i : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i))
    (i : Fin S.n) (j : (C i).I₀) (P : ModuleCat.{u + 1} (A l E))
    (_hP : Module.FinitePresentation (A l E) P)
    (_eP : (CondensedRing.upperStar (DerivedNakayama.integerRing l E)
      ((C i).f j ≫ S.immersion i)).obj M ≅ model l E ((C i).X j) P)
    (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
    (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P)
    (_hinj : Function.Injective (integralDifferential l E a b v).hom)
    (_hexact : Function.Exact (integralDifferential l E a b v).hom w.hom)
    (_hsurj : Function.Surjective w.hom),
    Nonempty
      (((CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.quotientRing l E (n + 1))
          ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n)) ≅
        internalComplex l E ((C i).X j) n a b v (enc ((C i).X j))) ∧
    Nonempty
      ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((enc ((C i).X j)).fixedDerived.functor.obj
          ((CondensedRing.moduleObjectDerivedPullback
            (DerivedNakayama.quotientRing l E (n + 1))
            ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n))) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (kernel (differential l E n a b v))) ∧
    Nonempty
      ((DerivedCategory.homologyFunctor _ 0).obj
        ((enc ((C i).X j)).fixedDerived.functor.obj
          ((CondensedRing.moduleObjectDerivedPullback
            (DerivedNakayama.quotientRing l E (n + 1))
            ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n))) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (cokernel (differential l E n a b v))) ∧
    Finite ↥(kernel (differential l E n a b v)) ∧
    Finite ↥(cokernel (differential l E n a b v)) ∧
    Module.FinitePresentation (ULift.{u + 1} (R l E n))
      ↥(kernel (differential l E n a b v)) ∧
    Module.FinitePresentation (ULift.{u + 1} (R l E n))
      ↥(cokernel (differential l E n a b v))

/-- Ordinary boundedness and intrinsic constructibility in the recorded finite-ring
encoding. The explicit finiteness witness installs only the finiteness just asserted
by the main theorem. Source: blueprint finite constructible cohomology clause
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def OrdinaryConclusion (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (hf : Finite (R l E n)) (e : Encoding l E n V) : Prop :=
  letI := hf
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  DerivedCategory.TStructure.t.bounded (e.fixedDerived.functor.obj (reduction l E V M n)) ∧
    ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
      (ULift.{u + 1} (R l E n))
      ((DerivedCategory.homologyFunctor _ q).obj
        (e.fixedDerived.functor.obj (reduction l E V M n)))

theorem cohomology_descent
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M)
    (n : ℕ) (hf : Finite (R l E n))
    (hd : @DiscreteTopology (R l E n) (AdicCompletion.finiteTopology l E (n + 1)))
    (enc : ∀ T : Scheme.{u}, Encoding l E n T)
    (hcalc : LocalCalculation l E V M n enc) :
    (∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (∀ q : ℤ, IsConstantModelConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) V
      ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (letI := hf
     letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
       (ULift.{u + 1} (R l E n))
       ((DerivedCategory.homologyFunctor _ q).obj
         ((enc V).fixedDerived.functor.obj (reduction l E V M n))))
```

## New

The same objects and conditions with explicit category and chart coordinates:

```lean
abbrev A := Padic.coefficientExtensionIntegers l E

/-- The recorded positive-level scalar quotient. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev R (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def quotientModules (n : ℕ) (T : Scheme.{u}) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Internal (R l E n) T

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleCategory (n : ℕ) (T : Scheme.{u}) :
    Category.{u + 1} (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstanceAs (Category (FiniteDiscreteOrdinary.Internal (R l E n) T))

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleAbelian (n : ℕ) (T : Scheme.{u}) :
    @Abelian (quotientModules l E n T) (quotientModuleCategory l E n T) := by
  dsimp only [quotientModuleCategory, quotientModules]
  infer_instance

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleDerived (n : ℕ) (T : Scheme.{u}) :
    @HasDerivedCategory.{u + 1} (quotientModules l E n T)
      (quotientModuleCategory l E n T) (quotientModuleAbelian l E n T) := by
  dsimp only [quotientModuleCategory, quotientModuleAbelian, quotientModules]
  infer_instance

attribute [instance] quotientModuleCategory quotientModuleAbelian quotientModuleDerived

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def quotientHomology (n : ℕ) (T : Scheme.{u}) (q : ℤ) :
    DerivedCategory (quotientModules l E n T) ⥤ quotientModules l E n T :=
  DerivedCategory.homologyFunctor _ q

/-- Ordinary quotient-module coordinates with the existing category structures.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def ordinaryHomology (n : ℕ) (T : Scheme.{u}) (q : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) ⥤ Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) :=
  DerivedCategory.homologyFunctor _ q

/-- Exact quotient inverse image in the named module category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientUpperStar (n : ℕ) {V T : Scheme.{u}} (f : T ⟶ V) :
    quotientModules l E n V ⥤ quotientModules l E n T :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient (R l E n)) f

/-- Derived quotient inverse image in the named category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def quotientPullback (n : ℕ) {V T : Scheme.{u}} (f : T ⟶ V) :
    DerivedCategory (quotientModules l E n V) ⥤
      DerivedCategory (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  CondensedRing.moduleObjectDerivedPullback (FiniteDiscreteOrdinary.coefficient (R l E n)) f

/-- The normalized encoding with exactly the recorded quotient topology.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev Encoding (n : ℕ) (T : Scheme.{u}) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (R l E n) T

/-- The specified ordinary encoding with its source written as the actual quotient
module category. Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def fixedEncoding (n : ℕ) (T : Scheme.{u}) (e : Encoding l E n T) :
    quotientModules l E n T ≌
      Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.ordinary.trans e.fixed

/-- The specified derived encoding with its source written as the actual quotient
module category. Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
def derivedEncoding (n : ℕ) (T : Scheme.{u}) (e : Encoding l E n T) :
    DerivedCategory (quotientModules l E n T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.fixedDerived

/-- The recorded scalar-extension model, with the induced norm topology on A.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def model (T : Scheme.{u}) (P : ModuleCat.{u + 1} (A l E)) :
    AdicCompletion.Modules l E T :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (FiniteConstantModel.modelFunctor (A l E) T).obj P

/-- Derived reduction of a sheaf in degree zero along the actual quotient homomorphism.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def reduction (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    DerivedCategory (quotientModules l E n T) :=
  (AdicCompletion.derivedReduction l E T n).obj ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Reduce every entry of the given scalar matrix by the actual quotient homomorphism.
The lift only puts the scalar coordinates in the site's coefficient universe.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def matrix (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    Matrix (Fin b) (Fin a) (ULift.{u + 1} (R l E n)) :=
  fun i j ↦ ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (v i j))

/-- The specified reduced scalar linear map, including ranks zero.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def differential (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin a → ULift.{u + 1} (R l E n)) ⟶
      ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin b → ULift.{u + 1} (R l E n)) :=
  ModuleCat.ofHom (matrix l E n a b v).mulVecLin

/-- The literal complex of free quotient modules in degrees -1 and 0.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def scalarComplex (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) ℤ :=
  HomologicalComplex.double (differential l E n a b v)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- Constant realization of that literal two-term scalar complex in ordinary coordinates.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def ordinaryComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  DerivedCategory.Q.obj
    (((constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (scalarComplex l E n a b v))

/-- The original integral scalar matrix in the lifted coordinates of the finite free modules.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def integralDifferential (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (A l E) (Fin a → ULift.{u + 1} (A l E)) ⟶
      ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) :=
  ModuleCat.ofHom
    (((LinearEquiv.piCongrRight fun _ : Fin b ↦
        (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).symm.toLinearMap).comp
      (v.mulVecLin.comp
        (LinearEquiv.piCongrRight fun _ : Fin a ↦
          (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).toLinearMap))

/-- Internal coordinates for the literal two-term quotient complex, transported by
exactly the normalized finite coefficient equivalence (not an arbitrary equivalence).
Source: blueprint specified scalar resolution and ordinary coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def internalComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T) :
    DerivedCategory (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (derivedEncoding l E n T e).inverse.obj (ordinaryComplex l E T n a b v)

/-- Properties of a specified quotient chart, kept as a record so projections do
not normalize the other derived cohomology types.
Source: blueprint Local models and Locality
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
structure ChartCalculation (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T)
    (D : DerivedCategory (quotientModules l E n T)) : Prop where
  /-- The reduction is the specified two-term complex. -/
  complex : Nonempty (D ≅ internalComplex l E T n a b v e)
  /-- The degree -1 cohomology is the constant kernel. -/
  kernelModel :
    Nonempty ((ordinaryHomology l E n T (-1)).obj
      ((derivedEncoding l E n T e).functor.obj D) ≅
      (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (kernel (differential l E n a b v)))
  /-- The degree zero cohomology is the constant cokernel. -/
  cokernelModel :
    Nonempty ((ordinaryHomology l E n T 0).obj
      ((derivedEncoding l E n T e).functor.obj D) ≅
      (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (cokernel (differential l E n a b v)))
  /-- Finiteness of the scalar kernel. -/
  finiteKernel : Finite ↥(kernel (differential l E n a b v))
  /-- Finiteness of the scalar cokernel. -/
  finiteCokernel : Finite ↥(cokernel (differential l E n a b v))
  /-- Finite presentation of the scalar kernel. -/
  fpKernel : Module.FinitePresentation (ULift.{u + 1} (R l E n))
    ↥(kernel (differential l E n a b v))
  /-- Finite presentation of the scalar cokernel. -/
  fpCokernel : Module.FinitePresentation (ULift.{u + 1} (R l E n))
    ↥(cokernel (differential l E n a b v))

/-- The chart calculation for every specified scalar resolution on every member of
any chosen stratification and pro-etale covers. The two cohomology identifications
retain the quotient coefficient action. Source: blueprint Local models and Locality
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
structure LocalCalculationAt (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T)
    (K : DerivedCategory (quotientModules l E n V)) : Prop where
  /-- Every specified scalar chart has the required finite quotient calculation. -/
  chart :
    ∀ (S : Scheme.Stratification V)
      (C : ∀ i : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i))
      (i : Fin S.n) (j : (C i).I₀) (P : ModuleCat.{u + 1} (A l E))
      (_hP : Module.FinitePresentation (A l E) P)
      (_eP : (CondensedRing.upperStar (DerivedNakayama.integerRing l E)
        ((C i).f j ≫ S.immersion i)).obj M ≅ model l E ((C i).X j) P)
      (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
      (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P)
      (_hinj : Function.Injective (integralDifferential l E a b v).hom)
      (_hexact : Function.Exact (integralDifferential l E a b v).hom w.hom)
      (_hsurj : Function.Surjective w.hom),
      ChartCalculation l E ((C i).X j) n a b v (enc ((C i).X j))
        ((quotientPullback l E n
          ((C i).f j ≫ S.immersion i)).obj K)

/-- The universal chart calculation at the actual specified reduction.
Source: blueprint Local models and Locality
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
abbrev LocalCalculation (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T) : Prop :=
  LocalCalculationAt l E V M n enc (reduction l E V M n)

/-- Ordinary boundedness and intrinsic constructibility in the recorded finite-ring
encoding. The explicit finiteness witness installs only the finiteness just asserted
by the main theorem. Source: blueprint finite constructible cohomology clause
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def OrdinaryConclusion (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (hf : Finite (R l E n)) (e : Encoding l E n V) : Prop :=
  let := hf
  DerivedCategory.TStructure.t.bounded
    ((derivedEncoding l E n V e).functor.obj (reduction l E V M n)) ∧
    ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
      (ULift.{u + 1} (R l E n))
      ((ordinaryHomology l E n V q).obj
        ((derivedEncoding l E n V e).functor.obj (reduction l E V M n)))

theorem cohomology_descent
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M)
    (n : ℕ) (hf : Finite (R l E n))
    (hd : @DiscreteTopology (R l E n) (AdicCompletion.finiteTopology l E (n + 1)))
    (enc : ∀ T : Scheme.{u}, Encoding l E n T)
    (hcalc : LocalCalculation l E V M n enc) :
    (∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (∀ q : ℤ, IsConstantModelConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) V
      ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (letI := hf
     letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
       (ULift.{u + 1} (R l E n))
       ((DerivedCategory.homologyFunctor _ q).obj
         ((enc V).fixedDerived.functor.obj (reduction l E V M n))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteModelSheafQuotientData | unclaimed | Equivalent records and named existing coordinates. |
| Sheaf.Paper.FiniteModelQuotientCohomologyDescent | P3 | Uses the record projections and named coordinate APIs. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | unclaimed | Constructs the outer record and uses the typed derived encoding. Public signature unchanged. |
| Sheaf.Paper.FiniteModelQuotientChartComparison | unclaimed | Same reduction and internal complex; mathematical statement unchanged. |
| Sheaf.Paper.FiniteModelFreeComplexReduction | unclaimed | Same coordinate objects; statement unchanged. |
| Sheaf.Paper.FiniteModelOrdinaryFreeComplex | unclaimed | Same coordinate objects; statement unchanged. |
| Sheaf.Paper.FiniteModelOrdinaryScalar | unclaimed | Same model and encoding; statement unchanged. |
| Sheaf.Paper.IntegralScalarModelCoordinates | P3 | New proved coordinate bridge using the same integral model. |

The downstream tool lists the data module, the item and its parent for LocalCalculation;
the additional rows are direct consumers of the other coordinate definitions. Later
consumers use the unchanged mathematical theorem interfaces. Claims were checked on
2026-10-26. No declaration in the adopted WeilConjectures tree is edited.

The complete packet, including direct consumers, is checked in import order by lcompile.py.
Final compile results are recorded in report.md and by the delivery tool. Only the maintainer
performs the global build; this record does not claim one.

## Status

landed 20261026T023654-L-590958 2026-10-26 (merge of deliver/P3/Sheaf.Paper.FiniteModelQuotientCohomologyDescent)
