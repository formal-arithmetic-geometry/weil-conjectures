/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Paper.FiniteCoefficientFlatModel
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModelReduction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Reduction of bounded flat models at finite coefficient levels

Source: Weil blueprint, sec-smooth-purity/sk-lem-sf-flat-model,
lem-sf-reduction-flat-model.md (blueprint: lem-sf-reduction-flat-model).

The pro-etale statement uses the recorded constant-ring module category and intrinsic
constructibility predicate. The etale statement uses the recorded finite-value
constructibility predicate.
All scalar extensions below use the canonical quotient map between the actual stages;
the upstream theorems provide the general proof ingredients without an encoding change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

/-- The quotient factor map between the actual finite coefficient rings, canonically
lifted to the coefficient universe. No flatness of this ring map is assumed.
Source: blueprint, lem-sf-reduction-flat-model.md, the map A_{E,n} to A_{E,m}
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionCoefficientMap :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E n) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E m) :=
  RingHom.ulift
    (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal l E n)
      (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))

/-- The canonical constant coefficient map from stage n to stage m.
Source: blueprint, lem-sf-reduction-flat-model.md, coefficient reduction
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionRingMap :
    proEtaleConstantRing T (Padic.coefficientExtensionRing l E n) ⟶
      proEtaleConstantRing T (Padic.coefficientExtensionRing l E m) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (flatModelReductionCoefficientMap l E m n hmn))

set_option linter.defProp false in
/-- Canonical scalar extension with its specified object/map formulas and its universal
left-derived pair, specialized to the finite-level quotient map. The formulas determine
the ordinary functor; the universal property determines the derived pair up to unique
compatible isomorphism.
Source: Stacks Tags 03EK, 06YT and 06YY; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionData :=
  letI : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)))
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E m)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (flatModelReductionRingMap l E m n hmn T)

/-- Ordinary tensor along the specified quotient map, fixed on objects and maps by
sectionwise tensor followed by sheafification in the recorded change-of-rings theorem.
Source: blueprint, lem-sf-reduction-flat-model.md, ordinary tensor complex
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionChange :=
  (flatModelReductionData l E m n hmn T).choose

/-- Additivity of the specified scalar extension, from its universal construction.
Source: Stacks Tag 03EK; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable instance flatModelReductionChange_additive :
    (flatModelReductionChange l E m n hmn T).Additive :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal left-derived scalar-extension pair and its K-flat computation.
Source: Stacks Tags 06YT and 06YY; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionDerivedData :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived reduction from finite coefficient stage n to stage m, as the universal
left-derived functor of the specified ordinary scalar extension.
Source: blueprint, lem-sf-reduction-flat-model.md, definition of K_m
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReduction :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E m) :=
  (flatModelReductionDerivedData l E m n hmn T).choose

/-- On the recorded pro-etale category, reduction of the supplied flat model is a flat
model in the same interval, and the derived reduction has that Tor amplitude.
Source: blueprint, sec-smooth-purity/sk-lem-sf-flat-model/
lem-sf-reduction-flat-model.md (blueprint: lem-sf-reduction-flat-model).

Proof:
1. The supplied model is bounded and termwise flat, hence K-flat by lem-sf-flat-model:
for every acyclic complex, tensor with each term is acyclic, and bounded totalization
preserves this acyclicity.
2. The universal change-of-rings counit therefore computes derived reduction on P by
its ordinary termwise scalar extension. Transport along the given isomorphism to K
produces the asserted isomorphism with K_m (def-weil-derived-tensor).
3. Each reduced term is flat over A_{E,m}: for an injection of A_{E,m}-module sheaves,
tensor associativity identifies its tensor with the reduced term with tensor by the
original A_{E,n}-flat term (lem-exc-constant-inverse-image-flat). Hence it stays injective.
4. Scalar extension sends zero to zero, so the support remains [a,b]. Tensoring this
bounded flat model with any test sheaf computes derived tensor and remains supported
in [a,b]; its cohomology vanishes outside that interval, as in lem-sf-flat-model.
The original amplitude hypothesis supplies the ordered-interval condition a ≤ b. -/
theorem finiteCoefficient_reduction_flatModel
    (_hm : 1 ≤ m) (hn : 1 ≤ n)
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T K)
    (a b : ℤ)
    (P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) (P.X q))
    (_hsupp : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))
    (_e : K ≅ DerivedCategory.Q.obj P) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E m))
      ((((flatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).X q)) ∧
    (∀ q : ℤ, q < a ∨ b < q → IsZero
      ((((flatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).X q)) ∧
    Nonempty ((flatModelReduction l E m n hmn T).obj K ≅ DerivedCategory.Q.obj
      (((flatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) ∧
    (HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n) K a b →
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E m)
        ((flatModelReduction l E m n hmn T).obj K) a b) := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

/-- Ordinary scalar extension on etale module sheaves: extend scalars on the underlying
presheaf and sheafify, with the induced tensor differentials on complexes.
Source: blueprint, lem-sf-reduction-flat-model.md, ordinary tensor model
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def etaleFlatModelReductionChange :
    Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
      Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Scheme.flatModelReductionCoefficientMap l E m n hmn)) ⋙
    presheafToSheaf _ _

/-- Additivity inherited from presheaf scalar extension and sheafification.
Source: Stacks Tag 03EK; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable instance etaleFlatModelReductionChange_additive :
    (etaleFlatModelReductionChange l E m n hmn T).Additive :=
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)).left_adjoint_additive
  inferInstanceAs ((sheafToPresheaf _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Scheme.flatModelReductionCoefficientMap l E m n hmn)) ⋙
    presheafToSheaf _ _).Additive)

/-- Reduction of an etale flat model over the actual finite coefficient stages.
The derived tensor on the right of the comparison retains the original scalars;
the displayed scalar-restriction functor identifies its quotient-ring model.
Source: blueprint, lem-sf-reduction-flat-model.md, etale clause
(blueprint: lem-sf-reduction-flat-model).

Proof:
1. The bounded flat P is K-flat (lem-sf-flat-model), since tensoring an acyclic
complex with each flat term is exact and the bounded total complex is acyclic.
2. K-flat computation of derived tensor (def-weil-derived-tensor) identifies K_m
with ordinary termwise scalar extension, regarded with the original scalars.
3. For any injection of modules over A_{E,m}, tensor associativity identifies its
tensor by each reduced term with tensor by the original flat term. This preserves
injections (lem-exc-constant-inverse-image-flat), hence the terms are A_{E,m}-flat.
4. Scalar extension is additive and preserves zero, so the same degree interval
supports the reduced model. Its bounded flatness gives the final Tor amplitude by
lem-sf-flat-model. No constructibility of the terms of P is required. -/
theorem finiteCoefficient_etale_reduction_flatModel
    (_hm : 1 ≤ m) (hn : 1 ≤ n)
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K)
    (a b : ℤ)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ℤ)
    (_hP : IsBoundedFlatComplex
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P)
    (_e : K ≅ (_root_.DerivedCategory.Q).obj P) :
    IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) a b
      (((etaleFlatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ∧
    Nonempty ((Sheaf.restrictScalars T.smallEtaleTopology
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)).mapDerivedCategory.obj
        ((_root_.DerivedCategory.Q).obj
          (((etaleFlatModelReductionChange l E m n hmn T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≅
      ((derivedTensor (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1}
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
              ((ModuleCat.restrictScalars
                (Scheme.flatModelReductionCoefficientMap l E m n hmn)).obj
                (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))))))) ∧
    DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) T a b
      ((_root_.DerivedCategory.Q).obj
        (((etaleFlatModelReductionChange l E m n hmn T).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  sorry

end AlgebraicGeometry.Etale
