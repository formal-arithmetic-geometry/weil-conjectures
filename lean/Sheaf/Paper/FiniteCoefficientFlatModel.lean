/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Bounded flat models at finite coefficient levels

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-lem-sf-flat-model`,
`lem-sf-flat-model.md`, all three clauses (blueprint: lem-sf-flat-model).

## Main statements

- `AlgebraicGeometry.Scheme.finiteCoefficient_torAmplitude_iff_flatModel`
- `AlgebraicGeometry.Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel`
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_flatConstructibleModel`
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_boundedFlatConstructibleModel`

The etale encoding uses `ULift` of the same coefficient ring, with its canonical ring
structure; this is the size convention of the recorded etale module-sheaf definitions.
The pro-etale encoding retains site objects in `Type (u + 1)` and morphisms in `Type u`.
No equality between these universes is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The pro-etale flat-model equivalence at the finite coefficient ring `A_{E,n}`.
Source: blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`,
conditions (i) and (ii) (blueprint: lem-sf-flat-model).

Proof: use lem-sf-proetale-flat-model, transporting the constant-coefficient module
encoding to the recorded ringed-site encoding. Equivalently, choose a bounded-above
free resolution zero above b. Amplitude tested on the coefficient sheaf gives exactness
below a. The cokernel of the differential into degree a is flat, since its Tor_1 with
any module is H^(a-1) of the tensor resolution and vanishes by the amplitude bound.
Good truncation at a gives the model. Conversely a bounded complex of flat sheaves is
K-flat and its tensor with a degree-zero sheaf is zero outside the same interval. -/
theorem finiteCoefficient_torAmplitude_iff_flatModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T K)
    (a b : ℤ) (_hab : a ≤ b) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n) K a b ↔
      ∃ P : CochainComplex (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ,
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
          (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) (P.X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The same equivalence on the small etale site, with finite-value constructibility.
Source: blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`,
the small-etale clause (blueprint: lem-sf-flat-model).

Proof: convert bounded constructibility using the constructible-sheaf comparison and
apply lem-sf-etale-flat-model. The flat terms and support interval are unchanged. -/
theorem finiteCoefficient_hasTorAmplitude_iff_flatModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K)
    (a b : ℤ) (_hab : a ≤ b) :
    DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T a b K ↔
      ∃ P : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ℤ,
        IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  sorry

/-- On a Noetherian scheme the model may be chosen constructible termwise.
Source: blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`,
constructible variant (blueprint: lem-sf-flat-model).

Proof: apply lem-sf-etale-flat-constructible, in its recorded finite-value interface.
Its class-resolution proof lifts maps from constructible sheaves along epimorphisms
by finite sums of affine-etale free sheaves after refining their covers. The kernels
and cokernels remain constructible; good truncation gives a flat constructible term
in degree a. This is the forward implication of the recorded equivalence; invert its
isomorphism to obtain the displayed orientation. -/
theorem finiteCoefficient_exists_flatConstructibleModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] [IsNoetherian T]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T a b K) :
      ∃ P : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ℤ,
        IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P ∧
        (∀ q : ℤ, @Scheme.IsConstructibleEtaleModuleSheaf.{u} T
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
          ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
            Padic.coefficientExtensionRing l E n).finite_iff.mpr
              (Padic.finite_coefficientExtensionRing l E n hn)) (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  sorry

/-- Every bounded constructible etale complex of finite Tor amplitude on a Noetherian
scheme has a bounded flat constructible model.
Source: blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`,
last clause of the constructible variant (blueprint: lem-sf-flat-model).

Proof: unfold membership in D^b_ctf as bounded constructibility and the existence of
one ordered Tor-amplitude interval. Choose that interval and apply the constructible
variant of lem-sf-etale-flat-constructible. Its terms are flat and constructible, and
zero outside the same interval, as required. -/
theorem finiteCoefficient_exists_boundedFlatConstructibleModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] [IsNoetherian T]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T a b K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∃ P : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ℤ,
        IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P ∧
        (∀ q : ℤ, @Scheme.IsConstructibleEtaleModuleSheaf.{u} T
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
          ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
            Padic.coefficientExtensionRing l E n).finite_iff.mpr
              (Padic.finite_coefficientExtensionRing l E n hn)) (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  sorry

end AlgebraicGeometry.Etale
