/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.DerivedTensor
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Tensor-invertible objects at finite coefficient level

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md (blueprint: pur9-cs-def-invertible).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A chosen inverse and tensor-unit isomorphism in a category.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
structure TensorInvertibleData {C : Type v} [Category.{u} C]
    (tensor : C → C → C) (unit : C) (L : C) where
  inverse : C
  iso : tensor L inverse ≅ unit

/-- A tensor-invertibility predicate records the chosen inverse data existentially.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
def IsTensorInvertible {C : Type v} [Category.{u} C]
    (tensor : C → C → C) (unit : C) (L : C) : Prop :=
  Nonempty (TensorInvertibleData tensor unit L)

namespace Scheme

/-- The cochain-complex category used to present the pro-etale derived category.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
abbrev proEtaleComplex (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  CochainComplex
    (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A))))) ℤ

/-- The localization functor for the recorded pro-etale derived category.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
noncomputable def proEtaleQuotient (X : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleComplex X A ⥤ proEtaleDerivedCategory X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- The constant coefficient sheaf placed in degree zero on the pro-etale site.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
noncomputable def proEtaleConstantComplex (X : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleDerivedCategory X A := by
  classical
  let R := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} A))
  let S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  letI := SheafOfModules.monoidalCategory R
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} S)
  exact DerivedCategory.Q.obj
    ((HomologicalComplex.single (SheafOfModules.{u + 1} S) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit S))

/-- Chosen inverse data on the pro-etale site, including a K-flat representative
of the first factor and the displayed tensor-unit isomorphism.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
structure ProEtaleInvertibleData (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleDerivedCategory X A) where
  inverse : proEtaleDerivedCategory X A
  K₁ : proEtaleComplex X A
  K₂ : proEtaleComplex X A
  P : proEtaleComplex X A
  f : P ⟶ K₁
  hP : CochainComplex.IsAcyclicTensorKFlat P
  hf : QuasiIso f
  iso₁ : (proEtaleQuotient X A).obj K₁ ≅ L
  iso₂ : (proEtaleQuotient X A).obj K₂ ≅ inverse
  iso : derivedTensor X A K₁ K₂ P f hf hP ≅ proEtaleConstantComplex X A

/-- A pro-etale derived object is invertible when a chosen inverse and one displayed
tensor-unit isomorphism are supplied, computed from a K-flat resolution of the first
factor.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
def IsProEtaleInvertible (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleDerivedCategory X A) : Prop :=
  Nonempty (ProEtaleInvertibleData X A L)

/-- The pro-etale invertibility predicate at the finite coefficient level.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
def IsProEtaleInvertibleAtLevel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (X : Scheme.{u})
    (L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) : Prop :=
  IsProEtaleInvertible X (Padic.coefficientExtensionRing l E n) L

end Scheme

namespace Etale

namespace DerivedCategory

/-- The derived tensor bifunctor on the etale site.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
noncomputable def etaleDerivedTensor (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (L M : DerivedCategoryModule Λ X) : DerivedCategoryModule Λ X :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj M

/-- The corresponding chosen inverse datum on the small etale site.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
def IsEtaleInvertible (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (L : DerivedCategoryModule Λ X) : Prop :=
  IsTensorInvertible (etaleDerivedTensor Λ X) (AlgebraicGeometry.Etale.constantComplex Λ X) L

/-- The etale invertibility predicate at finite level, using the standard `ULift`
coefficient encoding of `D(X_ét,A)`.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-coprojection/pur9-cs-def-invertible.md, order 2349
(blueprint: pur9-cs-def-invertible).
-/
def IsEtaleInvertibleAtLevel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (X : Scheme.{u})
    (L : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X) : Prop :=
  IsEtaleInvertible (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X L

end DerivedCategory

end Etale

end AlgebraicGeometry

