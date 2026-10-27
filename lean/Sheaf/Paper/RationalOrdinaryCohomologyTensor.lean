/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.Paper.SfStrictDirectImageScalarComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic

/-! # Rational ordinary cohomology and tensoring cycles
Source: Milne, Lectures on Etale Cohomology, printed p. 126; Stacks Tags 00HT and 00HD;
point evaluation, clauses (2)--(3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor).
The tensor coordinates are E tensor H, with the tensor commutor identifying them with
H tensor E. Coefficients and carriers retain the point fibre's recorded universe lifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures
namespace RationalOrdinaryTensor

/-- Reuse the point targets' Grothendieck localization at its recorded Hom universe.
Source: point evaluation size convention
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
@[implicit_reducible]
instance (priority := 2000) moduleDerived (R : Type u) [CommRing R] :
    HasDerivedCategory.{u} (ModuleCat.{u} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded flat fraction-field tensor, with its actual lifted coefficient map.
Source: Stacks 00HT, 00HD; point evaluation (3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
abbrev tensor := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)

/-- The canonical derived point comparison, including the specified coefficient descent.
Source: point evaluation (3), its rational object and sections normalizations
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def derivedComparison (L : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointFibreCoefficientDown E).mapDerivedCategory.{u + 1, u + 2}.obj
        ((tensor l E).mapDerivedCategory.{u + 1, u + 1}.obj
          ((pointIntegralFibre D l hl E).obj L).obj) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.{u, u + 2}.obj
        ((pointRationalFibre D l hl E).obj
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj L)).obj :=
  (pointRationalNormalization D l hl E
      ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj L) ≪≫
    (pointFibreRationalDownIso D l E).symm.app L.obj).symm

/-- The canonical cycle-tensor map followed by the normalized point comparison.
Source: Milne p. 126; Stacks 00HT, 00HD; point evaluation (3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def cohomologyComparison (L : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (i : ℤ) :
    (pointFibreCoefficientDown E).obj ((tensor l E).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
            i).obj ((pointIntegralFibre D l hl E).obj L).obj)) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).obj
        ((DerivedCategory.coefficientFdCohomology E i).obj
          ((pointRationalFibre D l hl E).obj
            ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj L))) :=
  (pointFibreCoefficientDown E).mapIso
      (((tensor l E).mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 1, u + 1} i).app
        ((pointIntegralFibre D l hl E).obj L).obj) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 1, u + 2}
      (pointFibreCoefficientDown E) i).app
      ((tensor l E).mapDerivedCategory.{u + 1, u + 1}.obj
          ((pointIntegralFibre D l hl E).obj L).obj) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) i).mapIso
      (derivedComparison D l hl E L) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u, u + 2}
      (ModuleCat.uliftFunctor.{u + 1, u} E) i).symm.app _

/-- Integral homology coordinates supplied by any representative of the point complex.
Source: localization and point evaluation (2)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def integralCoordinates (L : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (C : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (e : DerivedCategory.Q.{u + 1}.obj C ≅ ((pointIntegralFibre D l hl E).obj L).obj) (i : ℤ) :=
  ((DerivedCategory.homologyFunctorFactors.{u + 1} _ i).app C).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e

/-- Coordinates on the rational representative C tensor E, retaining the point comparison.
Source: point evaluation (3), and localization of exact termwise tensor
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def rationalCoordinates (L : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (C : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (e : DerivedCategory.Q.{u + 1}.obj C ≅ ((pointIntegralFibre D l hl E).obj L).obj) (i : ℤ) :=
  (pointFibreCoefficientDown E).mapIso
      (((DerivedCategory.homologyFunctorFactors.{u + 1} _ i).app
        (((tensor l E).mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso
        (((tensor l E).mapDerivedCategoryFactors.{u + 1, u + 1}.app C).symm ≪≫
          (tensor l E).mapDerivedCategory.{u + 1, u + 1}.mapIso e)) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 1, u + 2}
      (pointFibreCoefficientDown E) i).app _ ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) i).mapIso
      (derivedComparison D l hl E L) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u, u + 2}
      (ModuleCat.uliftFunctor.{u + 1, u} E) i).symm.app _

/-- A cycle class uses Mathlib's kernel-to-cycle identification and homology quotient.
Source: Stacks 00HD, cycles and boundaries
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def cycleClass
    (C : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (i : ℤ) (z : LinearMap.ker (C.sc i).g.hom) : C.homology i :=
  (C.sc i).homologyπ ((C.sc i).moduleCatCyclesIso.inv z)

/-- The class of the actual tensor cycle, using the canonical exact-kernel comparison.
Source: Stacks 00HT, 00HD
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def tensorCycleClass
    (C : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (i : ℤ) (z : LinearMap.ker (C.sc i).g.hom) (a : E) :
    (((tensor l E).mapHomologicalComplex (.up ℤ)).obj C).homology i :=
  ((C.sc i).map (tensor l E)).homologyπ
    (((C.sc i).mapCyclesIso (tensor l E)).inv
      (ULift.up a ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E),
        pointIntegralToField l E] (C.sc i).moduleCatCyclesIso.inv z))

/-- The representative formula for the specified comparison, with no boundedness or
connectivity condition on a representative. Its right side is the class of z tensor a.
Source: Milne p. 126; Stacks 00HT and 00HD; point evaluation (2)--(3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def CycleFormula (L : sfIntegralConstructibleCategory l E (Spec (.of D.k))) : Prop :=
  ∀ (C : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (e : DerivedCategory.Q.{u + 1}.obj C ≅ ((pointIntegralFibre D l hl E).obj L).obj)
    (i : ℤ) (z : LinearMap.ker (C.sc i).g.hom) (a : E),
    (cohomologyComparison D l hl E L i).hom
      (ULift.up a ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E),
        pointIntegralToField l E]
          (integralCoordinates D l hl E L C e i).hom (cycleClass l E C i z)) =
      (rationalCoordinates D l hl E L C e i).hom (tensorCycleClass l E C i z a)

/-- Naturality with respect to the actual integral point-image morphisms. In particular,
apply this to Rf_* of any integral coefficient morphism on Y.
Source: Milne p. 126 and point evaluation (3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor).
Proof: the exact cycle/quotient comparison is natural on chain maps. Tensor is flat
by lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-localization-flat and
lem-weil-pbc-flat-tensor-exact, so it preserves quasi-isomorphisms. The identity
therefore descends through derived localization (def-weil-abstract-derived-category).
The rational point-fibre map on h tensor 1 is the integral section map tensored with
1 by def-weil-finite-coefficient-point. Compose with its normalization and the
coefficient descent counit. Pure tensors generate, proving the asserted equation. -/
theorem naturality (L M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (h : L ⟶ M) (i : ℤ) :
    (pointFibreCoefficientDown E).map ((tensor l E).map
        ((DerivedCategory.coefficientFgCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}) i).map
            ((pointIntegralFibre D l hl E).map h))) ≫
        (cohomologyComparison D l hl E M i).hom =
      (cohomologyComparison D l hl E L i).hom ≫
        (ModuleCat.uliftFunctor.{u + 1, u} E).map
          ((DerivedCategory.coefficientFdCohomology E i).map
            ((pointRationalFibre D l hl E).map
              ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).map h))) := by
  sorry

variable (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]

/-- The normalized derived scalar comparison for ordinary sections of K.
Source: point evaluation (3); Milne p. 126
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def ordinaryDerivedComparison (K : sfIntegralConstructibleCategory l E Y) :=
  derivedComparison D l hl E (integralImage D l hl E Y K)

/-- The specified E-linear ordinary scalar comparison, using exactly the recorded
ordinary direct image. The tensor commutor changes E tensor H to H tensor E.
Source: Milne p. 126; point evaluation (2)--(3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor). -/
def ordinaryComparison (K : sfIntegralConstructibleCategory l E Y) (i : ℤ) :=
  cohomologyComparison D l hl E (integralImage D l hl E Y K) i

/-- The canonical rational ordinary cohomology comparison is invertible, has the
specified formula on every representative and is normalized on every degree-zero
constant-coefficient class. In particular this includes the unit coefficient section.
Naturality is the preceding theorem applied to the integral direct-image morphism.
Source: Milne, Lectures on Etale Cohomology, printed p. 126;
Stacks algebra.tex, Tags 00HT and 00HD; point evaluation (2)--(3)
(blueprint: lem-pod-rational-ordinary-cohomology-tensor).
Proof:
1. lem-sf-integral-direct-image-constructible puts Rf_*K in the integral constructible
   category at s. lem-sf-strict-direct-image-scalar-comparison makes this functor
   integral-linear. def-weil-finite-coefficient-point identifies the rational point
   image with C tensor E and extends its integral morphisms termwise.
   def-weil-ordinary-compact-cohomology identifies these with the stated groups.
2. lem-weil-l-adic-extension-integers-dvr makes E the fraction field of V.
   lem-weil-pbc-localization-flat makes E flat, so lem-weil-pbc-flat-tensor-exact applies.
3. Tensor the cycle, boundary and quotient sequences. Exactness identifies the kernel
   with Z^i tensor E, the image with B^i tensor E and their quotient with H^i(C) tensor E.
   The inverse quotient comparison sends [z] tensor a to [z tensor a]; replacing z by
   z + dw changes it by d(w tensor a). Scalar multiplication is on the E factor.
4. The formula commutes with chain maps and preserves quasi-isomorphisms. Localization
   (def-weil-abstract-derived-category) gives independence of representatives and
   naturality on all derived morphisms, as recorded by naturality above.
5. Set i = 0 and a = 1 for the completed constant coefficient object. Every class is
   a cycle class, including the class of the coefficient section 1. Point evaluation
   defines its rational unit by that same section tensored with 1. No computation of
   H^0, connectedness, properness or smoothness enters. -/
theorem rational_ordinary_cohomology_tensor (K : sfIntegralConstructibleCategory l E Y) :
    (∀ i : ℤ, IsIso (ordinaryComparison D l hl E Y K i).hom) ∧
    CycleFormula D l hl E (integralImage D l hl E Y K) ∧
    (∀ (C : CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
      (e : DerivedCategory.Q.{u + 1}.obj C ≅
        (integralOrdinarySections D l hl E Y
          (integralCohomologyCoefficient D l hl E Y)).obj)
      (z : LinearMap.ker (C.sc 0).g.hom),
      (ordinaryComparison D l hl E Y (integralCohomologyCoefficient D l hl E Y) 0).hom
        (ULift.up (1 : E) ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E),
          pointIntegralToField l E]
            (integralCoordinates D l hl E
              (integralImage D l hl E Y (integralCohomologyCoefficient D l hl E Y))
              C e 0).hom (cycleClass l E C 0 z)) =
        (rationalCoordinates D l hl E
          (integralImage D l hl E Y (integralCohomologyCoefficient D l hl E Y)) C e 0).hom
            (tensorCycleClass l E C 0 z 1)) := by
  sorry

end RationalOrdinaryTensor
end WeilConjectures
