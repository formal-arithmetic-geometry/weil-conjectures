/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Homology.RegularQuotientConeBasic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Notation for regular scalar quotients

Source: blueprint, sk-lem-sp-tower, proof paragraph 1, coefficient tensor calculation;
Stacks Project, Tags 03EI, 03CY, 03EK and 06YQ.
(blueprint: def-sp-regular-scalar-quotient-notation).

Natural index n denotes the positive exponent n+1. The quotient rings and principal
Koszul complexes are the existing constructions. The maps in the conclusion are
specified on the quotient projections, rather than chosen from unnormalized existence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.RegularScalarQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J CommRingCat.{r}]

/-- The recorded module category over a commutative ring sheaf.
Source: Stacks 03D7 (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing regular module sheaf.
Source: Stacks 03EK (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev unit (R : Sheaf J CommRingCat.{r}) : Modules R :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The recorded scalar restriction.
Source: Stacks 03D7 (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev res {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map f)

/-- The canonical linear map induced by a ring-sheaf map.
Source: Stacks 03D7 (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev ringMap {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.RegularQuotientCone.ringMap f

variable (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

/-- Scalar powers on any module, using the recorded global scalar transformation.
Source: Stacks 03EK (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev mul (M : Modules R) (k : ℕ) : M ⟶ M :=
  endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) k

/-- The existing quotient ring sheaf at positive level n+1.
Source: Stacks 03CY (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev B (n : ℕ) := principalPowerRingQuotient R t (n + 1)

/-- Its canonical quotient projection.
Source: Stacks 03CY (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev projection (n : ℕ) : R ⟶ B R t n := principalPowerRingProjection R t (n + 1)

/-- The quotient, regarded as an R-module by the canonical projection.
Source: Stacks 03D7 (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev Q (n : ℕ) : Modules R := (res (projection R t n)).obj (unit (B R t n))

/-- A module concentrated in degree zero, using the existing single functor.
Source: Stacks 05RR (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev single {S : Sheaf J CommRingCat.{r}} (M : Modules S) :=
  (CochainComplex.singleFunctor (Modules S) 0).obj M

/-- The two-term scalar cone, in degrees minus one and zero.
Source: blueprint sk-lem-sp-tower, coefficient tensor
(blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev twoTerm (M : Modules R) (k : ℕ) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))

/-- Inclusion of the degree-zero coefficient into its single complex.
Source: Stacks 05RR (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev singleIn {S : Sheaf J CommRingCat.{r}} (M : Modules S) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv

/-- The degree-zero coordinate inclusion of the two-term scalar cone.
Source: blueprint sk-lem-sp-tower (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev rightIn (M : Modules R) (k : ℕ) : M ⟶ (twoTerm R t M k).X 0 :=
  singleIn M ≫ (CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))).f 0

/-- The degree-minus-one coordinate inclusion of the two-term scalar cone.
Source: blueprint sk-lem-sp-tower (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev leftIn (M : Modules R) (k : ℕ) : M ⟶ (twoTerm R t M k).X (-1) :=
  singleIn M ≫ (CochainComplex.mappingCone.inl
    ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))).v 0 (-1) rfl

/-- The actual total tensor, with the quotient in the first factor.
Source: Stacks 06YN (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev tensor (n m : ℕ) :=
  CochainComplex.mapBifunctor (single (Q R t n)) (principalKoszul R t m)
    (curriedTensor (Modules R))

/-- The global scalar transported along a coefficient map.
Source: Stacks 03D7 (blueprint: def-sp-regular-scalar-quotient-notation). -/
def scalarImage {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) : (unit S).sections :=
  (Functor.sectionsFunctor Cᵒᵖ).map
    (Functor.whiskerRight f.hom (forget CommRingCat.{r})) t

/-- The two-term complex over the higher quotient coefficient ring itself.
Source: blueprint sk-lem-sp-tower (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev P (n m : ℕ) :=
  twoTerm (B R t n) (scalarImage R t (projection R t n)) (unit (B R t n)) (m + 1)

/-- Restriction of the two-term quotient-linear complex to R.
Source: Stacks 03D7 (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev restrictedP (n m : ℕ) :=
  ((res (projection R t n)).mapHomologicalComplex (.up ℤ)).obj (P R t n m)

/-- The coefficient summand inclusion in the total tensor, normalized by x tensor 1.
Source: Stacks 03EK, tensor unit (blueprint: def-sp-regular-scalar-quotient-notation). -/
def tensorIn (n m : ℕ) (i : ℤ) (j : unit R ⟶ (principalKoszul R t m).X i) :
    Q R t n ⟶ (tensor R t n m).X i :=
  (ρ_ (Q R t n)).inv ≫
    tensorHom (singleIn (Q R t n)) j ≫
    CochainComplex.ιMapBifunctor (single (Q R t n)) (principalKoszul R t m)
      (curriedTensor (Modules R)) 0 i i (zero_add i)

/-- The degree-zero inclusion in the recorded principal Koszul complex.
Source: blueprint sk-lem-sp-tower (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev koszulRight (m : ℕ) : unit R ⟶ (principalKoszul R t m).X 0 :=
  singleIn (unit R) ≫ (CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (Modules R) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))).f 0

/-- The degree-minus-one inclusion in the recorded principal Koszul complex.
Source: blueprint sk-lem-sp-tower (blueprint: def-sp-regular-scalar-quotient-notation). -/
abbrev koszulLeft (m : ℕ) : unit R ⟶ (principalKoszul R t m).X (-1) :=
  singleIn (unit R) ≫ (CochainComplex.mappingCone.inl
    ((CochainComplex.singleFunctor (Modules R) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))).v 0 (-1) rfl

end CategoryTheory.RegularScalarQuotient
