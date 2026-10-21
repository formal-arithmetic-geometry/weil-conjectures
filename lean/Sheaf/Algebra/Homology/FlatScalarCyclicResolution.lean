/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Paper.ProjectionMateExact
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Two-term scalar quotient resolutions after flat sheaf extension

Source: Stacks Project, Cohomology on Sites, Tags 06YQ and 06YU;
Modules on Sites, Tags 03EI and 03ER
(blueprint: lem-sfb-flat-scalar-cyclic-resolution).

The cone of scalar multiplication on the degree-zero ring complex is the displayed
complex in degrees -1 and 0. Its quotient is the sheaf cokernel, and the augmentation
is specified by its restriction to the degree-zero summand.
-/

@[expose] public section

universe u v r w

set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (A : Type r) [CommRing A]
  [HasWeakSheafify J CommRingCat.{r}]

/-- The existing constant commutative ring sheaf.
Source: Stacks Tag 093I (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable abbrev scalarCyclicBase := (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)

variable {J}

/-- Forget commutativity for the existing module-sheaf category.
Source: Stacks Tag 03CY (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable abbrev scalarCyclicRing (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

variable {A} (R : Sheaf J CommRingCat.{r})
  (α : scalarCyclicBase J A ⟶ R)

/-- The constant presheaf map adjoint to the given constant-sheaf algebra structure.
Source: Stacks Tags 03CY, 093I (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicPresheafMap :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj :=
  (sheafificationAdjunction J CommRingCat.{r}).homEquiv _ _ α

/-- Multiplication by the constant scalar, constructed from its compatible sections.
Source: Stacks Tags 03CY, 03ER (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicMultiplication (a : A) :
    unit (scalarCyclicRing R) ⟶ unit (scalarCyclicRing R) :=
  (unit (scalarCyclicRing R)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (scalarCyclicPresheafMap R α).app U a)
      (fun U V f ↦ by
        exact congrArg (fun g : CommRingCat.of A ⟶ R.obj.obj V ↦ g a)
          ((scalarCyclicPresheafMap R α).naturality f).symm))

/-- The displayed two-term complex: the cone of `a : R[0] → R[0]`.
Its differential from degree -1 to degree 0 is multiplication by `a`.
Source: Stacks Tags 06YQ, 06YU (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicComplex (a : A) :
    CochainComplex (SheafOfModules.{r} (scalarCyclicRing R)) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor _ 0).map (scalarCyclicMultiplication R α a))

/-- The quotient sheaf `R/aR`, as a module sheaf cokernel.
Source: Stacks Tag 03DA (blueprint: lem-sfb-flat-scalar-cyclic-resolution). -/
noncomputable def scalarCyclicQuotient (a : A) : SheafOfModules.{r} (scalarCyclicRing R) :=
  cokernel (scalarCyclicMultiplication R α a)

/-- A flat algebra over a constant domain has the indicated scalar quotient resolution.
The augmentation restricts to the cokernel projection on the degree-zero ring summand;
its source is the specified two-term complex, rather than an unspecified resolution.
The last clause computes derived tensor with the quotient for every unbounded complex.
Source: Stacks Tags 03EI, 03ER, 06YQ and 06YU
(blueprint: lem-sfb-flat-scalar-cyclic-resolution).

Proof:
1. For `a ≠ 0`, multiplication by `a` is injective on the domain `A`. Sheafify the
   constant presheaf monomorphism using exact module sheafification (03EI), as in
   `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`. This gives a monomorphism
   on the constant ring sheaf, without an enough-points hypothesis.
2. Tensor with the flat algebra `R`. By `def-pc-flat-sheaf-modules` this functor is exact.
   Identify the tensor of the base ring with `R` using the tensor unit; the transported
   map is the multiplication defined above, so it is monic and sectionwise injective.
3. The cokernel projection gives the augmentation from the cone. Its cohomology is
   zero in degree -1 by injectivity, the quotient in degree zero, and zero otherwise.
   Thus the augmentation is a quasi-isomorphism (`def-pc-quasi-iso-modules`).
4. Both terms are the free rank-one `R`-module, hence flat over `R`; zero terms are flat.
   The same applies to `R[0]`, using the tensor unit (`def-pur-sheaf-tensor-product`).
5. Both complexes vanish above degree zero. Apply `lem-pc-bounded-above-flat-kflat-site`
   (06YQ). Together with Step 3 this is a K-flat resolution (`def-pc-kflat-complex`).
6. Compute derived tensor by this one K-flat factor, as in the derived-tensor clause of
   `lem-weil-pbc-ringed-projection-mate-exact`, or directly the construction preceding
   Stacks 06YU. Total tensor with the cone therefore represents tensor with `R/aR`.
-/
theorem flat_scalar_cyclic_resolution [IsDomain A]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (scalarCyclicRing R))]
    (hflat : IsFlatOnSite (J := J) (R := scalarCyclicBase J A)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
        (unit (scalarCyclicRing R))))
    (a : A) (ha : a ≠ 0) :
    Mono (scalarCyclicMultiplication R α a) ∧
      ∃ ε : scalarCyclicComplex R α a ⟶
          (CochainComplex.singleFunctor _ 0).obj (scalarCyclicQuotient R α a),
        CochainComplex.mappingCone.inr
            ((CochainComplex.singleFunctor _ 0).map (scalarCyclicMultiplication R α a)) ≫ ε =
          (CochainComplex.singleFunctor _ 0).map
            (cokernel.π (scalarCyclicMultiplication R α a)) ∧
        CochainComplex.IsKFlatResolutionIndependentCoefficients ε ∧
        CochainComplex.IsKFlatIndependentCoefficients
          ((CochainComplex.singleFunctor _ 0).obj (unit (scalarCyclicRing R))) ∧
        ∀ M : CochainComplex (SheafOfModules.{r} (scalarCyclicRing R)) ℤ,
          Nonempty ((siteDerivedTensorIndependentCoefficients J R).obj
              (DerivedCategory.Q.obj M,
                DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
                  (scalarCyclicQuotient R α a))) ≅
            DerivedCategory.Q.obj (CochainComplex.mapBifunctor M
              (scalarCyclicComplex R α a) (curriedTensor _))) := by
  sorry

end SheafOfModules
