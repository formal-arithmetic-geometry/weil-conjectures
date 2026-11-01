/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PointFibreDerivedTensorBasic
public import WeilConjectures.CategoryTheory.DerivedCategory.Picard.DerivedTensorSecondFactorFunctor
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit

/-! # Condensed point tensor comparison and coefficient reduction data

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
finite reduction and scalar extension; Stacks Tag 07A4, lemma-pullback-tensor-product
(blueprint: def-sf-point-fibre-tensor-reduction).

The only constructions reused from PointFibreDerivedTensorScalar are its ordinary
module derived extension and ordinary scalar tensor data. No legacy coefficient
category, completion, or common-stage tensor enters the definitions below.

## Main definitions

* `NormalizedScalarData`: normalized ordinary derived scalar monoidality.
* `PointData`: coherent tensor comparisons for exact point evaluation.
* `ReductionData`: canonical coefficient-change comparison and its two squares.
* `FiniteReductionData`: specialization to the actual discrete quotient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

-- Prefer the universe-polymorphic size transport to legacy max-universe instances.
attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction

variable (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]

/-- The ambient termwise point evaluation of the exact sections functor. It is
available on a tensor object without assuming constructible tensor closure.
Source: exact point sections and latest blueprint compact-support specialization
(blueprint: def-sf-point-fibre-tensor-reduction). -/
abbrev fiber := (CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategory

/-- The coefficient map on actual singleton sections, obtained by reconstructing
commutative ring sheaves and evaluating the given morphism.
Source: latest blueprint coefficient change, a(*)
(blueprint: def-sf-point-fibre-tensor-reduction). -/
def scalarMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    condensedScalarRing Λ.X →+* condensedScalarRing Λ'.X :=
  (InternalAbelianSheafModule.commMonToRing.map
    (((Monoidal.commMonFunctorCategoryEquivalence _ _).functor.map
      ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapCommMon.map a)).app
        (op (⊤_ Profinite.{u})))).hom

/-- Natural point tensor isomorphisms, their Koszul symmetry, associativity and
both unit equations for the fixed ambient tensor. Membership arguments only index
the comparisons: they do not construct a tensor or change the ambient functor.
Intermediate membership witnesses make the associativity equation meaningful
without installing a second tensor on a full subcategory.
The unit representative identifies a coefficient section with its singleton scalar.
Source: latest blueprint relative product coherence at Spec k; Stacks 07A4
(blueprint: def-sf-point-fibre-tensor-reduction). -/
structure PointData where
  tensorIso (M N : CohomologyTransport.D Λ.X (Spec (.of k)))
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    (fiber Λ k).obj (M ⊗ N) ≅ (fiber Λ k).obj M ⊗ (fiber Λ k).obj N
  naturality {M M' N N' : CohomologyTransport.D Λ.X (Spec (.of k))}
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hM' : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M')
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N)
    (hN' : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N')
    (f : M ⟶ M') (g : N ⟶ N') :
    (fiber Λ k).map (f ⊗ₘ g) ≫ (tensorIso M' N' hM' hN').hom =
      (tensorIso M N hM hN).hom ≫ ((fiber Λ k).map f ⊗ₘ (fiber Λ k).map g)
  associativity (M N P : CohomologyTransport.D Λ.X (Spec (.of k)))
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N)
    (hP : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) P)
    (hMN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) (M ⊗ N))
    (hNP : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) (N ⊗ P)) :
    (tensorIso (M ⊗ N) P hMN hP).hom ≫
        ((tensorIso M N hM hN).hom ▷ (fiber Λ k).obj P) ≫
        (α_ ((fiber Λ k).obj M) ((fiber Λ k).obj N) ((fiber Λ k).obj P)).hom =
      (fiber Λ k).map (α_ M N P).hom ≫ (tensorIso M (N ⊗ P) hM hNP).hom ≫
        ((fiber Λ k).obj M ◁ (tensorIso N P hN hP).hom)
  symmetry (M N : CohomologyTransport.D Λ.X (Spec (.of k)))
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    (fiber Λ k).map
        ((_root_.DerivedCategory.braidedCategory'.{u + 1}
          (ModuleRingedComparison.internalModules Λ.X (Spec (.of k)))).braiding M N).hom ≫
        (tensorIso N M hN hM).hom =
      (tensorIso M N hM hN).hom ≫
        ((_root_.DerivedCategory.braidedCategory'.{u + 1}
          (ModuleCat.{u + 1} (condensedScalarRing Λ.X))).braiding
          ((fiber Λ k).obj M) ((fiber Λ k).obj N)).hom
  unitIso : (fiber Λ k).obj (𝟙_ _) ≅ 𝟙_ _
  left_unit (M : CohomologyTransport.D Λ.X (Spec (.of k)))
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hOne : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) (𝟙_ _)) :
    (tensorIso (𝟙_ _) M hOne hM).hom ≫ (unitIso.hom ▷ (fiber Λ k).obj M) ≫
        (λ_ ((fiber Λ k).obj M)).hom = (fiber Λ k).map (λ_ M).hom
  right_unit (M : CohomologyTransport.D Λ.X (Spec (.of k)))
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hOne : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) (𝟙_ _)) :
    (tensorIso M (𝟙_ _) hM hOne).hom ≫ ((fiber Λ k).obj M ◁ unitIso.hom) ≫
        (ρ_ ((fiber Λ k).obj M)).hom = (fiber Λ k).map (ρ_ M).hom
  unitModel :
    ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapHomologicalComplex (.up ℤ)).obj
        (𝟙_ (CochainComplex (ModuleRingedComparison.internalModules Λ.X (Spec (.of k))) ℤ)) ≅
      𝟙_ (CochainComplex (ModuleCat.{u + 1} (condensedScalarRing Λ.X)) ℤ)
  unitModel_apply (r : condensedScalarRing Λ.X) :
    (unitModel.inv.f 0) r = CohomologyTransport.scalarMap Λ.X (Spec (.of k)) r
  unit_normalization :
    (fiber Λ k).map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      (CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategoryFactors.hom.app
        (𝟙_ (CochainComplex (ModuleRingedComparison.internalModules Λ.X (Spec (.of k))) ℤ)) ≫
      DerivedCategory.Q.map unitModel.hom =
    unitIso.hom ≫ Functor.LaxMonoidal.ε DerivedCategory.Q


variable {Λ Λ' : ScalarSixRing.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
