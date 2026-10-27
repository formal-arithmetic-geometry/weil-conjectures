/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.FlatScalarExtensionHomologyAdjunct
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import Sheaf.Algebra.Homology.BalancedDerivedTensorModel
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat

/-! # Flat change of a diagram of rings and derived tensor cohomology

Source: Stacks Project, More on Algebra, Tags 0DJD and 08HW
(blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology).

The ordinary derived extension is the published K-flat universal pair. The comparison
is the transpose of the two scalar-extension units, with the restriction composition
isomorphisms of the commutative diagram. Thus its formula fixes the map, not just its
source and target. Cohomology lifts retain both commuting factor actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat.FlatRingDiagram

/-- The normalization of a derived scalar adjunction by the ordinary unit on complexes.
The counit is the existing universal K-flat computation map. It is invertible on every
K-flat representative, so this equation also fixes the units on all such representatives.
Source: Stacks 0DJD, proof, and 07A6
(blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def UnitNormalized {E F : Type u} [CommRing E] [CommRing F] (f : E →+* F)
    (a : ordinaryDerivedExtendScalars f ⊣ derivedRestrictScalars f) : Prop :=
  ∀ P : CochainComplex (ModuleCat.{u} E) ℤ,
    a.unit.app (DerivedCategory.Q.obj P) ≫
        (derivedRestrictScalars f).map ((ordinaryDerivedChangeOfRings f).counit.app P) ≫
        (restrictScalars f).mapDerivedCategoryFactors.hom.app
          (((extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((extendRestrictScalarsAdj f).unit.mapHomologicalComplex (.up ℤ)).app P)

variable (R A B R₁ A₁ B₁ : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing R₁] [CommRing A₁] [CommRing B₁]
  [Algebra R A] [Algebra R B] [Algebra R R₁]
  [Algebra A A₁] [Algebra B B₁] [Algebra R₁ A₁] [Algebra R₁ B₁]
  [Algebra R A₁] [Algebra R B₁]
  [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
  [IsScalarTower R B B₁] [IsScalarTower R R₁ B₁]

/-- The induced map on the two tensor rings, on pure tensors `a ⊗ b ↦ a₁ ⊗ b₁`.
Source: Stacks 0DJD and 08HW
(blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def tensorRingMap : A ⊗[R] B →+* A₁ ⊗[R₁] B₁ :=
  Algebra.TensorProduct.mapRingHom (algebraMap R R₁) (algebraMap A A₁) (algebraMap B B₁)
    ((IsScalarTower.algebraMap_eq R A A₁).symm.trans
      (IsScalarTower.algebraMap_eq R R₁ A₁))
    ((IsScalarTower.algebraMap_eq R B B₁).symm.trans
      (IsScalarTower.algebraMap_eq R R₁ B₁))

/-- The compatible restriction square, through the common map `R → A₁`.
Source: Stacks 0DJD, proof (blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def restrictionSquare :
    derivedRestrictScalars (algebraMap A A₁) ⋙ derivedRestrictScalars (algebraMap R A) ≅
      derivedRestrictScalars (algebraMap R₁ A₁) ⋙ derivedRestrictScalars (algebraMap R R₁) :=
  derivedRestrictScalarsCompIso (IsScalarTower.algebraMap_eq R A A₁) ≪≫
    (derivedRestrictScalarsCompIso (IsScalarTower.algebraMap_eq R R₁ A₁)).symm

/-- The source derived tensor, retaining the B-action, before taking cohomology.
Source: Stacks 0DJD (blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def sourceDerived : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  derivedRestrictScalars (algebraMap R A) ⋙ ordinaryDerivedExtendScalars (algebraMap R B)

/-- The target derived tensor as the four functors in the proof of Stacks 0DJD.
Source: Stacks 0DJD (blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def targetDerived : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B₁) :=
  ordinaryDerivedExtendScalars (algebraMap A A₁) ⋙ sourceDerived R₁ A₁ B₁

/-- The unit map around the diagram, prior to transposition along `R → B`.
Source: Stacks 0DJD, the canonical maps of 08HW
(blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def unitAround
    (a : ordinaryDerivedExtendScalars (algebraMap A A₁) ⊣
      derivedRestrictScalars (algebraMap A A₁))
    (b : ordinaryDerivedExtendScalars (algebraMap R₁ B₁) ⊣
      derivedRestrictScalars (algebraMap R₁ B₁)) :
    derivedRestrictScalars (algebraMap R A) ⟶
      targetDerived A R₁ A₁ B₁ ⋙ derivedRestrictScalars (algebraMap B B₁) ⋙
        derivedRestrictScalars (algebraMap R B) :=
  Functor.whiskerRight a.unit (derivedRestrictScalars (algebraMap R A)) ≫
    Functor.whiskerLeft (ordinaryDerivedExtendScalars (algebraMap A A₁))
      (restrictionSquare R A R₁ A₁).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (ordinaryDerivedExtendScalars (algebraMap A A₁) ⋙
        derivedRestrictScalars (algebraMap R₁ A₁)) b.unit)
      (derivedRestrictScalars (algebraMap R R₁)) ≫
    Functor.whiskerLeft (targetDerived A R₁ A₁ B₁)
      (restrictionSquare R B R₁ B₁).inv

/-- The canonical derived comparison, the transpose of the scalar units around the square.
Source: Stacks 0DJD, proof (blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def comparison
    (r : ordinaryDerivedExtendScalars (algebraMap R B) ⊣
      derivedRestrictScalars (algebraMap R B))
    (a : ordinaryDerivedExtendScalars (algebraMap A A₁) ⊣
      derivedRestrictScalars (algebraMap A A₁))
    (b : ordinaryDerivedExtendScalars (algebraMap R₁ B₁) ⊣
      derivedRestrictScalars (algebraMap R₁ B₁)) :
    sourceDerived R A B ⟶
      targetDerived A R₁ A₁ B₁ ⋙ derivedRestrictScalars (algebraMap B B₁) :=
  ((r.whiskerRight (DerivedCategory (ModuleCat.{u} A))).homEquiv _ _).symm
    (unitAround R A B R₁ A₁ B₁ a b)

/-- The comparison on cohomology, using the canonical exact-restriction identification.
Source: Stacks 0DJD, proof (blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology). -/
def cohomologyComparison
    (r : ordinaryDerivedExtendScalars (algebraMap R B) ⊣
      derivedRestrictScalars (algebraMap R B))
    (a : ordinaryDerivedExtendScalars (algebraMap A A₁) ⊣
      derivedRestrictScalars (algebraMap A A₁))
    (b : ordinaryDerivedExtendScalars (algebraMap R₁ B₁) ⊣
      derivedRestrictScalars (algebraMap R₁ B₁)) (i : ℤ) :
    sourceDerived R A B ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⟶
      targetDerived A R₁ A₁ B₁ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) i ⋙
        restrictScalars (algebraMap B B₁) :=
  Functor.whiskerRight (comparison R A B R₁ A₁ B₁ r a b)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i) ≫
    Functor.whiskerLeft (targetDerived A R₁ A₁ B₁)
      ((restrictScalars (algebraMap B B₁)).mapDerivedCategoryHomologyFunctorIso i).inv

/-- Canonical flat ring-diagram comparison on unbounded derived tensor cohomology.
Source: Stacks Project, More on Algebra, Tags 0DJD and 08HW
(blueprint: lem-sfb-flat-ring-diagram-tensor-cohomology).

Proof:
1. Set A₀ = A tensor_R R₁ and B₀ = R₁ tensor_R B. Flat tensor exactness
   (lem-weil-pbc-flat-tensor-exact) and flat transitivity (lem-pc-module-flat-transitive)
   make A → A₁ flat. Identify D₀ = A₁ tensor_R B = D tensor_A A₁ and
   D₁ = D₀ tensor_B₀ B₁ by their factor generators.
2. Choose unbounded flat-term K-flat models P → M and F → B[0]
   (lem-pc-source-module-kflat-resolution). Scalar extension preserves K-flatness
   (lem-pc-kflat-extension-of-scalars). Flat cohomology extension
   (lem-pc-flat-scalar-extension-homology-adjunct) shows F tensor_R R₁ → B₀[0]
   is a resolution. The universal K-flat counit computes derived extension
   (lem-pc-kflat-scalar-extension-counit).
3. Balanced models (lem-pc-balanced-derived-tensor-model) give total complexes
   C = Tot(P tensor_R F) and C₀ = Tot((P tensor_A A₁) tensor_R₁ (F tensor_R R₁)).
   The chain isomorphism C₀ → C tensor_A A₁ sends (p tensor a) tensor (f tensor r)
   to (p tensor f) tensor ar. Its inverse adjoins 1 in the R₁ factor. Balancing,
   the signed total differential, and direct-sum inclusions verify these formulas.
   Functoriality in F (lem-pc-derived-tensor-second-factor-functor) preserves the
   B-action, so the cohomology identification is D₀-linear.
4. Flat homology extension identifies H(C) tensor_A A₁ with H(C tensor_A A₁).
   The balancing identification T tensor_D D₀ = T tensor_A A₁ sends
   t tensor (a tensor b) to bt tensor a. Together these give the D₀-linear unit map.
5. For R₁ → B₀ → B₁, successive normalized derived extension
   (lem-sfb-successive-derived-quotient-normalization) is represented by
   (x tensor s) tensor t ↦ x tensor st. K-flat scalar extension and its counit
   compute it. Flatness of B₁ over B₀ and flat homology extension give the
   B₁-linear cohomology identification. Naturality in A₁ multiplication gives
   D₁-linearity without any flatness over R₁.
6. Tensor the D₀-isomorphism with B₁ and rebracket balanced tensors. This yields
   the displayed D₁-linear isomorphism.
7. On representatives all maps use p ↦ p tensor 1 and f ↦ f tensor 1.
   The normalized scalar adjunction (lem-pur-sheaf-ring-derived-coefficient-adjunction)
   on the singleton site (lem-weil-pbc-singleton-site-module-comparison), and the
   unit identity for successive extension, identify them with unitAround and its
   transpose comparison. The linear extension is uniquely fixed by
   d tensor t ↦ d gamma(t). Balanced-model naturality and the explicit formulas
   commute with augmentations and changes of K-flat models. Bounded-above free
   resolutions are included by lem-pc-module-bounded-flat-kflat. Thus naturality
   on the derived category also expresses compatibility with every resolution. -/
theorem flat_ring_diagram_tensor_cohomology
    (hR : (algebraMap R R₁).Flat)
    (hA : (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R A A₁) (IsScalarTower.toAlgHom R R₁ A₁)
      (fun _ _ ↦ Commute.all _ _)).toRingHom.Flat)
    (hB : (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R R₁ B₁) (IsScalarTower.toAlgHom R B B₁)
      (fun _ _ ↦ Commute.all _ _)).toRingHom.Flat) :
    ∃ (r : ordinaryDerivedExtendScalars (algebraMap R B) ⊣
        derivedRestrictScalars (algebraMap R B))
      (a : ordinaryDerivedExtendScalars (algebraMap A A₁) ⊣
        derivedRestrictScalars (algebraMap A A₁))
      (b : ordinaryDerivedExtendScalars (algebraMap R₁ B₁) ⊣
        derivedRestrictScalars (algebraMap R₁ B₁)),
      UnitNormalized (algebraMap R B) r ∧ UnitNormalized (algebraMap A A₁) a ∧
      UnitNormalized (algebraMap R₁ B₁) b ∧
      ∀ i : ℤ,
      ∃ (S : DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} (A ⊗[R] B))
        (T : DerivedCategory (ModuleCat.{u} A₁) ⥤ ModuleCat.{u} (A₁ ⊗[R₁] B₁))
        (eS : S ⋙ restrictScalars
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom ≅
          sourceDerived R A B ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i)
        (eT : T ⋙ restrictScalars
          (Algebra.TensorProduct.includeRight : B₁ →ₐ[R₁] A₁ ⊗[R₁] B₁).toRingHom ≅
          sourceDerived R₁ A₁ B₁ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) i)
        (c : S ⋙ extendScalars (tensorRingMap R A B R₁ A₁ B₁) ⟶
          ordinaryDerivedExtendScalars (algebraMap A A₁) ⋙ T),
        IsIso c ∧
        (∀ (M : DerivedCategory (ModuleCat.{u} A)) (x : S.obj M) (s : A),
          eS.hom.app M ((s ⊗ₜ[R] (1 : B)) • x) =
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              ((sourceDerived R A B).map (s • 𝟙 M)) (eS.hom.app M x)) ∧
        (∀ (N : DerivedCategory (ModuleCat.{u} A₁)) (x : T.obj N) (s : A₁),
          eT.hom.app N ((s ⊗ₜ[R₁] (1 : B₁)) • x) =
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) i).map
              ((sourceDerived R₁ A₁ B₁).map (s • 𝟙 N)) (eT.hom.app N x)) ∧
        ∀ (M : DerivedCategory (ModuleCat.{u} A)) (x : S.obj M),
          eT.hom.app ((ordinaryDerivedExtendScalars (algebraMap A A₁)).obj M)
              (c.app M ((1 : A₁ ⊗[R₁] B₁) ⊗ₜ[A ⊗[R] B,
                tensorRingMap R A B R₁ A₁ B₁] x)) =
            (cohomologyComparison R A B R₁ A₁ B₁ r a b i).app M (eS.hom.app M x) := by
  sorry

end ModuleCat.FlatRingDiagram
