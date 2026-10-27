module

public import Sheaf.RingTheory.MarkedFlatAlgebraDeformations
public import Sheaf.RingTheory.NaiveCotangentComparison
public import Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Objects in the completed local deformation comparison

Source: Stacks Project, Tags 0DYV, 0GPU, 0GPW, 0AJR and 0GAE, with the
localized-polynomial continuous-presentation interpretation in the parent node
(blueprint: def-sfb-completed-local-deformation-objects).

The groupoids are full subcategories of the existing marked deformation groupoids.
The conormal complexes are cones on the existing conormal differential. The completed
cone uses extension of scalars on both terms and its differential. Relation-map
normalization specifies the classification independently of any choice of lift.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ArtinDeformation
open scoped ChangeOfRings TensorProduct

namespace Algebra.FlatDeformation

variable {k : Type u} [Field k]

/-- The dual-number test, with its standard augmentation.
Source: Stacks, Tag 0GPU (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev dualTest (k : Type u) [Field k] : TestCategory k k :=
  squareZeroTest (R := k) (k := k) k

/-- The dual-number infinitesimal generator.
Source: Stacks, Tag 0GPU (blueprint: def-sfb-completed-local-deformation-objects). -/
def epsilon : ring (dualTest k) := TrivSqZeroExt.inr (1 : k)

/-- Maximal-ideal completion, retaining the standard algebra structure.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev localCompletion (A : Type u) [CommRing A] [IsLocalRing A] :=
  AdicCompletion (IsLocalRing.maximalIdeal A) A

/-- The complete Noetherian local objects. No residue-field equality with k is imposed.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-completed-local-deformation-objects). -/
def IsContinuous {B : Type u} [CommRing B] [Algebra k B]
    {R : TestCategory k k} (Q : Groupoid B R) : Prop :=
  ∃ h : IsLocalRing (algebra Q), IsNoetherianRing (algebra Q) ∧
    IsAdicComplete (@IsLocalRing.maximalIdeal (algebra Q) _ h) (algebra Q)

/-- Complete local marked deformations; marked isomorphisms are automatically local,
and hence continuous for the maximal-ideal-adic topologies.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev ContinuousGroupoid (B : Type u) [CommRing B] [Algebra k B]
    (R : TestCategory k k) := ObjectProperty.FullSubcategory
      (fun Q : Groupoid B R ↦ IsContinuous Q)

/-- All first-order algebraic deformation classes, modulo marked isomorphism.
Source: Stacks, Tag 0GPU (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev FirstOrderClasses (B : Type u) [CommRing B] [Algebra k B] :=
  Quotient (isIsomorphicSetoid (Groupoid B (dualTest k)))

/-- All continuous first-order classes, modulo continuous marked isomorphism.
Source: Stacks, Tags 0GPU and 0DYV
(blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev ContinuousClasses (B : Type u) [CommRing B] [Algebra k B] :=
  Quotient (isIsomorphicSetoid (ContinuousGroupoid B (dualTest k)))

/-- A finite localized polynomial presentation, using the existing presentation record.
Source: Stacks, Tags 08RB and 0AJR
(blueprint: def-sfb-completed-local-deformation-objects). -/
def IsFinitePolynomial {A : Type u} [CommRing A] [Algebra k A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) : Prop :=
  ∃ (r : ℕ) (a : MvPolynomial (Fin r) k →+* P.ring)
    (W : Submonoid (MvPolynomial (Fin r) k)),
    (∀ x : k, a (MvPolynomial.C x) = P.base x) ∧
      (letI := a.toAlgebra; IsLocalization W P.ring)

/-- The two-term conormal complex in degrees minus one and zero, in cone coordinates.
Source: Stacks, Tag 0GPU (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev conormalComplex {f : Arrow CommRingCat.{u}}
    (P : CotangentResolution.Naive.Presentation f) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (ModuleCat f.right) 0).map
    (CotangentResolution.Naive.differential P))

/-- The scalar-extended conormal differential.
Source: Stacks, Tags 0AJR and 0DYV
(blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev completedDifferential {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :=
  (ModuleCat.extendScalars (algebraMap A (localCompletion A))).map
    (CotangentResolution.Naive.differential P)

/-- The completed complex, with termwise tensor and its induced differential.
Source: Stacks, Tags 0AJR and 0GAE
(blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev completedConormalComplex {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor
    (ModuleCat (localCompletion A)) 0).map (completedDifferential P))

/-- The ordinary derived Hom, with the coefficient module in degree zero before shift.
Source: Stacks, Tag 0GPU (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev TangentHom {A : Type u} [CommRing A] [Algebra k A]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :=
  (DerivedCategory.Q (C := ModuleCat.{u} A)).obj (conormalComplex P) ⟶
    ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
      (ModuleCat.of A A))⟦(1 : ℤ)⟧

/-- The continuous derived Hom uses completed conormal modules, not ordinary
Kähler differentials of the completed ring.
Source: Stacks, Tags 0GPU and 0AJR
(blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev CompletedTangentHom {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (localCompletion A))]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :=
  DerivedCategory.Q.obj (completedConormalComplex P) ⟶
    ((DerivedCategory.singleFunctor (ModuleCat (localCompletion A)) 0).obj
      (ModuleCat.of (localCompletion A) (localCompletion A)))⟦(1 : ℤ)⟧

/-- Normalization of an algebraic relation map. Multiplication by epsilon identifies
the marked special fibre with the square-zero kernel, without choosing a section.
Source: Stacks, Tag 0GPU (blueprint: def-sfb-completed-local-deformation-objects). -/
def IsRelationMap {A : Type u} [CommRing A] [Algebra k A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (Q : Groupoid A (dualTest k))
    (φ : CotangentResolution.Naive.conormal P ⟶ ModuleCat.of A A) : Prop :=
  ∃ a : P.ring →+* algebra Q,
    (∀ c : k, a (P.base c) = algebraMap k (algebra Q) c) ∧
    (∀ x : P.ring, marking Q (a x) = P.augmentation x) ∧
    ∀ (j : RingHom.ker P.augmentation.hom) (e : algebra Q),
      marking Q e = φ (CotangentResolution.Naive.kernelClass P j) →
        a j = scalar Q epsilon * e

/-- Normalization after completion, evaluated on the dense algebraic relations.
Source: Stacks, Tags 0GPU, 0GPW and 0DYV
(blueprint: def-sfb-completed-local-deformation-objects). -/
def IsCompletedRelationMap {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (Q : Groupoid (localCompletion A) (dualTest k))
    (φ : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
      (CotangentResolution.Naive.conormal P) ⟶
        ModuleCat.of (localCompletion A) (localCompletion A)) : Prop :=
  ∃ a : P.ring →+* algebra Q,
    (∀ c : k, a (P.base c) = algebraMap k (algebra Q) c) ∧
    (∀ x : P.ring, marking Q (a x) =
      algebraMap A (localCompletion A) (P.augmentation x)) ∧
    ∀ (j : RingHom.ker P.augmentation.hom) (e : algebra Q),
      marking Q e = φ ((1 : localCompletion A) ⊗ₜ[A,algebraMap A (localCompletion A)]
        CotangentResolution.Naive.kernelClass P j) → a j = scalar Q epsilon * e


/-- A comparison of conormal differentials induced by a map of presentations.
Source: Stacks, Tags 0GAE and 08RB
(blueprint: def-sfb-completed-local-deformation-objects). -/
structure ConormalSquare {f : Arrow CommRingCat.{u}}
    {P P' : CotangentResolution.Naive.Presentation f}
    (h : CotangentResolution.Naive.PresentationMap (𝟙 f) P P') where
  negOne : CotangentResolution.Naive.conormal P ⟶ CotangentResolution.Naive.conormal P'
  zero : CotangentResolution.Naive.differentials P ⟶ CotangentResolution.Naive.differentials P'
  kernel_formula : ∀ (j : RingHom.ker P.augmentation.hom)
    (j' : RingHom.ker P'.augmentation.hom), (j' : P'.ring) = h.map j →
      negOne (CotangentResolution.Naive.kernelClass P j) =
        CotangentResolution.Naive.kernelClass P' j'
  tensor_formula : ∀ (b : f.right) (x : P.ring),
    zero (CotangentResolution.Naive.tensorGenerator P b x) =
      CotangentResolution.Naive.tensorGenerator P' b (h.map x)
  commutes : CotangentResolution.Naive.differential P ≫ zero =
    negOne ≫ CotangentResolution.Naive.differential P'

/-- The comparison of the two-term complexes specified on conormal classes and tensors.
Source: Stacks, Tag 08RB
(blueprint: def-sfb-completed-local-deformation-objects). -/
def ConormalSquare.chainMap {f : Arrow CommRingCat.{u}}
    {P P' : CotangentResolution.Naive.Presentation f}
    {h : CotangentResolution.Naive.PresentationMap (𝟙 f) P P'} (s : ConormalSquare h) :=
  DerivedCategory.twoTermSquareMap (CotangentResolution.Naive.differential P)
    (CotangentResolution.Naive.differential P') s.negOne s.zero s.commutes

/-- Tensor extension of a conormal comparison, on its actual terms and differential.
Source: Stacks, Tags 00MB and 0GAE
(blueprint: def-sfb-completed-local-deformation-objects). -/
def ConormalSquare.completedChainMap {A : Type u} [CommRing A] [Algebra k A]
    [IsLocalRing A]
    {P P' : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))}
    {h : CotangentResolution.Naive.PresentationMap (𝟙 _) P P'} (s : ConormalSquare h) :=
  DerivedCategory.twoTermSquareMap (completedDifferential P) (completedDifferential P')
    ((ModuleCat.extendScalars (algebraMap A (localCompletion A))).map s.negOne)
    ((ModuleCat.extendScalars (algebraMap A (localCompletion A))).map s.zero)
    (((ModuleCat.extendScalars (algebraMap A (localCompletion A))).map_comp _ _).symm.trans
      ((congrArg (ModuleCat.extendScalars (algebraMap A (localCompletion A))).map
        s.commutes).trans
          ((ModuleCat.extendScalars (algebraMap A (localCompletion A))).map_comp _ _)))

/-- Scalar extension on relation maps, fixed on every simple conormal tensor.
Source: Stacks, Tag 0GPW (blueprint: def-sfb-completed-local-deformation-objects). -/
def IsExtendedRelationMap {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (φ : CotangentResolution.Naive.conormal P ⟶ ModuleCat.of A A)
    (ψ : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
      (CotangentResolution.Naive.conormal P) ⟶
        ModuleCat.of (localCompletion A) (localCompletion A)) : Prop :=
  ∀ (b : localCompletion A) (j : RingHom.ker P.augmentation.hom),
    ψ (b ⊗ₜ[A,algebraMap A (localCompletion A)]
      CotangentResolution.Naive.kernelClass P j) =
        b * algebraMap A (localCompletion A) (φ (CotangentResolution.Naive.kernelClass P j))

/-- The completion of the presentation at the inverse image of the maximal ideal.
Source: Stacks, Tag 0DYV (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev completedPresentationRing {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) : CommAlgCat.{u} k :=
  letI : Algebra k P.ring := P.base.hom.toAlgebra
  CommAlgCat.of k (AdicCompletion
    ((IsLocalRing.maximalIdeal A).comap P.augmentation.hom) P.ring)

/-- The coefficient algebra structure retained by the bundled completed presentation.
Source: Stacks, Tag 0AJR (blueprint: def-sfb-completed-local-deformation-objects). -/
instance completedPresentationAlgebra {A : Type u} [CommRing A] [Algebra k A]
    [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :
    Algebra k (completedPresentationRing (k := k) P) :=
  CommAlgCat.algebra (completedPresentationRing (k := k) P)

/-- The continuous differential module before passage to the completed quotient.
This is completion of polynomial differentials, not ordinary differentials of completion.
Source: Stacks, Tag 0AJR (blueprint: def-sfb-completed-local-deformation-objects). -/
abbrev completedPresentationDifferentials {A : Type u} [CommRing A] [Algebra k A]
    [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :
    ModuleCat.{u} (completedPresentationRing P) :=
  letI : Algebra k P.ring := P.base.hom.toAlgebra
  ModuleCat.of _ (AdicCompletion ((IsLocalRing.maximalIdeal A).comap P.augmentation.hom)
    (KaehlerDifferential k P.ring))

/-- Restriction of the canonical completed-module action to k.
Source: Stacks, Tag 0AJR (blueprint: def-sfb-completed-local-deformation-objects). -/
instance completedDifferentialsModule {A : Type u} [CommRing A] [Algebra k A]
    [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :
    Module k (completedPresentationDifferentials (k := k) P) :=
  Module.restrictScalars k (completedPresentationRing (k := k) P)
    (completedPresentationDifferentials (k := k) P)

/-- The restricted completed differential action is the scalar-tower action.
Source: Stacks, Tag 0AJR (blueprint: def-sfb-completed-local-deformation-objects). -/
instance completedDifferentialsTower {A : Type u} [CommRing A] [Algebra k A]
    [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) :
    IsScalarTower k (completedPresentationRing (k := k) P)
      (completedPresentationDifferentials (k := k) P) :=
  IsScalarTower.restrictScalars k (completedPresentationRing (k := k) P)
    (completedPresentationDifferentials (k := k) P)

/-- The dense map of polynomial differentials into their completion.
Source: Stacks, Tag 0AJR (blueprint: def-sfb-completed-local-deformation-objects). -/
def completedDx {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (x : P.ring) : completedPresentationDifferentials P :=
  letI : Algebra k P.ring := P.base.hom.toAlgebra
  AdicCompletion.of ((IsLocalRing.maximalIdeal A).comap P.augmentation.hom)
    (KaehlerDifferential k P.ring) (KaehlerDifferential.D k P.ring x)

end Algebra.FlatDeformation
