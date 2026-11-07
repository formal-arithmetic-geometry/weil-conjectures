/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import Submission.WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import Submission.WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Tensor and composition coherence of ringed-topos projection maps

Source: Stacks Project, Cohomology on Sites, Tag 0B56,
`equation-projection-formula-map`; Categories, Tag 0DV0, `lemma-compose-counits`
(blueprint: lem-sfb-ringed-projection-tensor-composition).

We use the recorded ringed-site tensor models, their canonical tensor comparisons,
and `RingedTensorEdge.projection`. Associators and symmetries below are specified
on flat K-flat representatives. A section comparison is specified by the given
ringed isomorphism on underlying sheaves, ordinary modules, and representatives.
(blueprint: def-sfb-ringed-projection-coherence-data).

The composite adjunction is the normal form of the canonical pullback/direct-image
comparisons: its tensor map is the composite of the two canonical tensor maps.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.ProjectionCoherence

/-- The recorded direct-sum total tensor, abbreviated only to keep representative
normalizations readable. Source: Stacks 06YN and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
abbrev total (A : RingedTensorCorner.{u, w})
    (P Q : CochainComplex A.mateModules ℤ) :=
  CochainComplex.mapBifunctor P Q A.mateTensor

/-- The ordinary associator of the signed total tensor: it reassociates pure tensors
without a sign. Source: Stacks 06YN, 07A4 and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def totalAssociator (A : RingedTensorCorner.{u, w})
    (P Q T : CochainComplex A.mateModules ℤ) :
    total A (total A P Q) T ≅ total A P (total A Q T) := by
  letI := monoidalCategory A.ring
  letI := symmetricCategory A.ring
  letI := ringedTensorPreadditive A.ring
  letI : MonoidalClosed A.mateModules := Classical.choice (tensorClosed A.ring).2.1
  letI : HasColimitsOfSize.{0, 0} A.mateModules := hasColimitsOfSizeShrink.{0, 0, u, u} _
  exact HomologicalComplex.associator P Q T

/-- The projection mate for the composite in the canonical comparison normal form.
This is defined by transposing the composite tensor comparison followed by the
composite counit; it is not defined as the two projection maps whose equality is asserted.
Source: Stacks 0B56 and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def compositeProjection {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z)
    (E : X.mateDerived) (Q : Z.mateDerived) :
    Z.tensor.obj (g.right.obj (f.right.obj E), Q) ⟶
      g.right.obj (f.right.obj (X.tensor.obj (E, f.left.obj (g.left.obj Q)))) :=
  (g.derivedAdjunction.comp f.derivedAdjunction).homEquiv _ _
    (f.left.map ((g.tensorComparison c b).hom.app (g.right.obj (f.right.obj E), Q)) ≫
      (f.tensorComparison b a).hom.app
        (g.left.obj (g.right.obj (f.right.obj E)), g.left.obj Q) ≫
      X.tensor.map (Prod.mkHom
        ((g.derivedAdjunction.comp f.derivedAdjunction).counit.app E)
        (𝟙 (f.left.obj (g.left.obj Q)))))

/-- Ordinary comparisons presenting a chosen ringed-topos composite `h = g f`.
The insertion equation fixes the module comparison from the underlying geometric
comparison and the structural ring maps. It is not a tensor or projection equation.
Source: Stacks 0D6D, 0D6E and 0FPI
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure Composition {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X) where
  sets : h.inverse ≅ g.inverse ⋙ f.inverse
  modules : h.pullback ≅ g.pullback ⋙ f.pullback
  insertion : ∀ M : Z.mateModules,
    h.insertion M ≫
        (toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
          RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).map
            (modules.hom.app M) =
      sets.hom.app ((toSheaf ((sheafCompose Z.topology (forget₂ CommRingCat.{u}
        RingCat.{u})).obj Z.ring) ⋙
          sheafCompose Z.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
        f.inverse.map (g.insertion M) ≫ f.insertion (g.pullback.obj M)

/-- The defining K-flat normalization of the canonical derived composition comparison.
Source: Stacks 0D6D and 0FPI
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def Composition.Normalized {X Y Z : RingedTensorCorner.{u, w}}
    {f : RingedTensorEdge Y X} {g : RingedTensorEdge Z Y} {h : RingedTensorEdge Z X}
    (s : Composition f g h) (l : h.left ≅ g.left ⋙ f.left) : Prop :=
  ∀ (P : CochainComplex Z.mateModules ℤ), Z.mateFlat P →
    l.hom.app (DerivedCategory.Q.obj P) ≫
        f.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
        derivedPullbackComplexComparison f.pullback f.left f.epsilon
          ((g.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      derivedPullbackComplexComparison h.pullback h.left h.epsilon P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)).hom.app P)

/-- An ordinary ringed-topos comparison with the identity morphism. The insertion
condition includes compatibility with the structural ring map.
Source: Stacks 0D6D, 0FPI and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure Identity {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X) where
  sets : h.inverse ≅ 𝟭 (Sheaf X.topology (Type u))
  modules : h.pullback ≅ 𝟭 X.mateModules
  insertion : ∀ M : X.mateModules,
    h.insertion M ≫
        (toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
          RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).map
            (modules.hom.app M) =
      sets.hom.app ((toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
        RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M)

/-- The identity pullback comparison, specified on all flat K-flat representatives.
Source: Stacks 0D6D, 0FPI and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def Identity.Normalized {X : RingedTensorCorner.{u, w}} {h : RingedTensorEdge X X}
    (s : Identity h) (l : h.left ≅ 𝟭 X.mateDerived) : Prop :=
  ∀ (P : CochainComplex X.mateModules ℤ), X.mateFlat P →
    l.hom.app (DerivedCategory.Q.obj P) =
      derivedPullbackComplexComparison h.pullback h.left h.epsilon P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)).hom.app P)

/-- The direct-image identity comparison adjunction-conjugate to its pullback comparison.
Source: Stacks 0FPI and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def identityRight {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X)
    (l : h.left ≅ 𝟭 X.mateDerived) : h.right ≅ 𝟭 X.mateDerived :=
  conjugateIsoEquiv h.derivedAdjunction Adjunction.id l.symm

/-- A specified ringed isomorphism `p i ≅ id`, including its ordinary module map.
The insertion equation is the compatibility with the structural ring maps, written
on generalized module elements. It assumes no derived tensor or projection equation.
Source: Stacks 0D6D, 0FPI and the section specialization of 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure Section {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W) where
  sets : p.inverse ⋙ i.inverse ≅ 𝟭 (Sheaf X.topology (Type u))
  modules : p.pullback ⋙ i.pullback ≅ 𝟭 X.mateModules
  insertion : ∀ M : X.mateModules,
    i.inverse.map (p.insertion M) ≫ i.insertion (p.pullback.obj M) ≫
        (toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
          RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).map
            (modules.hom.app M) =
      sets.hom.app ((toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
        RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M)

/-- The normalization defining the canonical derived pullback comparison for a section.
Source: Stacks 0D6D and 0FPI; section specialization of 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def Section.Normalized {X W : RingedTensorCorner.{u, w}}
    {i : RingedTensorEdge W X} {p : RingedTensorEdge X W} (s : Section i p)
    (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived) : Prop :=
  ∀ (P : CochainComplex X.mateModules ℤ), X.mateFlat P →
    l.hom.app (DerivedCategory.Q.obj P) =
      i.left.map (derivedPullbackComplexComparison p.pullback p.left p.epsilon P) ≫
        derivedPullbackComplexComparison i.pullback i.left i.epsilon
          ((p.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)).hom.app P)

end SheafOfModules.ProjectionCoherence
