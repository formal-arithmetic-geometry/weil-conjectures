/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputationSupplement

/-!
# Bounded finite-free projection chain model

Source: Stacks Project, Cohomology on Sites, Tags 0B56 and 0944
(blueprint: lem-pbc-bounded-free-projection-chain-model).

The chain map is the existing signed total counit mate.  The derived
identifications in the statement are the representative identifications of the
ringed tensor presentation, with their naturality and representative
independence recorded explicitly below.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MonoidalCategory

namespace SheafOfModules

set_option linter.style.haveILetI false in
/-- The direct image on module sheaves is additive because its right adjoint preserves products.
Source: Stacks Tag 07A6 (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
instance ringedTensorEdgePushforwardAdditive
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :
    e.pushforward.Additive := by
  letI := e.moduleAdjunction.rightAdjoint_preservesLimits
  exact e.pushforward.additive_of_preserves_binary_products

/-- The signed total chain map adjoint to the tensor of the counit.
Source: Stacks, Tags 0B56 and 0944; blueprint order for
`lem-pbc-bounded-free-projection-chain-model`.
The finite-free and bounded hypotheses are deliberately not used to define the
map: they are hypotheses for the derived projection-formula identification.
-/
noncomputable def boundedFreeProjectionChainMap
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (I : CochainComplex X.mateModules ℤ)
    (P : CochainComplex Y.mateModules ℤ) :
    CochainComplex.mapBifunctor
        ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        P (curriedTensor Y.mateModules) ⟶
      (e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor I
          ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (curriedTensor X.mateModules)) := by
  letI := monoidalCategory Y.ring
  letI := monoidalCategory X.ring
  exact CategoryTheory.tensorAdjunctionTotal e.pullback e.pushforward
    e.moduleAdjunction e.ordinaryTensor.mu
    (fun {_ _ _ _} f g ↦ e.ordinaryTensor.naturality f g) I P

/-- The canonical right-derived comparison supplied by the derived adjunction.
Its adjunct is the derived pullback comparison followed by the ordinary counit,
so it does not choose an isomorphism or an inverse.
Source: Stacks Tags 07A6 and 0944 (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
noncomputable def boundedFreeRightDerivedComparison
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (I : CochainComplex X.mateModules ℤ) :
    DerivedCategory.Q.obj
        ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      e.right.obj (DerivedCategory.Q.obj I) :=
  e.derivedAdjunction.homEquiv _ _
    (e.epsilon.app
      ((HomotopyCategory.quotient Y.mateModules (ComplexShape.up ℤ)).obj
        ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      DerivedCategory.Q.map
        ((e.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I))

/-- The finite-free termwise package used for the K-flat representative.
Source: Stacks Tag 06YQ (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
noncomputable def boundedFreeStrictPerfectPackage
    {Y : RingedTensorCorner.{u, w}} (P : CochainComplex Y.mateModules ℤ)
    (hfree : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P.X r ≅ ∏ᶜ fun _ : Fin N ↦
      SheafOfModules.unit ((sheafCompose Y.topology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring))) :
    StrictPerfectCoefficientPackage
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring) P :=
  { N := fun r ↦ Classical.choose (hfree r)
    i := fun r ↦ (Classical.choice (Classical.choose_spec (hfree r))).hom
    p := fun r ↦ (Classical.choice (Classical.choose_spec (hfree r))).inv
    splitting := fun r ↦ (Classical.choice (Classical.choose_spec (hfree r))).hom_inv_id }

/-- The source comparison in the bounded projection formula is the inverse of the
canonical mixed-tensor representative, followed by the right-derived comparison for
`I` in the first factor. The finite-free and bounded hypotheses determine the
K-flat/flat proof supplied to `mixedTensorRepresentative`; no comparison is chosen
freely.
Source: Stacks Tags 07A4 and 0944 (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
noncomputable def boundedFreeSourceComparison
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (I : CochainComplex X.mateModules ℤ)
    (P : CochainComplex Y.mateModules ℤ)
    (hbounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P.X r))
    (hfree : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P.X r ≅ ∏ᶜ fun _ : Fin N ↦
      SheafOfModules.unit ((sheafCompose Y.topology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring))) :
    DerivedCategory.Q.obj (CochainComplex.mapBifunctor
        ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) P
        (curriedTensor Y.mateModules)) ⟶
      Y.tensor.obj (e.right.obj (DerivedCategory.Q.obj I), DerivedCategory.Q.obj P) := by
  let hP := StrictPerfectCoefficientPackage.isKFlat_flat Y.ring P
    (boundedFreeStrictPerfectPackage (Y := Y) P hfree) hbounded
  exact (mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl) Y.tensor
      a.mateRepresentative ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      P hP).inv ≫
    Y.tensor.map (Prod.mkHom (boundedFreeRightDerivedComparison e I) (𝟙 _))

/-- The target comparison uses the canonical mixed-tensor representative on `X`,
the right-derived comparison for `I ⊗ e^*P`, and the comparison `e_P` computing
left derived pullback on the K-flat finite-free complex.
Source: Stacks Tags 07A4 and 0944 (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
noncomputable def boundedFreeTargetComparison
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (b : RingedTensorModel X) (I : CochainComplex X.mateModules ℤ)
    (P : CochainComplex Y.mateModules ℤ)
    (hPpull : X.mateFlat ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hIso : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P)) :
    DerivedCategory.Q.obj ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor I
        ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (curriedTensor X.mateModules))) ⟶
      e.right.obj (X.tensor.obj (DerivedCategory.Q.obj I,
        e.left.obj (DerivedCategory.Q.obj P))) := by
  letI := hIso
  let J := CochainComplex.mapBifunctor I
    ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (curriedTensor X.mateModules)
  exact boundedFreeRightDerivedComparison e J ≫
    e.right.map ((mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl) X.tensor
      b.mateRepresentative I ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      hPpull).inv ≫
      X.tensor.map (Prod.mkHom (𝟙 _) (inv
        (derivedPullbackComplexComparison e.pullback e.left e.epsilon P))))

/-- The uniquely normalized coefficient-unit comparison selected by
`canonicalRingedTensorComparison_unit`.
Source: Stacks Tag 03EL (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
noncomputable def boundedFreeProjectionUnit
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :
    e.pullback.obj (SheafOfModules.unit
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ≅
      SheafOfModules.unit
        ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring) :=
  Classical.choose (canonicalRingedTensorComparison_unit
    Y.ring X.ring e.inverseRing e.inverse e.algebraic e.ringMap e.pullback
    e.object_eq e.map_eq e.ordinaryTensor).exists

/-- The chain-level coefficient-unit comparison induced by `boundedFreeProjectionUnit`.
Source: Stacks Tag 03EL (blueprint: lem-pbc-bounded-free-projection-chain-model).
-/
noncomputable def boundedFreeProjectionUnitComplex
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :
    (e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y.mateUnitComplex ≅
      X.mateUnitComplex := by
  letI := monoidalCategory Y.ring
  letI := monoidalCategory X.ring
  exact (HomologicalComplex.singleMapHomologicalComplex e.pullback
      (ComplexShape.up ℤ) 0).app
      (SheafOfModules.unit
        ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ≪≫
    (CochainComplex.singleFunctor X.mateModules 0).mapIso (boundedFreeProjectionUnit e)

/-- The finite-free representative comparison equation.
Source: Stacks Tags 0B56 and 0944 (blueprint:
`lem-pbc-bounded-free-projection-chain-model-comparison`).
Proof plan: (3) construct the signed total counit mate from the ordinary
pullback-tensor comparison and termwise adjunction; (4) pass to a flat-term
K-flat resolution and use the fixed-tensor and derived-pullback computations;
(5) compare the two adjuncts using the canonical tensor shift/unit formula and
uniqueness of adjuncts. -/
theorem boundedFreeProjectionChainModel_comparison
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (I : CochainComplex X.mateModules ℤ) (hI : I.IsKInjective)
    (P : CochainComplex Y.mateModules ℤ)
    (hbounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P.X r))
    (hfree : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P.X r ≅ ∏ᶜ fun _ : Fin N ↦
      SheafOfModules.unit ((sheafCompose Y.topology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
    (hPpull : X.mateFlat
      ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hIso : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P)) :
      boundedFreeSourceComparison e a I P hbounded hfree ≫
          derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
            (e.tensorComparison a b) (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (boundedFreeProjectionChainMap e I P) ≫
          boundedFreeTargetComparison e b I P hPpull hIso := by
  sorry

/-- Naturality and tensor-unit normalization for the bounded-free representative comparison.
Source: Stacks Tags 0B56 and 03EL (blueprint:
`lem-pbc-bounded-free-projection-chain-model-naturality-unit`).
Proof plan: (6) use ordinary counit naturality and the termwise adjunction,
then localize and invoke the naturality of the right-derived comparison; (7)
represent derived isomorphisms by homotopy-equivalent K-injective maps and use
homotopy invariance of the fixed-tensor functors, with the coefficient-unit
case reduced to the adjunction identity. -/
theorem boundedFreeProjectionChainModel_naturality_unit
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (I : CochainComplex X.mateModules ℤ) (hI : I.IsKInjective)
    (P : CochainComplex Y.mateModules ℤ)
    (hbounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P.X r))
    (hfree : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P.X r ≅ ∏ᶜ fun _ : Fin N ↦
      SheafOfModules.unit ((sheafCompose Y.topology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
    (hPpull : X.mateFlat
      ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hIso : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P)) :
      (∀ (I' : CochainComplex X.mateModules ℤ) (hI' : I'.IsKInjective)
        (P' : CochainComplex Y.mateModules ℤ)
        (hbounded' : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P'.X r))
        (hfree' : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P'.X r ≅ ∏ᶜ fun _ : Fin N ↦
          SheafOfModules.unit ((sheafCompose Y.topology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
        (u : I ⟶ I') (v : P ⟶ P')
        (hPpull' : X.mateFlat
          ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
        (hIso' : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P')),
        DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap
              ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map u)
              v (curriedTensor Y.mateModules) (ComplexShape.up ℤ)) ≫
          boundedFreeSourceComparison e a I' P' hbounded' hfree' =
        boundedFreeSourceComparison e a I P hbounded hfree ≫
          Y.tensor.map (Prod.mkHom (e.right.map (DerivedCategory.Q.map u))
            (DerivedCategory.Q.map v))) ∧
      (∀ (I' : CochainComplex X.mateModules ℤ) (hI' : I'.IsKInjective)
        (P' : CochainComplex Y.mateModules ℤ)
        (hbounded' : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P'.X r))
        (hfree' : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P'.X r ≅ ∏ᶜ fun _ : Fin N ↦
          SheafOfModules.unit ((sheafCompose Y.topology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
        (u : I ⟶ I') (v : P ⟶ P')
        (hPpull' : X.mateFlat
          ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
        (hIso' : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P')),
        DerivedCategory.Q.map
            ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap u
                ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).map v)
                (curriedTensor X.mateModules) (ComplexShape.up ℤ))) ≫
          boundedFreeTargetComparison e b I' P' hPpull' hIso' =
        boundedFreeTargetComparison e b I P hPpull hIso ≫ e.right.map (X.tensor.map
          (Prod.mkHom (DerivedCategory.Q.map u) (e.left.map (DerivedCategory.Q.map v))))) ∧
      (letI := monoidalCategory Y.ring
       letI := monoidalCategory X.ring
       boundedFreeProjectionChainMap e I Y.mateUnitComplex ≫
          (e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap (𝟙 I)
              (boundedFreeProjectionUnitComplex e).hom
              (curriedTensor X.mateModules) (ComplexShape.up ℤ) ≫
              (HomologicalComplex.rightUnitor I).hom) =
        (HomologicalComplex.rightUnitor
          ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).hom) := by
  sorry

/-- Bounded finite-free chain representative of the projection formula.
Source: Stacks Tags 0B56 and 0944 (blueprint:
`lem-pbc-bounded-free-projection-chain-model`).
Proof plan: (1) the finite-free package gives bounded flat terms and hence a
K-flat complex; (2) ringed-topos pullback preserves this K-flatness and the
canonical derived-pullback comparison is an isomorphism; (3--5) prove the
finite-free representative comparison by the signed counit mate, a K-flat
resolution, and the canonical tensor comparison; (6--7) prove naturality,
representative independence, and the tensor-unit normalization. The last two
parts are isolated in the named comparison and naturality/unit lemmas below.
-/
theorem boundedFreeProjectionChainModel
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (I : CochainComplex X.mateModules ℤ) (hI : I.IsKInjective)
    (P : CochainComplex Y.mateModules ℤ)
    (hbounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P.X r))
    (hfree : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P.X r ≅ ∏ᶜ fun _ : Fin N ↦
      SheafOfModules.unit ((sheafCompose Y.topology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring))) :
    ∃ (hPpull : X.mateFlat
        ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
      (hIso : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P)),
      boundedFreeSourceComparison e a I P hbounded hfree ≫
          derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
            (e.tensorComparison a b) (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (boundedFreeProjectionChainMap e I P) ≫
          boundedFreeTargetComparison e b I P hPpull hIso ∧
      (∀ (I' : CochainComplex X.mateModules ℤ) (hI' : I'.IsKInjective)
        (P' : CochainComplex Y.mateModules ℤ)
        (hbounded' : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P'.X r))
        (hfree' : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P'.X r ≅ ∏ᶜ fun _ : Fin N ↦
          SheafOfModules.unit ((sheafCompose Y.topology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
        (u : I ⟶ I') (v : P ⟶ P')
        (hPpull' : X.mateFlat
          ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
        (hIso' : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P')),
        DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap
              ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map u)
              v (curriedTensor Y.mateModules) (ComplexShape.up ℤ)) ≫
          boundedFreeSourceComparison e a I' P' hbounded' hfree' =
        boundedFreeSourceComparison e a I P hbounded hfree ≫
          Y.tensor.map (Prod.mkHom (e.right.map (DerivedCategory.Q.map u))
            (DerivedCategory.Q.map v))) ∧
      (∀ (I' : CochainComplex X.mateModules ℤ) (hI' : I'.IsKInjective)
        (P' : CochainComplex Y.mateModules ℤ)
        (hbounded' : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (P'.X r))
        (hfree' : ∀ r : ℤ, ∃ N : ℕ, Nonempty (P'.X r ≅ ∏ᶜ fun _ : Fin N ↦
          SheafOfModules.unit ((sheafCompose Y.topology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
        (u : I ⟶ I') (v : P ⟶ P')
        (hPpull' : X.mateFlat
          ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
        (hIso' : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P')),
        DerivedCategory.Q.map
            ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap u
                ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).map v)
                (curriedTensor X.mateModules) (ComplexShape.up ℤ))) ≫
          boundedFreeTargetComparison e b I' P' hPpull' hIso' =
        boundedFreeTargetComparison e b I P hPpull hIso ≫
          e.right.map (X.tensor.map
            (Prod.mkHom (DerivedCategory.Q.map u) (e.left.map (DerivedCategory.Q.map v))))) ∧
      (letI := monoidalCategory Y.ring
       letI := monoidalCategory X.ring
       boundedFreeProjectionChainMap e I Y.mateUnitComplex ≫
          (e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap (𝟙 I)
              (boundedFreeProjectionUnitComplex e).hom
              (curriedTensor X.mateModules) (ComplexShape.up ℤ) ≫
              (HomologicalComplex.rightUnitor I).hom) =
        (HomologicalComplex.rightUnitor
          ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).hom) := by
  classical
  letI := monoidalCategory Y.ring
  letI := monoidalCategory X.ring
  have hP : Y.mateFlat P := by
    exact (StrictPerfectCoefficientPackage.isKFlat_flat Y.ring P
      (boundedFreeStrictPerfectPackage P hfree) hbounded)
  have hPpull : X.mateFlat
      ((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
    have hf (n : ℤ) : IsFlatOnSite (J := Y.topology) (R := Y.ring) (P.X n) :=
      (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso Y.ring (P.X n)).symm (hP.2 n)
    obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
      e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1) hf
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso X.ring (((e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)) (ht n)
  have hfsite (n : ℤ) : SheafOfModules.IsFlatOnSite (J := Y.topology)
      (R := Y.ring) (P.X n) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso Y.ring (P.X n)).symm (hP.2 n)
  have hIso : IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P) := by
    exact (SheafOfModules.CanonicalTensorPullbackOfUniverses.derivedPullback_kflat_tensor_computation
      e.inverse e.direct e.adjunction e.algebraic e.ringMap e.pullback e.object_eq e.map_eq
      e.left e.epsilon e.isLeftDerived).1 P hP.1 hfsite
  refine ⟨hPpull, hIso, ?_⟩
  exact ⟨boundedFreeProjectionChainModel_comparison e a b I hI P hbounded hfree hPpull hIso,
    boundedFreeProjectionChainModel_naturality_unit e a b I hI P hbounded hfree hPpull hIso⟩

end SheafOfModules
