/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.RingedTopoiDerivedPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Bounded acyclic flat models for the proper coefficient map

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6,
remark-Rf-lower-shriek-change-of-rings (blueprint:
lem-sp-acyclic-flat-proper-coefficient-model).

The scalar extension, its pullback comparison, and the coefficient mate are the
canonical constructions already provided by the étale six-functor interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/- The three names below expose the canonical objects named in the statement. -/

/-- The derived tensor `T_T = - ⊗ᴸ_{A_T} B_T` used in the coefficient comparison.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientTensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension φ T

/-- The canonical tensor/pullback comparison `λ : T_W r_A^* ≅ r_B^* T_V` for the
coefficient extension; `scalarPullbackIso` is its inverse, used in the transpose below.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientPullbackComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  (scalarPullbackIso φ r).symm

/-- The canonical coefficient map `q_r`, defined as the adjoint mate of the
scalar-extended counit through the comparison above.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  scalarMate φ r

/-- The termwise scalar extension `C_B` of a cochain complex on `W`.
Source: Stacks 0GL6 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
abbrev coefficientExtendedComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
  ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj C

/-- The canonical acyclic-complex comparison, including the homotopy quotient factor.
Source: Stacks 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properAcyclicComparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj (DerivedCategory.Q.obj C) :=
  DerivedCategory.Qh.map
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)

/-- The ordinary B-linear projection map: the mate of scalar extension of the A-counit
through the ordinary scalar/pullback isomorphism. Its degreewise adjunct is precisely
pullback/tensor reassociation followed by counit tensor identity.
Source: Stacks 0GL6, 07A4 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properSheafCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    lowerStar (ModuleCat.{u + 1} A) r ⋙ ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ W ⋙ lowerStar (ModuleCat.{u + 1} B) r :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom)).natTrans

/-- The termwise projection chain map pi_C. Mapping the ordinary natural transformation
on complexes guarantees that its components commute with the differentials.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properCoefficientComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj
        (coefficientExtendedComplex φ W C) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (lowerStar (ModuleCat.{u + 1} A) r ⋙
        ProEtale.etaleSheafExtendScalars φ V)) (.up ℤ)).hom.app C ≫
    (NatTrans.mapHomologicalComplex (properSheafCoefficientMap φ r) (.up ℤ)).app C ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ W ⋙
        lowerStar (ModuleCat.{u + 1} B) r)) (.up ℤ)).inv.app C

/-- The bounded, termwise flat and direct-image-acyclic hypotheses for this model.
Flatness of a term is exactness of tensoring with it (Stacks 03ER), the predicate
`exactFunctor` on the sheaf `tensorRight` recorded for this encoding by def-pc-flat-sheaf-modules.
Both coefficient rings and the proper Noetherian morphism are bound by the theorem.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def IsAcyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (C.X n)) ∧
    (∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (C.X n))) ∧
    (∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight
      ((lowerStar (ModuleCat.{u + 1} A) r).obj (C.X n)))) ∧
    (∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj
            ((DerivedCategory.singleFunctor
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (C.X n))))) ∧
    (∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) r).obj
            ((DerivedCategory.singleFunctor
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj
              ((coefficientExtendedComplex φ W C).X n)))))

/-- A bounded acyclic flat model computes the canonical proper coefficient mate termwise.
The comparisons alpha_A and alpha_B are the canonical derived units on complexes;
the scalar-extension comparisons are the canonical flat-model counits. The displayed
square identifies the B-linear coefficient mate with the localization of pi_C.

Source: Stacks 0GL6, 015E, 0FND, 06YQ and 07A4
(blueprint: lem-sp-acyclic-flat-proper-coefficient-model).

Proof:
1. The etale module-sheaf categories are Grothendieck abelian with enough injectives
(lem-weil-pbc-module-sheaves-grothendieck-abelian and
lem-weil-pbc-module-sheaves-enough-injectives). Direct image is additive and left exact
(lem-weil-pbc-module-direct-image-left-exact), and its left adjoint is exact
(prop-weil-pbc-inverse-image-modules-exact). Use the canonical derived adjunction.
2. Apply lemma-weil-pbc-leray-acyclicity clause (3) to the identity quasi-isomorphisms
of C and C_B. Boundedness and positive direct-image acyclicity make the specified
comparison maps alpha_A and alpha_B invertible in the unbounded derived categories.
3. The bounded flat complexes C and D = r_*C are K-flat by
lem-pc-bounded-above-flat-kflat-site. K-flatness is the project's `kFlat` for the
quasi-isomorphisms: tensoring with the complex preserves quasi-isomorphisms, equivalently
(through mapping cones) sends acyclic complexes to acyclic total tensor complexes.
The canonical scalar-extension comparisons therefore identify their derived extensions
with their termwise extensions, by
def-kun-derived-tensor and lem-weil-pbc-ringed-topoi-derived-pullback. This resolves
the first factor only and needs no flatness or finite projective dimension of B.
4. The explicit Hom formula of lem-pc-pre-derived-adjoint-functors-general at the
identity denominators says that alpha_A has adjunct the degreewise A-counit.
5. Pullback preserves K-flat flat-term models by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. On these models the canonical
scalar/pullback comparison is ordinary reassociation. Naturality and step 4 show
that the adjunct of q_r composed with scalar extension of alpha_A is the localized
ordinary reassociation followed by counit tensor identity.
6. Its ordinary B-adjunct is pi_C in each degree. Naturality of the ordinary Hom
bijection makes these components a chain map. Apply the same explicit derived Hom
formula at identity denominators: alpha_B composed with Q(pi_C) has that adjunct.
7. Injectivity of the derived adjunction Hom bijection identifies the two maps,
giving the displayed square with the specified scalar-extension comparisons.
8. All comparisons are the canonical natural transformations. Naturality of their
units, counits, and homotopy quotient factors, and the ordinary mate defining pi,
give all six naturality equations for maps between the stipulated models. -/
theorem acyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {W V : Scheme.{u}} (r : W ⟶ V) [IsProper r] [IsNoetherian W] [IsNoetherian V]
    (φ : A →+* B)
    (C : CochainComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : IsAcyclicFlatProperCoefficientModel φ r C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ∧
      IsIso (properAcyclicComparison A r C) ∧
      IsIso (properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      IsIso (scalarExtensionRepresentative φ W C) ∧
      IsIso (scalarExtensionRepresentative φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ((properCoefficientTensor φ V).map (properAcyclicComparison A r C) ≫
          (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
            (scalarExtensionRepresentative φ W C) =
        scalarExtensionRepresentative φ V
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map (properCoefficientComplexMap φ r C) ≫
          properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      (∀ (C' : CochainComplex
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (_hC' : IsAcyclicFlatProperCoefficientModel φ r C') (h : C ⟶ C'),
        (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              ((properCoefficientTensor φ W).map (DerivedCategory.Q.map h)) =
          (properCoefficientTensor φ V).map
              ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
                (DerivedCategory.Q.map h)) ≫
            (properCoefficientMap φ r).app (DerivedCategory.Q.obj C') ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properAcyclicComparison A r C' =
          properAcyclicComparison A r C ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ≫
            properAcyclicComparison B r (coefficientExtendedComplex φ W C') =
          properAcyclicComparison B r (coefficientExtendedComplex φ W C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              (DerivedCategory.Q.map
                (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ∧
        (properCoefficientTensor φ W).map (DerivedCategory.Q.map h) ≫
            scalarExtensionRepresentative φ W C' =
          scalarExtensionRepresentative φ W C ≫ DerivedCategory.Q.map
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h) ∧
        (properCoefficientTensor φ V).map (DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ≫
            scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C') =
          scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
            DerivedCategory.Q.map
              (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
                (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ∧
        ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properCoefficientComplexMap φ r C' =
          properCoefficientComplexMap φ r C ≫
            ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) := by
  sorry

end AlgebraicGeometry.Etale
