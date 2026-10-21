/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-! # The ringed geometric point as final-object evaluation

Source: Stacks Project, Tags 0991, 03EL and 07A4, and the completed coefficient
construction in blueprint order 1455
(blueprint: def-sf-point-evaluation-tensor-data).

The data below specify the maps, including every total summand, rather than merely
asserting that the relevant objects are isomorphic. The integral tensor is ambient.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.all false
set_option linter.unusedVariables false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.PointEvaluation

variable (k : Type u) [Field k]

/-- The final object of the recorded small site.
Source: Stacks 0991 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev finalObject := Scheme.ProEt.mk (𝟙 (Spec (.of k)))

/-- The actual section ring, with its inherited commutative ring operations.
Source: Stacks 03EL (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev sectionRing (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :=
  B.obj.obj (op (finalObject k))

/-- The recorded termwise exact section functor, without a new module construction.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev complexSections (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :=
  (pointModuleSections k B).mapHomologicalComplex (.up ℤ)

variable {k}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})

/-- The dependency's module-sheaf category, with its universes explicit.
Source: Stacks 03DA (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev ModuleSheaves := SheafOfModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)

/-- Fix the existing monoidal structure at the recorded coefficient size.
Source: Stacks 03EK (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2000) moduleMonoidal : MonoidalCategory (ModuleSheaves B) :=
  SheafOfModules.KFlatTotalTensorModel.monoidal B

/-- The existing signed-symmetry input at the same fixed coefficient size.
Source: Stacks 03EK (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2000) moduleSymmetric : SymmetricCategory (ModuleSheaves B) :=
  SheafOfModules.cochainModulesSymmetric.{u + 1, u, u + 1} B

/-- Specialize the dependency's tensor additivity without changing its structure.
Source: Stacks 03EK (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2000) moduleTensorPreadditive : MonoidalPreadditive (ModuleSheaves B) :=
  SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1} B

/-- Specialize the dependency's tensor colimits at the small pro-etale sizes.
Source: Stacks 03EK (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2000) moduleLeftColimits (M : ModuleSheaves B) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits.{u + 1, u, u + 1} B M

/-- Specialize the dependency's right tensor colimits at the same sizes.
Source: Stacks 03EK (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2000) moduleRightColimits (M : ModuleSheaves B) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits.{u + 1, u, u + 1} B M

/-- The existing category of unbounded integer cochain complexes.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev Complexes := CochainComplex (ModuleSheaves B) ℤ

/-- The canonical section tensor in Mathlib's localization tensor, obtained from
its sheafification-unit tensor via the specified comparison.
Source: Stacks 03EK, 03EL (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev sectionTensor (M N : ModuleSheaves B)
    (x : (pointModuleSections k B).obj M) (y : (pointModuleSections k B).obj N) :=
  Scheme.proEtaleTensorPair (Spec (.of k)) B M N (op (finalObject k)) x y

/-- The flat-term K-flat class from the two recorded dependency predicates.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev resolving := Scheme.proEtaleFlatRepresentatives (Spec (.of k)) B

/-- Ordinary K-flatness is the same acyclic-test definition, now for R-modules.
Source: Stacks 06YN (blueprint: def-sf-point-evaluation-tensor-data). -/
def moduleResolving : ObjectProperty (CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ) :=
  fun P ↦ (HomologicalComplex.quasiIso
    (ModuleCat.{u + 1} (sectionRing k B)) (.up ℤ)).kFlat P ∧
    ∀ i : ℤ, Module.Flat (sectionRing k B) (P.X i)

/-- The existing inclusion of a summand into the signed total, at fixed coefficient size.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev totalInclusion (P Q : Complexes B) (i j n : ℤ) (h : i + j = n) :
    P.X i ⊗ Q.X j ⟶ ((SheafOfModules.KFlatTotalTensorModel.total B).obj (P, Q)).X n :=
  CochainComplex.ιMapBifunctor P Q (SheafOfModules.KFlatTotalTensorModel.tensor B) i j n h

/-- The existing total tensor object with its coefficient universe fixed.
Source: Stacks 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev totalObj (P Q : Complexes B) :=
  (SheafOfModules.KFlatTotalTensorModel.total B).obj (P, Q)

/-- Pin the existing abelian structure when constructing degree-zero complexes.
Source: Stacks 03DA (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2000) moduleAbelian : Abelian (ModuleSheaves B) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
    (SheafOfModules.KFlatTotalTensorModel.smallSiteHasSheafify.{u + 1, u, u + 1})
    (SheafOfModules.KFlatTotalTensorModel.smallSiteWEqualsLocallyBijective.{u + 1, u, u + 1})

/-- The existing degree-zero coefficient unit.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
abbrev complexUnit : Complexes B :=
  @HomologicalComplex.tensorUnit.{u + 1, u + 2, 0} (ModuleSheaves B) _
    (moduleMonoidal B) _ (@Abelian.hasZeroObject _ _ (moduleAbelian B)) ℤ _ (.up ℤ) _

/-- The existing small colimits, with the module carrier universe fixed explicitly.
Source: Stacks 03DA (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2100) moduleColimits : HasColimitsOfSize.{0, 0} (ModuleSheaves B) :=
  @SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf.{0, 0,
    u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
    (inferInstance : HasWeakSheafify (Scheme.ProEt.topology (Spec (.of k)))
      AddCommGrpCat.{u + 1})
    (SheafOfModules.KFlatTotalTensorModel.smallSiteWEqualsLocallyBijective.{u + 1, u, u + 1})
    (inferInstance : HasColimitsOfSize.{0, 0}
      (PresheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj))

/-- Use small colimits directly, avoiding an unconstrained carrier universe.
Source: Stacks 03DA (blueprint: def-sf-point-evaluation-tensor-data). -/
instance (priority := 2200) moduleShapeColimits (I : Type) [SmallCategory I] :
    HasColimitsOfShape I (ModuleSheaves B) :=
  @HasColimitsOfSize.has_colimits_of_shape _ _ (moduleColimits B) I _

set_option maxHeartbeats 800000 in
-- Elaborate the termwise tensor and unit comparison data.
/-- A point tensor model, with its actual section tensor and signed chain maps.
All coherence fields are equations of maps in the existing cochain categories.
Source: Stacks 03EL and 07A4 (blueprint: def-sf-point-evaluation-tensor-data). -/
structure TensorModel where
  /-- Additivity of the recorded evaluation functor. -/
  [sectionsAdditive : (pointModuleSections k B).Additive]
  /-- The ordinary module comparison, normalized on sections. -/
  moduleIso : ∀ M N : ModuleSheaves B,
    (pointModuleSections k B).obj (M ⊗ N) ≅
      (pointModuleSections k B).obj M ⊗ (pointModuleSections k B).obj N
  /-- Its inverse is the section tensor, not a chosen multiple. -/
  module_pure : ∀ (M N : ModuleSheaves B) (x : (pointModuleSections k B).obj M)
    (y : (pointModuleSections k B).obj N),
    (moduleIso M N).inv (x ⊗ₜ[sectionRing k B] y) = sectionTensor B M N x y
  /-- The chain comparison in the direction of the statement. -/
  b : ∀ P Q : Complexes B,
    (complexSections k B).obj ((SheafOfModules.KFlatTotalTensorModel.total B).obj (P, Q)) ≅
      HomologicalComplex.tensorObj (C := ModuleCat.{u + 1} (sectionRing k B))
        ((complexSections k B).obj P) ((complexSections k B).obj Q)
  /-- The inverse is fixed on every bidegree summand of the full direct-sum total. -/
  inverse_summand : ∀ (P Q : Complexes B) (i j n : ℤ) (h : i + j = n),
    HomologicalComplex.ιTensorObj (C := ModuleCat.{u + 1} (sectionRing k B))
        ((complexSections k B).obj P)
        ((complexSections k B).obj Q) i j n h ≫ (b P Q).inv.f n =
      (moduleIso (P.X i) (Q.X j)).inv ≫ (pointModuleSections k B).map
        (totalInclusion B P Q i j n h)
  /-- Two-variable naturality before localization. -/
  naturality : ∀ (P Q P' Q' : Complexes B) (f : P ⟶ P') (g : Q ⟶ Q'),
    (complexSections k B).map
      ((SheafOfModules.KFlatTotalTensorModel.total B).map (Prod.mkHom f g)) ≫ (b P' Q').hom =
      (b P Q).hom ≫ ((complexSections k B).map f ⊗ₘ (complexSections k B).map g)
  /-- The unit is the degree-zero lift of evaluation B(s) = R. -/
  unit : (complexSections k B).obj (complexUnit B) ≅
    𝟙_ (CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ)
  /-- The module unit is evaluation of the coefficient sheaf itself. -/
  moduleUnit : (pointModuleSections k B).obj (SheafOfModules.unit
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≅
    ModuleCat.of (sectionRing k B) (sectionRing k B)
  /-- The degree-zero coefficient map is exactly the identity. -/
  unit_value : ∀ x : sectionRing k B, moduleUnit.hom x = x
  /-- Exact evaluation preserves the zero maps needed for the unit lift. -/
  [sectionsZero : (pointModuleSections k B).PreservesZeroMorphisms]
  /-- Evaluation preserves precisely the resolving class used for derived pullback. -/
  preserves_resolving : ∀ P : Complexes B, resolving B P →
    moduleResolving B ((complexSections k B).obj P)




end AlgebraicGeometry.ProEtale.PointEvaluation
