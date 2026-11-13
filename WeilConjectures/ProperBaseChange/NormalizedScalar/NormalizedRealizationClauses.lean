/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedBoundedScalar
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.Adjunction.NormalizedExactDerivedUnit
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The coefficient, adjunction and derived clauses of the normalized assertion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NormalizedScalar

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- Extension by the actual coefficient inclusion, at the module universes of T. -/
abbrev ordinaryExtension := Mod.extendScalars (inclusion l E T)

/-- Restriction by the same coefficient inclusion. -/
abbrev ordinaryRestriction :=
  Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (inclusion l E T)

/-- Both scalar functors are additive and exact, and their adjunction has the
unit obtained by inserting the ring unit and projecting to the balanced tensor.
Source: the internal extension-restriction adjunction.
(blueprint: lem-weil-pbc-normalized-realization-clauses). -/
def ScalarAdjunctionData : Prop :=
  (ordinaryExtension l E T).Additive ∧ (ordinaryRestriction l E T).Additive ∧
  PreservesFiniteLimits (ordinaryExtension l E T) ∧
  PreservesFiniteColimits (ordinaryExtension l E T) ∧
  PreservesFiniteLimits (ordinaryRestriction l E T) ∧
  PreservesFiniteColimits (ordinaryRestriction l E T) ∧
  ∃ a : ordinaryExtension l E T ⊣ ordinaryRestriction l E T,
    ∀ M, (a.unit.app M).hom =
      (λ_ M.X).inv ≫
        CategoryTheory.MonoidalCategory.whiskerRight (η[fieldRing l E T]) M.X ≫
          Mod.extendπ (inclusion l E T) M

/-- The exact adjunction and its normalized ordinary tensor unit.
Source: internal scalar extension and its explicit adjunction unit.
(blueprint: lem-weil-pbc-normalized-realization-clauses).
Proof: exactness of extension is normalized coefficient exactness; restriction
preserves finite limits and colimits on underlying objects. The canonical
adjunction's unit is precisely unit insertion followed by the tensor projection. -/
theorem scalar_adjunction_data : ScalarAdjunctionData l E T := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Mod.extendRestrictAdjunction (inclusion l E T), ?_⟩
  intro M
  exact Mod.extendRestrictAdjunction_unit_app_hom (inclusion l E T) M

/-- The derived functors have coherent integer shifts, preserve triangles, compute
termwise on every complex, and their adjunction unit is the localized termwise unit.
Source: exact derived factorization and localization of adjunctions.
(blueprint: lem-weil-pbc-normalized-realization-clauses). -/
def DerivedScalarData : Prop :=
  let F := ordinaryExtension l E T
  let G := ordinaryRestriction l E T
  -- Reuse exactness instances instead of synthesizing them at every derived occurrence.
  have : F.Additive := inferInstance
  have : G.Additive := inferInstance
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesFiniteLimits G := inferInstance
  have : PreservesFiniteColimits G := inferInstance
  let DF := F.mapDerivedCategory
  let DG := G.mapDerivedCategory
  let a : F ⊣ G := Mod.extendRestrictAdjunction (inclusion l E T)
  Nonempty (F.leftDerivedFunctor ≅ DF) ∧
  Nonempty (G.rightDerivedFunctor ≅ DG) ∧
  Nonempty (DF.CommShift ℤ) ∧
  Nonempty (DG.CommShift ℤ) ∧
  DF.IsTriangulated ∧
  DG.IsTriangulated ∧
  (∀ P, IsIso (F.mapDerivedCategoryFactors.hom.app P)) ∧
  (∀ P, IsIso (G.mapDerivedCategoryFactors.hom.app P)) ∧
  ∀ P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (integralRing l E T)) ℤ,
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj P) ≫
        DG.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P)

/-- All-complex derived computation and the normalized derived unit.
Source: exact derived functor comparisons and the exact derived adjunction unit.
(blueprint: lem-weil-pbc-normalized-realization-clauses).
Proof: exactness supplies both total-derived comparisons with the termwise
localization. The latter has its canonical shifts and preserves triangles.
Its comparison components are isomorphisms on every complex. The unit formula
is the component formula for the localization of the ordinary adjunction. -/
theorem derived_scalar_data : DerivedScalarData l E T := by
  let F := ordinaryExtension l E T
  let G := ordinaryRestriction l E T
  refine ⟨⟨F.leftDerivedFunctorIsoMapDerivedCategory⟩,
    ⟨G.rightDerivedFunctorIsoMapDerivedCategory⟩,
    ⟨inferInstance⟩, ⟨inferInstance⟩, inferInstance, inferInstance,
    (fun P ↦ inferInstance), (fun P ↦ inferInstance), ?_⟩
  intro P
  exact CategoryTheory.Adjunction.mapExactDerivedCategory_unit (F := F) (G := G)
    (Mod.extendRestrictAdjunction (inclusion l E T)) P

/-- The exact ordinary and derived scalar clauses together.
Source: the canonical scalar adjunction and exact-derived factorization.
(blueprint: lem-weil-pbc-normalized-realization-clauses).
Proof: combine the explicit ordinary unit with the all-complex derived-unit formula. -/
theorem realization_clauses : ScalarAdjunctionData l E T ∧ DerivedScalarData l E T :=
  ⟨scalar_adjunction_data l E T, derived_scalar_data l E T⟩

end WeilConjectures.NormalizedScalar
