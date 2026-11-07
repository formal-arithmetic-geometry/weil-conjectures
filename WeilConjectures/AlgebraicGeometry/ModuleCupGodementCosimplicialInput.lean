/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelPairing
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Cosimplicial input for the Godement cup product -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section


/-- Extend the unnormalized alternating coface complex by zero in negative degrees.
Source: Stacks Project, Tag 0FKR (blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialComplex (X : Scheme.{u}) (A : CosimplicialObject X.Modules) :
    CochainComplex X.Modules ℤ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extend ComplexShape.embeddingUpNat

/-- The degree-zero identification with the cosimplicial term.
Source: Stacks Project, Tag 0FKR (blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialZeroIso (X : Scheme.{u}) (A : CosimplicialObject X.Modules) :
    (moduleCup_cosimplicialComplex X A).X 0 ≅ A.obj ⦋0⦌ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
    ComplexShape.embeddingUpNat (i := 0) rfl

/-- Pointwise tensor product of two cosimplicial objects.
Source: Stacks Project, Tag 0FKR
(blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialTensor (X : Scheme.{u})
    (A B : CosimplicialObject X.Modules) : CosimplicialObject X.Modules :=
  CategoryTheory.Monoidal.FunctorCategory.tensorObj
    (C := SimplexCategory) (D := X.Modules) A B

/-- The degree-zero pairing induced by a pointwise cosimplicial tensor morphism.
Source: Stacks Project, Tag 0FKR (blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialZeroPair (X : Scheme.{u})
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    (moduleCup_cosimplicialComplex X A).X 0 ⊗
      (moduleCup_cosimplicialComplex X B).X 0 ⟶ (moduleCup_cosimplicialComplex X C).X 0 :=
  ((moduleCup_cosimplicialZeroIso X A).hom ⊗ₘ
    (moduleCup_cosimplicialZeroIso X B).hom) ≫ μ.app ⦋0⦌ ≫
    (moduleCup_cosimplicialZeroIso X C).inv


end
end AlgebraicGeometry.Scheme.Modules
