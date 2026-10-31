/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.CategoryTheory.CochainCoefficientUniverseTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Quasi-coherent algebra sheaves on an algebraic space

Source: Stacks Project, Morphisms of Spaces, Tags 081V and 081W, and the affine
ring tests in Tags 03ZQ and 0410 (blueprint: def-sfb-space-quasi-coherent-algebra).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Regular functions satisfy the sheaf condition as commutative rings.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: def-sfb-space-quasi-coherent-algebra).
Proof: the underlying ring presheaf is `structurePresheaf`. Its existing sheaf condition
is the unique-gluing condition on the same sections; forgetting commutativity changes
neither compatible families nor their unique amalgamations. -/
theorem commStructurePresheaf_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf X.etaleTopology (X.etaleForget.op ⋙ Scheme.Γ) := by
  sorry

/-- The existing regular-functions structure sheaf, retaining commutativity.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
def commStructureSheaf (X : AlgebraicSpace S) : Sheaf X.etaleTopology CommRingCat.{u} :=
  ⟨X.etaleForget.op ⋙ Scheme.Γ, commStructurePresheaf_isSheaf X⟩

/-- Commutative algebra sheaves and their structure-preserving ring-sheaf maps.
Source: Stacks, Morphisms of Spaces, Tag 081V
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
abbrev CommAlgebraSheaf (X : AlgebraicSpace S) := Under X.commStructureSheaf

/-- The underlying module: restrict the algebra's unit module along its structure map.
Source: Stacks, Morphisms of Spaces, Tag 081V; Modules on Sites, Tag 03DL
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
def CommAlgebraSheaf.toModule {X : AlgebraicSpace S} (A : X.CommAlgebraSheaf) : X.Modules :=
  (SheafOfModules.restrictScalars.{u, u, u, u + 1}
    ((sheafCompose.{u, u, u, u + 1, u + 1, u + 1} X.etaleTopology
      (forget₂ CommRingCat.{u} RingCat.{u})).map A.hom)).obj
    (SheafOfModules.unit.{u, u + 1, u}
      ((sheafCompose.{u, u, u, u + 1, u + 1, u + 1} X.etaleTopology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A.right))

/-- Quasi-coherent commutative algebra sheaves, as a full subcategory.
Source: Stacks, Morphisms of Spaces, Tag 081V
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
abbrev QCAlg (X : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory (fun A : X.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)

/-- Integrality on every affine étale chart, using the actual structure ring map.
Source: Stacks, Morphisms of Spaces, Tags 081V and 03ZQ
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
def CommAlgebraSheaf.IsIntegral {X : AlgebraicSpace S} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ V : X.EtaleSite, IsAffine (X.etaleForget.obj V) →
    (A.hom.hom.app (op V)).hom.IsIntegral

/-- Module finiteness on every affine étale chart.
Source: Stacks, Morphisms of Spaces, Tags 081V and 03ZQ
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
def CommAlgebraSheaf.IsFinite {X : AlgebraicSpace S} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ V : X.EtaleSite, IsAffine (X.etaleForget.obj V) →
    (A.hom.hom.app (op V)).hom.Finite

/-- Algebra finite presentation on every affine étale chart. This is polynomial algebra
finite presentation, not finite presentation of the underlying module.
Source: Stacks, Morphisms of Spaces, Tags 081V and 0410
(blueprint: def-sfb-space-quasi-coherent-algebra). -/
def CommAlgebraSheaf.IsFinitePresentation {X : AlgebraicSpace S}
    (A : X.CommAlgebraSheaf) : Prop :=
  ∀ V : X.EtaleSite, IsAffine (X.etaleForget.obj V) →
    (A.hom.hom.app (op V)).hom.FinitePresentation

end AlgebraicGeometry.AlgebraicSpace
