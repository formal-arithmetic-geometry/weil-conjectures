/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj.BoundedConstructibleTensorSingle
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-! # BoundedConstructibleTensorPreservation

The tensor unit and the two finite truncation inductions for tensor closure.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The derived tensor of two bounded constructible module-object complexes is bounded
constructible, for any coefficient ring whose bounded constructible category is triangulated
and satisfies the degree-zero tensor calculation `hsingle` (`boundedConstructible_tensor_single`).
Source: `lem-sfb-dc-tensor-preserves` in the blueprint.
(blueprint: lem-sfb-dc-tensor-preserves) -/
private theorem boundedConstructible_tensor_closure_of
    (htri : (boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated)
    (hsingle : ∀ F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      IsConstructibleModuleObject (condensedRingObj Λ X.left) G →
      boundedConstructible (condensedRingObj Λ X.left)
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G))
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K)
    (hL : boundedConstructible (condensedRingObj Λ X.left) L) :
    boundedConstructible (condensedRingObj Λ X.left)
      (((-⊗ᴸ-(X.left)⟦Λ⟧).obj K).obj L) := by
  let P := boundedConstructible (condensedRingObj Λ X.left)
  have : P.IsTriangulated := htri
  change P (K ⊗ L)
  apply prop_of_boundedConstructibleModule (P.inverseImage (tensorLeft K)) ?_ hL
  intro G hG
  exact prop_of_boundedConstructibleModule
    (P.inverseImage (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)))
    (fun F hF ↦ hsingle F G hF hG) hK

variable {X}

private theorem isNoetherian_left : IsNoetherian X.left :=
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  ⟨⟩

/-- The derived tensor of two bounded constructible complexes is bounded constructible,
`ℚ̄_ℓ` coefficients. This is the tensor-closure clause of the ell-adic finiteness theorem.
Source: `lem-sfb-dc-tensor-preserves` in the blueprint.
(blueprint: lem-sfb-dc-tensor-preserves) -/
theorem boundedConstructible_tensor_closure
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      (((-⊗ᴸ-(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj K).obj L) :=
  have := isNoetherian_left (X := X)
  boundedConstructible_tensor_closure_of _ X
    (isTriangulated_boundedConstructible_ellAdic_padicAlgCl X.left ℓ)
    (fun F G hF hG ↦ boundedConstructible_tensor_single ℓ X F G hF hG) K L hK hL

namespace ContinuousMapRingObj

end ContinuousMapRingObj

namespace PadicIntegersRingObj

end PadicIntegersRingObj

namespace UnitBallRingObj

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
