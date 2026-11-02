/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor

/-! # Canonical condensed point tensor comparison normalization

Source: `thm-sf-kunneth-relative.proof.md`, Step 5, together with
`def-weil-finite-coefficient-point` and `def-weil-derived-pullback-tensor-hom`
(blueprint: def-sf-point-fibre-tensor-models).

The definition records a natural comparison on the finite-Tor constructible point
subcategory and its coefficient-unit normalization. The tensor comparison and unit
used in the normalization are the native condensed constructions of
`def-pod-condensed-point-tensor`; no finite-stage, completion, Roos, or adic model is
introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ambient derived category of native coefficient modules at the point.
Source: `def-weil-derived-pullback-tensor-hom`
(blueprint: def-sf-point-fibre-tensor-models). -/
abbrev pointSiteDerived (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :=
  DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))

/-- The ordinary derived category over the section ring `Λ(*)`.
Source: `def-weil-finite-coefficient-point`
(blueprint: def-sf-point-fibre-tensor-models). -/
abbrev pointOrdinaryDerived (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  DerivedCategory (ModuleCat (MonObj.Γ Λ))

/- The family is a natural isomorphism in both variables, written with its
   component isomorphisms and the two naturality equations. -/
/-- The coefficient-unit arrow fixed by the normalized native section tensor data.
Source: `def-pod-condensed-point-tensor` (blueprint: def-sf-point-fibre-tensor-models). -/
def pointCoefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    𝟙_ (pointOrdinaryDerived Λ) ⟶
      (CondensedRing.TraceCupPoint.fiber Λ k).obj
        (𝟙_ (pointSiteDerived Λ k)) :=
  (CondensedRing.TraceCupPoint.tensorData Λ k).derived.ε ≫
    (CondensedRing.TraceCupPoint.exactComparison Λ k).inv.app
      (𝟙_ (pointSiteDerived Λ k))

end AlgebraicGeometry.ProEtale.CondensedRing
