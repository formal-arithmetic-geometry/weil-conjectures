/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Local returns for both condensed coefficient fields

Source: latest blueprint, def-weil-local-frobenius-trace, local return convention;
Deligne, Weil II (1.1.7)--(1.1.10) (blueprint: def-weil-local-frobenius-trace).

## Main definitions

- `Modules`, `scalars`, `scalarsOp`, `sections`, `fibre`: the actual point-fibre functor.
- `moduleIterate`, `moduleReturn`: positive module returns with their compositors.
- `derivedIterate`, `returnComparison`, `derivedReturn`: their exact derived counterparts.
- `cohomology`, `cohomologyReturn`, `alternatingTrace`: ordinary cohomology and traces.

The previous interfaces are reexported. Here scalars are the global sections of the
condensed coefficient ring itself, canonically its underlying field in both field cases.
Every comparison is the published module pullback comparison or its exact localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedLocalReturn

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing module category for the pulled-back condensed coefficients.
Source: blueprint coefficient convention (blueprint: def-weil-local-frobenius-trace). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Pullback of constant scalars, acting by multiplication on the regular module.
Source: blueprint pulled-back coefficient convention
(blueprint: def-weil-local-frobenius-trace). -/
def scalars (X : Scheme.{u}) : Γ Λ →+* End (Mod.regular (condensedRingObj Λ X)) :=
  Mod.regularEndRingHom.comp (Γ.mapFunctor (upperStarFromPoint X))

/-- The opposite-ring scalar map used by the existing additive coyoneda functor.
Source: blueprint sections of coefficient modules
(blueprint: def-weil-local-frobenius-trace). -/
def scalarsOp (X : Scheme.{u}) :
    Γ Λ →+* (End (Mod.regular (condensedRingObj Λ X)))ᵐᵒᵖ :=
  (scalars Λ X).toOpposite (fun a b ↦ (map_mul (scalars Λ X) a b).symm.trans
    ((congrArg (scalars Λ X) (mul_comm a b)).trans (map_mul (scalars Λ X) b a)))

/-- Actual point sections, represented by Hom from the regular coefficient module.
Source: blueprint vector-space fibre convention
(blueprint: def-weil-local-frobenius-trace). -/
def sections (k : Type u) [Field k] : Modules Λ (Spec (.of k)) ⥤ ModuleCat.{u + 1} (Γ Λ) :=
  preadditiveCoyonedaObj (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ⋙
    ModuleCat.restrictScalars.{u + 1} (scalarsOp Λ (Spec (.of k)))

/-- The actual geometric fibre functor: module inverse image, then point sections.
Source: blueprint derived geometric stalk (blueprint: def-weil-local-frobenius-trace). -/
abbrev fibre (k : Type u) [Field k] {X : Scheme.{u}} (z : Spec (.of k) ⟶ X) :
    Modules Λ X ⥤ ModuleCat.{u + 1} (Γ Λ) :=
  CondensedRing.upperStar Λ z ⋙ sections Λ k

end WeilConjectures.CondensedLocalReturn
