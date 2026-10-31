/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.Targets.PoincareTateBoundedConstructible
import WeilConjectures.SmoothPurity.RepresentingTraceClassification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # The trace normalized by its specified orientation

The counit transpose of a supplied orientation is the unique trace with that adjunct.
The geometric construction of the orientation belongs to `smoothOrientation` in
`WeilConjectures.SmoothPurity.Defs`; this categorical statement does not construct it.
The independent nonuniqueness result remains in `WeilConjectures.SmoothPurity.TraceNonuniqueness`.
-/

@[expose] public section
set_option autoImplicit false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

/-- Blueprint `def-pur-smooth-trace`: the **normalized smooth trace**. For a supplied
orientation `γ : M ≅ Rf^! U` of the shifted Tate object (the purity isomorphism `γ_f` of
`sk-prop-sp-orientation`, normalized by integration on the affine line), the composite
`Rf_! M ⟶ Rf_! Rf^! U ⟶ U` of `Rf_! γ` and the counit of `Rf_! ⊣ Rf^!` is the unique morphism
`Rf_! M ⟶ U` whose adjunct is `γ`, and it represents `Hom(-, M)`.

The orientation is part of the statement: Hom bijectivity alone does not determine the trace,
since precomposition with any automorphism of `M` (for instance `-1`) preserves it
(`not_existsUnique_representing_trace_at_point`, at a geometric point with `f = 𝟙`, `d = 0`).
Proof: `existsUnique_trace_of_orientation` for the chosen adjunction.
Source: def-pur-smooth-trace, def-route-smooth-trace.
(blueprint: lem-route-smooth-trace-representing-unique) -/
theorem existsUnique_smoothTrace
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ)
    (_hsm : SmoothOfRelativeDimension d f.left)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (_hM : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (γ : M ≅ (boundedConstructibleUpperShriek ℓ f).obj U) :
    ∃! t :
        (boundedConstructibleLowerShriek ℓ f).obj M ⟶ U,
      (∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ M ↦
          (boundedConstructibleLowerShriek ℓ f).map a ≫ t)) ∧
        (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv M U t = γ.hom :=
  existsUnique_trace_of_orientation _ (boundedConstructibleUpperShriekAdjunction ℓ f) γ


end AlgebraicGeometry.ProEtale.CondensedRing
