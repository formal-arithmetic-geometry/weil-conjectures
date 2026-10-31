/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemIso
public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemDomains
public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemAdjoints
public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemComparison

/-! # Scalar compatibility of tower purity

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md,
Proof (2), finite unit/counit/purity compatibilities in the tower category, using
the orientation comparison of rank-one tower sheaves.
(blueprint: lem-sp-field-tower-purity-square).

The source comparison is kept as the normalized scalar/pullback, Tate-line and
shift comparison supplied by the coefficient model.  The exceptional comparison
is the recorded counit mate, represented by `FieldExceptionalSystem.iso`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldTowerPuritySquare

open AlgebraicGeometry.ProEtale.FieldShriekSystem
open AlgebraicGeometry.ProEtale.FieldExceptionalSystem

/-- Coefficient extension preserves the normalized tower purity square.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md,
Proof (2), finite unit/counit/purity compatibilities in the tower category, using
the orientation comparison of rank-one tower sheaves.
(blueprint: lem-sp-field-tower-purity-square).

The hypotheses fix the finite-field datum, separated finite-type schemes, the
separated smooth morphism and compactification, the normalized model and laws,
and the two actual tower purity maps.  `s` is the normalized scalar/pullback,
Tate-line and shift comparison from the fixed coefficient model.  The conclusion
is the component equation and its naturality in every input morphism.  The proof
uses the tower mate identities, the proper/open comparison, and the balanced
K-flat tensor formula; it is intentionally postponed at this stage.
-/
theorem field_tower_purity_square
    (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f]
    (c : Compactification f)
    (D : Models P) (laws : FieldShriekSystem.Laws P D c)
    (a : Domains P D c) (A : Adjoints P D c laws a)
    (L : FieldExceptionalSystem.Laws P D c laws a A)
    {E F : Index P} (h : E ≤ F)
    (J_E : N P D E Y ⥤ N P D E X)
    (J_F : N P D F Y ⥤ N P D F X)
    (γ_E : J_E ≅ A.right E)
    (γ_F : J_F ≅ A.right F)
    (s : J_E ⋙ scalar P D a h X ≅ scalar P D a h Y ⋙ J_F) :
    let C_X := scalar P D a h X
    let C_Y := scalar P D a h Y
    let c := FieldExceptionalSystem.iso P D c laws a A L h
    Functor.whiskerRight γ_E.hom C_X ≫ c.hom ≫
      Functor.whiskerLeft C_Y γ_F.inv = s.hom := by
  sorry

end AlgebraicGeometry.ProEtale.FieldTowerPuritySquare
