/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-affine-index). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The actual affine-line projection with its standard projective compactification.
Source: affine-line normalization (blueprint: def-pur-transport-affine-index). -/
def affineDatum (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y : Over (Spec (.of D.k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] : SmoothDatum D := by
  let p := AffineSpace PUnit.{u + 1} Y.left ↘ Y.left
  letI : (AffineSpace PUnit.{u + 1} Y.left).Over (Spec (.of D.k)) := ⟨p ≫ Y.hom⟩
  letI : p.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let X : Over (Spec (.of D.k)) := Over.mk (p ≫ Y.hom)
  letI : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (p ≫ Y.hom)
    infer_instance
  letI : QuasiCompact X.hom := by
    change QuasiCompact (p ≫ Y.hom)
    infer_instance
  letI : IsSeparated X.hom := by
    change IsSeparated (p ≫ Y.hom)
    infer_instance
  letI : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_unique] using
      AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} Y.left
  exact
    { X := X
      Y := Y
      map := p
      dim := 1
      compactification := affineTraceLineCompactification Y.left }

end AlgebraicGeometry.ProEtale.PurityTransport
