/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFamily

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-geometric-base-change). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Composition retains its specified proper/open compactification model.
Source: composition clause (blueprint: def-pur-transport-geometric-base-change). -/
def SmoothDatum.comp {D : WeilConjectures.FiniteFieldDatum.{u}}
    (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)) :
    SmoothDatum D :=
  { X := s.X
    Y := Z
    map := s.map ≫ g
    dim := s.dim + e
    compactification := compositeCompactification s.compactification cg cr }

end AlgebraicGeometry.ProEtale.PurityTransport
