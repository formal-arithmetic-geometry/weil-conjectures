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

/-- Base change retains the literal fibre product and its recorded compactification.
Source: base-change clause (blueprint: def-pur-transport-geometric-base-change). -/
def SmoothDatum.baseChange {D : WeilConjectures.FiniteFieldDatum.{u}}
    (s : SmoothDatum D) (Y' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of D.k))] : SmoothDatum D := by
  let f' := pullback.snd s.map v
  letI : (pullback s.map v).Over (Spec (.of D.k)) := ⟨f' ≫ (Y'.left ↘ Spec (.of D.k))⟩
  letI : f'.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let X' : Over (Spec (.of D.k)) :=
    Over.mk (f' ≫ Y'.hom)
  letI : LocallyOfFiniteType X'.hom := by
    change LocallyOfFiniteType (f' ≫ Y'.hom)
    infer_instance
  letI : QuasiCompact X'.hom := by
    change QuasiCompact (f' ≫ Y'.hom)
    infer_instance
  letI : IsSeparated X'.hom := by
    change IsSeparated (f' ≫ Y'.hom)
    infer_instance
  exact
    { X := X'
      Y := Y'
      map := f'
      dim := s.dim
      compactification := s.compactification.baseChange v }

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
