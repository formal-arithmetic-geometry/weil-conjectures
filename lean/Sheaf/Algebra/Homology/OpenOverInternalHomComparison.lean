/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.InternalHomOverEquiv
import Sheaf.Algebra.Homology.InternalHomOverNaturality

/-! # Composite open restriction comparison -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverInternalHomComparisonCategory
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverInternalHomComparisonPreadditive
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000) openOverInternalHomComparisonAbelian
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf



set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Scheme.Modules.overEquiv Scheme.Modules.overFunctorEquiv
attribute [local irreducible] Scheme.Modules.restrictFunctor SheafOfModules.overFunctor


/-- Composite restriction commutes naturally with internal Hom.
Source: Stacks Project, Tag 08DL, restriction of internal Hom.
(blueprint: new-t4-open-over-internal-hom-comparison).

Proof: First use overHomObjIso for V. Transport it through the open-site
module equivalence using internalHom_overEquiv, then transport along the
natural isomorphism overFunctorEquiv from localized modules to restriction.
Finally apply overHomObjIso for W. Pre- and postcomposition commute with
all four comparisons; composing their naturality squares proves the formula.
All maps are reindexing maps on local linear morphisms, so the construction
also works for the empty open and for zero modules. -/
theorem openOver_internalHom_comparison (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    let F : X.Modules ⥤
      SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W) :=
      Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    ∃ e : ∀ M N : X.Modules,
      F.obj (SheafOfModules.homObj (R := X.sheaf) M N) ≅
        SheafOfModules.homObj (R := V.toScheme.sheaf.over W) (F.obj M) (F.obj N),
      ∀ (M M' N N' : X.Modules) (f : M' ⟶ M) (g : N ⟶ N'),
        F.map (SheafOfModules.homObjMap (R := X.sheaf) f g) ≫ (e M' N').hom =
          (e M N).hom ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
            (F.map f) (F.map g) := by
  sorry

end CategoryTheory
