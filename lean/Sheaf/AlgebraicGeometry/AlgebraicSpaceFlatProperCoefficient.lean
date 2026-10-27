/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Relative flatness and annihilator support for algebraic-space modules

Source: Stacks Project, Morphisms of Spaces, relative flatness; Cohomology of Spaces,
Tag 0A1P (blueprint: def-sfb-space-flat-proper-coefficient).
Support is specified on every étale chart by its annihilator ideal, so the existential
closed immersion is the specified closed subspace, rather than an arbitrary carrier.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative flatness on all compatible étale scheme charts. On quasi-coherent modules
this is equivalent to flatness of geometric stalks over the target local ring.
Source: Stacks, Morphisms of Spaces, relative flatness, and Tag 0A1P
(blueprint: def-sfb-space-flat-proper-coefficient). -/
def ModuleIsFlatOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (M : X.Modules) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (h : U.obj.left ⟶ V.obj.left),
    U.obj.hom ≫ f.hom.hom = yoneda.map h ≫ V.obj.hom →
      ((schemeRestriction X U).obj M).IsFlatOver h.left

/-- The module's annihilator closed subspace is proper over the target.
On every étale chart, every representing pullback has exactly the annihilator ideal
on each affine open, not merely the same underlying point set.
Source: Stacks, Tag 0A1P; Modules, annihilator support
(blueprint: def-sfb-space-flat-proper-coefficient). -/
def HasProperAnnihilatorSupport {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (M : X.Modules) : Prop :=
  ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
    MapIsProper (i ≫ f) ∧
    ∀ (T : X.EtaleSite) (W : Over S) (p : W ⟶ T.obj.left)
      (q : yoneda.obj W ⟶ Z.obj.obj),
      IsPullback q (yoneda.map p) i.hom.hom T.obj.hom →
      ∀ V : ((etaleForget X).obj T).affineOpens,
        p.left.ker.ideal V = Module.annihilator
          (Γ((etaleForget X).obj T, V.1))
          (((schemeRestriction X T).obj M).val.obj (op V.1))

end AlgebraicGeometry.AlgebraicSpace
