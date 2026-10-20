/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Canonical composition maps for strict constant-coefficient towers

Source: Stacks Project, Tags 0F7J, 0F7C, 0F7D and 0F7F, and the strict-tower adaptation
in the blueprint (blueprint: def-cbc-strict-tower-composition-maps).

`Compactification.Triangle` names the node's maps as follows: `cf.i = c`, `cf.g = p_Y`,
`cg.i = i`, `cg.g = q`, `cfg.i = a`, `q = b`, and `p = p`.
All maps below are constructed in the derived category of strict towers, before evaluation.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The supplied-compactification functor `R_p J_j`.
Source: Stacks, Tag 0F7J
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionF {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Derived B X ⥤ Derived B Y := J B c.i ⋙ R B c.g

/-- The actual composition comparison `R_q gamma_Q J_c`, including both compositors.
Source: Stacks, Tag 0F7J
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionD {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF B T.cf ⋙ compositionF B T.cg ⟶ compositionF B T.cfg :=
  (Functor.associator (J B T.cf.i) (R B T.cf.g) (J B T.cg.i ⋙ R B T.cg.g)).hom ≫
  Functor.whiskerLeft (J B T.cf.i)
    ((Functor.associator (R B T.cf.g) (J B T.cg.i) (R B T.cg.g)).inv ≫
      Functor.whiskerRight (gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
        (R B T.cg.g) ≫
      (Functor.associator (J B T.q) (R B T.p) (R B T.cg.g)).hom) ≫
  (Functor.associator (J B T.cf.i) (J B T.q) (R B T.p ⋙ R B T.cg.g)).inv ≫
  Functor.whiskerRight
    ((jComp B T.cf.i T.q).hom ≫ (jCongr B T.i_q).hom)
    (R B T.p ⋙ R B T.cg.g) ≫
  Functor.whiskerLeft (J B T.cfg.i)
    ((rComp B T.p T.cg.g).hom ≫ (eqToIso (congrArg (R B) T.p_g)).hom)

/-- The refinement comparison is gamma for the identity-left square, followed by R.
Source: Stacks, Tag 0F7J, choice independence
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionC {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF B d ⟶ compositionF B c :=
  Functor.whiskerRight
    ((Functor.leftUnitor (J B d.i)).inv ≫
      Functor.whiskerRight (rId B X).inv (J B d.i) ≫
      gamma B c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
    (R B d.g) ≫
  (Functor.associator (J B c.i) (R B r.hom) (R B d.g)).hom ≫
  Functor.whiskerLeft (J B c.i)
    ((rComp B r.hom d.g).hom ≫ (eqToIso (congrArg (R B) r.hom_g)).hom)

/-- The specified exchange: first the proper-square mate, then the open comparison.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionE {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    compositionF B c ⋙ G B y ⟶ G B x ⋙ compositionF B c' :=
  (Functor.associator (J B c.i) (R B c.g) (G B y)).hom ≫
  Functor.whiskerLeft (J B c.i) (exchange B s c'.g c.g y wp) ≫
  (Functor.associator (J B c.i) (G B s) (R B c'.g)).inv ≫
  Functor.whiskerRight (beta B x c'.i c.i s wi si).hom (R B c'.g) ≫
  (Functor.associator (G B x) (J B c'.i) (R B c'.g)).hom

/-- A refinement of the supplied towers consists of the three existing compactification
refinements and the two remaining compatibility equations. No cartesian condition is imposed.
Source: Stacks, Tag 0F7J, refinement diagram; compatible-tower dependency
(blueprint: def-cbc-strict-tower-composition-maps). -/
structure CompositionRefinement {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T₁ T₂ : Compactification.Triangle f h) where
  rf : T₁.cf.Refinement T₂.cf
  rh : T₁.cg.Refinement T₂.cg
  rfh : T₁.cfg.Refinement T₂.cfg
  b_comm : T₁.q ≫ rfh.hom = rf.hom ≫ T₂.q
  p_comm : rfh.hom ≫ T₂.p = T₁.p ≫ rh.hom

/-- The horizontal refinement `(C_h F_f1)(F_h2 C_f)`.
Source: Stacks, Tag 0F7J
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionH {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    {T₁ T₂ : Compactification.Triangle f h}
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i]
    (r : CompositionRefinement T₁ T₂) :
    compositionF B T₂.cf ⋙ compositionF B T₂.cg ⟶
      compositionF B T₁.cf ⋙ compositionF B T₁.cg :=
  Functor.whiskerRight (compositionC B r.rf) (compositionF B T₂.cg) ≫
    Functor.whiskerLeft (compositionF B T₁.cf) (compositionC B r.rh)

/-- The cartesian faces of a base change of a supplied compatible tower. All arrows
are supplied projections; this does not choose a compactification or an arbitrary comparison.
Source: Stacks, Tags 0F7J and 0F7F; compatible-tower dependency
(blueprint: def-cbc-strict-tower-composition-maps). -/
structure CompositionBaseChange {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z) where
  d : T'.cf.Z ⟶ T.cf.Z
  t : T'.cg.Z ⟶ T.cg.Z
  s : T'.cfg.Z ⟶ T.cfg.Z
  cf_i : IsPullback x T'.cf.i T.cf.i d
  cf_g : IsPullback d T'.cf.g T.cf.g y
  cg_i : IsPullback y T'.cg.i T.cg.i t
  cg_g : IsPullback t T'.cg.g T.cg.g g
  cfg_i : IsPullback x T'.cfg.i T.cfg.i s
  cfg_g : IsPullback s T'.cfg.g T.cfg.g g
  b : IsPullback d T'.q T.q s
  p : IsPullback s T'.p T.p t

/-- Exchange for f on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionEf {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cf T'.cf x y A.d A.cf_i.w A.cf_g.w A.cf_i

/-- Exchange for h on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionEh {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cg T'.cg y g A.t A.cg_i.w A.cg_g.w A.cg_i

/-- Exchange for hf on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionEhf {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cfg T'.cfg x g A.s A.cfg_i.w A.cfg_g.w A.cfg_i

/-- The horizontal exchange `(F_h' e_f)(e_h F_f)` with explicit associators.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionHorizontalE {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    (compositionF B T.cf ⋙ compositionF B T.cg) ⋙ G B g ⟶
      G B x ⋙ (compositionF B T'.cf ⋙ compositionF B T'.cg) :=
  (Functor.associator (compositionF B T.cf) (compositionF B T.cg) (G B g)).hom ≫
  Functor.whiskerLeft (compositionF B T.cf) (compositionEh B A) ≫
  (Functor.associator (compositionF B T.cf) (G B y) (compositionF B T'.cg)).inv ≫
  Functor.whiskerRight (compositionEf B A) (compositionF B T'.cg) ≫
  (Functor.associator (G B x) (compositionF B T'.cf) (compositionF B T'.cg)).hom

end AlgebraicGeometry.ProEtale.StrictTower
