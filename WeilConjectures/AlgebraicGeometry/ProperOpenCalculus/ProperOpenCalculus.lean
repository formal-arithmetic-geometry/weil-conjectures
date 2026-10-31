/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Tower
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.Compactification.CategoryBaseChange

/-!
# Abstract proper/open interchange data

Source: Stacks Project, Tags 0F7C, 0F7D, 0F7J and 0F7K, the formal pasting
calculus (blueprint: def-sp-proper-open-calculus).

`A` specifies the schemes in the ambient category. All arrows below are actual
scheme morphisms, and no category or functor outside `A` is required.
The compositors accept a named composite and its equality, avoiding hidden transports.
-/

@[expose] public section
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option linter.checkUnivs false in
namespace ProperOpenCalculus

attribute [instance] category

variable {A : Scheme.{u} → Prop} (F : ProperOpenCalculus.{u, v, w} A)

/-- The specified open/proper composite, not an independently chosen shriek functor.
Source: Stacks 0F7J (blueprint: def-sp-proper-open-calculus). -/
def H (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1}
    (c : Compactification f) (hc : A c.Z) [QuasiCompact f] : F.obj X ⥤ F.obj Y :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  F.J X ⟨c.Z, hc⟩ c.i ⋙ F.P ⟨c.Z, hc⟩ Y c.g

/-- Refinement comparison: insert the proper identity, apply the specified gamma,
then compose the proper functors. No cartesian hypothesis is imposed on the refinement.
Source: Stacks 0F7J (blueprint: def-sp-proper-open-calculus). -/
def rho (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1}
    {c d : Compactification f} (hc : A c.Z) (hd : A d.Z) (r : d.Refinement c) [QuasiCompact f] :
    F.H X Y c hc ≅ F.H X Y d hd :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  Functor.isoWhiskerRight
    ((Functor.leftUnitor (F.J X ⟨c.Z, hc⟩ c.i)).symm ≪≫
      Functor.isoWhiskerRight (F.pId X).symm (F.J X ⟨c.Z, hc⟩ c.i) ≪≫
      F.gamma X ⟨d.Z, hd⟩ X ⟨c.Z, hc⟩ d.i (𝟙 X.1) r.hom c.i
        (r.i_hom.trans (Category.id_comp c.i).symm)) (F.P ⟨c.Z, hc⟩ Y c.g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.J X ⟨d.Z, hd⟩ d.i)
      (F.pComp ⟨d.Z, hd⟩ ⟨c.Z, hc⟩ Y r.hom c.g d.g r.hom_g)

/-- Comparison from `c₂` to `c₁` computed on a supplied common refinement.
Source: Stacks 0F7J (blueprint: def-sp-proper-open-calculus). -/
def compare (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1}
    {c₁ c₂ d : Compactification f} (h₁ : A c₁.Z) (h₂ : A c₂.Z) (hd : A d.Z)
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂) [QuasiCompact f] :
    F.H X Y c₂ h₂ ≅ F.H X Y c₁ h₁ :=
  F.rho X Y h₂ hd r₂ ≪≫ (F.rho X Y h₁ hd r₁).symm

/-- The ambient membership certificates of a compatible binary tower.
Source: Stacks 0F7J (blueprint: def-sp-proper-open-calculus). -/
def TriangleObjects {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) : Prop :=
  A T.cf.Z ∧ A T.cg.Z ∧ A T.cfg.Z

/-- A refining tower has arbitrary proper refinements, with the two ambient compatibility
squares; no additional cartesianness over X or Y is required.
Source: Stacks 0F7J, six-square diagram (blueprint: def-sp-proper-open-calculus). -/
structure TowerRefinement {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T' T : Compactification.Triangle f g) where
  rf : T'.cf.Refinement T.cf
  rg : T'.cg.Refinement T.cg
  rfg : T'.cfg.Refinement T.cfg
  q_comm : T'.q ≫ rfg.hom = rf.hom ≫ T.q
  p_comm : rfg.hom ≫ T.p = T'.p ≫ rg.hom

/-- The tower transformation is gamma whiskered by the outside proper/open functors,
followed by the open and proper compositors.
Source: Stacks 0F7J (blueprint: def-sp-proper-open-calculus). -/
def towerIso (X Y Z : {X : Scheme.{u} // A X})
    {f : X.1 ⟶ Y.1} {g : Y.1 ⟶ Z.1} (T : Compactification.Triangle f g)
    (hT : TriangleObjects (A := A) T) [QuasiCompact f] [QuasiCompact g] :
    F.H X Y T.cf hT.1 ⋙ F.H Y Z T.cg hT.2.1 ≅ F.H X Z T.cfg hT.2.2 :=
  letI : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.cfg.i := T.cfg.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact T.q :=
    MorphismProperty.of_isPullback T.isPullback (inferInstance : QuasiCompact T.cg.i)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.J X ⟨T.cf.Z, hT.1⟩ T.cf.i)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (F.gamma ⟨T.cf.Z, hT.1⟩ ⟨T.cfg.Z, hT.2.2⟩ Y ⟨T.cg.Z, hT.2.1⟩
            T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
          (F.P ⟨T.cg.Z, hT.2.1⟩ Z T.cg.g) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (F.jComp X ⟨T.cf.Z, hT.1⟩ ⟨T.cfg.Z, hT.2.2⟩ T.cf.i T.q T.cfg.i T.i_q)
      (F.P ⟨T.cfg.Z, hT.2.2⟩ ⟨T.cg.Z, hT.2.1⟩ T.p ⋙
        F.P ⟨T.cg.Z, hT.2.1⟩ Z T.cg.g) ≪≫
    Functor.isoWhiskerLeft (F.J X ⟨T.cfg.Z, hT.2.2⟩ T.cfg.i)
      (F.pComp ⟨T.cfg.Z, hT.2.2⟩ ⟨T.cg.Z, hT.2.1⟩ Z T.p T.cg.g T.cfg.g T.p_g)

/-- The six ambient schemes of a three-map staircase belong to the specified category.
Source: Stacks 0F7K (blueprint: def-sp-proper-open-calculus). -/
def TowerObjects {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (T : Compactification.Tower f g h) : Prop :=
  A T.cf.Z ∧ A T.cg.Z ∧ A T.ch.Z ∧ A T.cfg.Z ∧ A T.cgh.Z ∧ A T.cfgh.Z

/-- The identification of the trivial identity compactification with the identity functor.
Source: Stacks 0F7K, identity towers (blueprint: def-sp-proper-open-calculus). -/
def identityIso (X : {X : Scheme.{u} // A X}) :
    F.H X X (Compactification.ofIsProper (𝟙 X.1)) X.2 ≅ 𝟭 (F.obj X) :=
  Functor.isoWhiskerRight (F.jId X) (F.P X X (𝟙 X.1)) ≪≫
    Functor.leftUnitor _ ≪≫ F.pId X

/-- Precisely the assumed geometric existence: cofiltered compactifications inside A,
common refining binary towers, and compatible three-map staircases. These are hypotheses,
not consequences of the proper/open axioms.
Source: Stacks 0F7J/0F7K, with the supplied-compactification formulation of
lem-cbc-compactifiable-compatible-tower (blueprint: def-sp-proper-open-calculus). -/
structure Geometry (A : Scheme.{u} → Prop) : Prop where
  nonempty (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ c : Compactification f, A c.Z
  common (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (_hc : A c.Z) (_hd : A d.Z) :
    ∃ e : Compactification f, A e.Z ∧ Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d)
  equalize (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (_hc : A c.Z) (_hd : A d.Z) (r s : c.Refinement d) :
    ∃ (e : Compactification f) (_he : A e.Z) (t : e.Refinement c), t.comp r = t.comp s
  compatible (X Y Z : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d : Compactification g) (c : Compactification (f ≫ g)) (_hd : A d.Z) (_hc : A c.Z) :
    ∃ (T : Compactification.Triangle f g), TriangleObjects (A := A) T ∧
      T.cg = d ∧ Nonempty (T.cfg.Refinement c)
  towers (X Y Z : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (T S : Compactification.Triangle f g)
    (_hT : TriangleObjects (A := A) T) (_hS : TriangleObjects (A := A) S) :
    ∃ (R : Compactification.Triangle f g), TriangleObjects (A := A) R ∧
      Nonempty (TowerRefinement R T) ∧ Nonempty (TowerRefinement R S)
  staircases (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    ∃ T : Compactification.Tower f g h, TowerObjects (A := A) T

end ProperOpenCalculus
end AlgebraicGeometry
