/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison

/-! # Exact-functor presentations of normalized coherent comparisons

Source: Stacks Project, Tags 03P2 and 03FD. The data below concern sheaves and
sections; their induced maps in every cohomological degree are constructed by Ext.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

namespace CoherentEtale

attribute [local irreducible] tensorPullback tensorPullbackObj
  tensorSectionsUnit coherentEtaleMap sourceZero

local instance (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Abelian sheaves on the small Zariski site.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
abbrev ZariskiAbelian (X : Scheme.{u}) :=
  Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The integer sheaf defining the large Zariski Ext presentation.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
abbrev zariskiInteger (X : Scheme.{u}) : ZariskiAbelian X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- The integer sheaf defining etale cohomology.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
abbrev etaleInteger (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The section equation for exact comparison data.
Source: Stacks Project, Tag 03FD.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
@[irreducible] def SectionNormalization {X : Scheme.{u}}
    (P : ZariskiAbelian X ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (integer : etaleInteger X ⟶ P.obj (zariskiInteger X))
    (coefficient : ∀ (F : X.Modules) [F.IsQuasicoherent],
      P.obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ⟶ Coeff F) : Prop :=
  ∀ (F : X.Modules) [F.IsQuasicoherent] (x : Source X F 0),
    (P.map (Abelian.Ext.addEquiv₀ x) ≫ coefficient F).hom.app (op (⊤_ X.Etale))
        (Sheaf.H.equiv₀ (P.obj (zariskiInteger X)) terminalIsTerminal
          (Abelian.Ext.mk₀ integer)) =
      ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F (sourceZero X F x))

attribute [local irreducible] Coeff

/-- An exact-functor presentation, with coefficient naturality and its section unit.
All data are supplied explicitly. No comparison on positive-degree cohomology is
part of this structure.
Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
structure ExactComparison (X : Scheme.{u}) where
  P : ZariskiAbelian X ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  additive : P.Additive
  limits : PreservesFiniteLimits P
  colimits : PreservesFiniteColimits P
  integer : etaleInteger X ⟶ P.obj (zariskiInteger X)
  coefficient : ∀ (F : X.Modules) [F.IsQuasicoherent],
    P.obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ⟶ Coeff F
  naturality : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G),
    P.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫ coefficient G =
      coefficient F ≫ coherentEtaleMap F G φ
  zero : SectionNormalization P integer coefficient

attribute [instance] ExactComparison.additive ExactComparison.limits ExactComparison.colimits

attribute [local irreducible] CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.mapExactFunctor CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Sheaf.H.equiv₀


namespace ExactComparison

/-- The additive Ext map induced by exact functor data.
Source: Stacks Project, Tag 03FD; functoriality of Ext.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
def extMap {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {S : A} {T : B} (b : T ⟶ P.obj S) {M : A} {N : B}
    (a : P.obj M ⟶ N) (q : ℕ) : Abelian.Ext S M q →+ Abelian.Ext T N q :=
  { toFun := fun x ↦
      ((Abelian.Ext.mk₀ b).comp (x.mapExactFunctor P) (zero_add q)).comp
        (Abelian.Ext.mk₀ a) (add_zero q)
    map_zero' := by
      rw [Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.comp_zero, Abelian.Ext.zero_comp]
    map_add' := by
      intro x y
      rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.comp_add, Abelian.Ext.add_comp] }

/-- Apply the exact functor to an Ext class and compose with the two specified maps.
Source: Stacks Project, Tag 03FD.
(blueprint: def-pbc-coherent-etale-exact-comparison). -/
def map {X : Scheme.{u}} (D : ExactComparison X)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) : Source X F q →+ Target X F q :=
  extMap D.P D.integer (D.coefficient F) q

end ExactComparison
end CoherentEtale
end
end AlgebraicGeometry.Scheme.Modules
