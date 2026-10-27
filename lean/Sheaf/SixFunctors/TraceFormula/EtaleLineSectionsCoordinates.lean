/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Module-valued tensor-section coordinates for invertible modules

Source: Stacks Project, Descent, Tags 03DR, 03DX, 03LC and 05VG.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Construction of the section functor and its normalized unit and restriction maps.
Source: Stacks Project, Descent, Tags 03DR (equation-quasi-coherent-presheaf),
03DX (proposition-equivalence-quasi-coherent (2)), 03LC (1), and 05VG.
(blueprint: lem-trf-etale-line-sections-coordinates)

Proof: Equip the tensor-section presheaf with its sectionwise module action.
The semilinearity of its normalized restrictions makes this a module presheaf;
quasi-coherent descent makes it a sheaf without changing any sections. On a module
map use the maps on sections of its tensor pullbacks. Naturality of the adjunction
unit and of tensorSectionsComp proves restriction naturality. The functor laws are
those of tensor pullback. The additive coordinate isomorphism is the identity, so
its scalar and module-map equations follow from the construction.

The adjoint structure-module comparison sends a local tensor a tensor b to
 a times u-sharp(b), with inverse a to a tensor 1. Its unit equation and the
balanced relation prove that these maps are inverse. The tensor-unit restriction
equation proves naturality, giving epsilon and its displayed coordinate formula.
Tensor pullback preserves invertibility: compare it by adjoint uniqueness with
Mathlib's module pullback, which preserves Zariski rank-one trivializations.

At w over Y define beta by sections of the inverse of tensorSectionsComp w v.
Adjunction-unit naturality and left-adjoint composition associativity give its
restriction square; its linearity follows because the comparison is a module map.
Thus it is an isomorphism of module presheaves with exactly the stated coordinates.
Finally choose a Zariski trivializing cover of each invertible module. Its image is
an etale cover. Beta, the image of a chosen frame, and epsilon trivialize the
constructed module on each localized site: the slice of the small etale site at
an etale U over X identifies with the small etale site of U, including its ring
presheaf, by composition of structure maps. These are genuine local frames and
prove the image is a line module. Restricting the constructed functor to these
full subcategories gives A. No coherence law for beta or inverse formula for
epsilon is asserted here. All constructions allow an empty scheme and empty cover.
-/
theorem etale_line_sections_coordinates :
    ∃ (A : ∀ X : Scheme.{u}, TrfInvertibleModules X ⥤ TrfEtaleLineModules X)
      (α : ∀ (X : Scheme.{u}) (L : TrfInvertibleModules X),
        trfLineSections ((A X).obj L) ≅ trfInvertibleSections L)
      (ε : ∀ X : Scheme.{u},
          ((A X).obj (trfStructureInvertible X)).obj ≅
            SheafOfModules.unit (trfEtaleStructureRing X))
      (p : ∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X),
          ((Modules.tensorPullback v).obj L.obj).IsInvertible)
        (β : ∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X),
          (PresheafOfModules.pushforward₀ (trfEtaleCompose v)
            (trfEtaleStructureRing X).obj).obj ((A X).obj L).obj.val ≅
          ((A Y).obj ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).obj.val),
      (∀ (X : Scheme.{u}) (L : TrfInvertibleModules X) (U : X.Etale)
        (r : Γ(U.left, ⊤)) (s : ((A X).obj L).obj.val.obj (op U)),
        (α X L).hom.hom.app (op U) (r • s) =
          (((Modules.tensorPullback U.hom).obj L.obj).smul r).hom
            ((α X L).hom.hom.app (op U) s)) ∧
      (∀ (X : Scheme.{u}) (L K : TrfInvertibleModules X) (h : L.obj ⟶ K.obj)
        (U : X.Etale) (s : ((A X).obj L).obj.val.obj (op U)),
        (α X K).hom.hom.app (op U)
          ((trfComparisonMap (A X) h).val.app (op U) s) =
        ((Modules.tensorPullback U.hom).map h).app ⊤ ((α X L).hom.hom.app (op U) s)) ∧
      (∀ (X : Scheme.{u}) (U : X.Etale)
        (s : ((A X).obj (trfStructureInvertible X)).obj.val.obj (op U)),
        (ε X).hom.val.app (op U) s = (trfTensorUnit U.hom).hom.app ⊤
          ((α X (trfStructureInvertible X)).hom.hom.app (op U) s)) ∧
        (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (L : TrfInvertibleModules X)
          (W : Y.Etale) (s : ((A X).obj L).obj.val.obj
            (op ((trfEtaleCompose v).obj W))),
          (α Y ⟨(Modules.tensorPullback v).obj L.obj, p X Y v L⟩).hom.hom.app (op W)
              ((β X Y v L).hom.app (op W) s) =
            ((Modules.tensorSectionsComp W.hom v).inv.app L.obj).app ⊤
              ((α X L).hom.hom.app (op ((trfEtaleCompose v).obj W)) s)) := by
  sorry

end AlgebraicGeometry.Scheme
