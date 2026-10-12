/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # The sheaf of compatible local module sections

Source: Stacks Project, Sheaves, Tags 00AL (first proof) and 00AM.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Local sections on every subopen of a cover member inside `V`.
Source: Stacks, Tag 00AL, first proof, with intersection sections expanded by restriction.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
abbrev OpenModuleFamily (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (V : Opens X) :=
  ∀ (i : I) (W : Opens X) (hi : W ≤ U i) (_ : W ≤ V),
    (Fi i).val.obj (op (Over.mk (homOfLE hi)))

/-- A local family respects restrictions and the given overlap maps.
Source: Stacks, Tags 00AL and 00AM, compatible-family equalizer.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
def OpenModuleFamilyCoherent (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (V : Opens X) (a : OpenModuleFamily X I U Fi V) : Prop :=
  (∀ (i : I) (W Z : Opens X) (hi : W ≤ U i) (hWV : W ≤ V) (hZW : Z ≤ W),
    (Fi i).val.map (Over.homMk (homOfLE hZW)).op (a i W hi hWV) =
      a i Z (hZW.trans hi) (hZW.trans hWV)) ∧
  (∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V),
    (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) (a i W hi hWV) =
      a j W hj hWV)

/-- Evaluate a global section through a local projection after restricting it.
Source: Stacks, Tag 00AL, projection of the compatible-family equalizer.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
noncomputable abbrev openModuleFamilyEval
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (H : SheafOfModules.{max u v} (moduleRings X))
    (π : ∀ i : I, H.over (U i) ⟶ Fi i) (V : Opens X)
    (s : H.val.obj (op V)) : OpenModuleFamily X I U Fi V :=
  fun i _W hi hWV => (π i).val.app (op (Over.mk (homOfLE hi)))
    (H.val.map (homOfLE hWV).op s)

/-- The compatible-family equalizer is represented by a module sheaf with projections.
No diagonal or cocycle assumption is needed for this construction.
Source: Stacks Project, Sheaves, Tags 00AL (first proof, construction and sheaf axiom)
and 00AM (module structure on the equalizer).
(blueprint: lem-weil-pbc-module-compatible-family-sheaf)

Proof: on an open V take families in Fi i(V ∩ U i) whose restrictions are identified
by every overlap map. They form a submodule, since the transition maps are linear.
Restrictions are componentwise and preserve the equalizer by naturality. Gluing is
componentwise in the local sheaves; the equations hold after gluing by separation
on the induced covering of each overlap. This proves the sheaf axiom. Projection
on a component, followed by restriction, defines π i and gives its compatibility.
A family on all subopens is determined by its component on V ∩ U i; its restriction
and overlap equations are precisely those of this equalizer. Hence all coherent
families are evaluations of global sections, and equality of evaluations implies
equality of sections.

For the universe bound, choose a cover member through each point of X. The resulting
subcover is indexed in universe u. Compatible families on the full cover inject into
the product of the components on this subcover: for each original member, its
components are determined on its intersections with the subcover by the overlap
isomorphisms, and then by separation. The full compatible-family module is therefore
small in universe max u v. Shrink this explicit module, transport its restrictions
and module structures through the shrinking equivalences, and obtain H. This changes
no equations or universal properties. For the empty space the equalizer is the zero
module, since every local sheaf has a unique section on the empty open. -/
theorem module_compatible_family_sheaf
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    : ∃ (H : SheafOfModules.{max u v} (moduleRings X))
      (π : ∀ i : I, H.over (U i) ⟶ Fi i),
      ∀ V : Opens X,
        (∀ s : H.val.obj (op V),
          OpenModuleFamilyCoherent X I U Fi φij V
            (openModuleFamilyEval X I U Fi H π V s)) ∧
        Function.Injective (openModuleFamilyEval X I U Fi H π V) ∧
        (∀ a : OpenModuleFamily X I U Fi V,
          OpenModuleFamilyCoherent X I U Fi φij V a →
            ∃ s : H.val.obj (op V), openModuleFamilyEval X I U Fi H π V s = a) := by sorry

end AlgebraicGeometry
