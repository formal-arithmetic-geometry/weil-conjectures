/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.Topology.Sheaves.Module
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Open section functors for module presheaves

Source: Stacks Project, Sheaves, Tags 00A0, 00A1, 008S and 008W
(blueprint: lem-weil-pbc-open-module-section-functors).

The open-subset site is represented by `Over U`: its objects are precisely opens
of `X` contained in `U`, and its coverings are the ordinary open coverings.
`U.overEquivalence` identifies this site with the opens of the subspace `U`.
The restricted ring sheaf is `(moduleRings X).over U`; the commutative ring
structure is inherited from `X.sheaf.over U`. No sheafification is used here.

## Main definitions

* `modulePresheafOpenRestriction`: retain sections and their module structures.
* `modulePresheafOpenDirectImage`: evaluate at the intersection, restricting scalars.
* `moduleSheafOpenRestriction` and `moduleSheafOpenDirectImage`: the corresponding
  functors on sheaves, using Mathlib's existing functors.

## Main statements

* `open_module_section_functors`: sheaf preservation, semilinearity, and the two
  identity-restriction computations for arbitrary module presheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace TopologicalSpace.Opens

/-- Retain the sections, actions, restrictions and linear morphism components on subopens.
Source: Stacks Project, Tags 00A0(1) and 00A1(4)
(blueprint: lem-weil-pbc-open-module-section-functors). -/
noncomputable abbrev modulePresheafOpenRestriction (X : RingedSpace.{u}) (U : Opens X) :
    PresheafOfModules.{w} (moduleRings X).obj ⥤
      PresheafOfModules.{w} ((moduleRings X).over U).obj :=
  PresheafOfModules.pushforward₀ (Over.forget U) (moduleRings X).obj

/-- On `V`, take sections on `U ∩ V`, with scalars restricted from `V`.
The components on morphisms are the original components on `U ∩ V`.
Source: Stacks Project, Tags 008S and 00A0
(blueprint: lem-weil-pbc-open-module-section-functors). -/
noncomputable abbrev modulePresheafOpenDirectImage (X : RingedSpace.{u}) (U : Opens X) :
    PresheafOfModules.{w} ((moduleRings X).over U).obj ⥤
      PresheafOfModules.{w} (moduleRings X).obj :=
  PresheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := moduleRings X) U).hom

/-- The restriction functor on module sheaves, retaining their sectionwise data.
Source: Stacks Project, Tags 00A0(2) and 00A1(4)
(blueprint: lem-weil-pbc-open-module-section-functors). -/
noncomputable abbrev moduleSheafOpenRestriction (X : RingedSpace.{u}) (U : Opens X) :
    ringedSiteModules.{w} (moduleRings X) ⥤
      ringedSiteModules.{w} ((moduleRings X).over U) :=
  SheafOfModules.overFunctor (moduleRings X) U

/-- The direct-image functor on module sheaves with the restriction-of-scalars action.
Source: Stacks Project, Tags 008W and 00A0(5)
(blueprint: lem-weil-pbc-open-module-section-functors). -/
noncomputable abbrev moduleSheafOpenDirectImage (X : RingedSpace.{u}) (U : Opens X) :
    ringedSiteModules.{w} ((moduleRings X).over U) ⥤
      ringedSiteModules.{w} (moduleRings X) :=
  SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := moduleRings X) U)

/-- Open restriction and direct image preserve module sheaves and have the stated
sectionwise scalar and restriction identities. `HEq` expresses literal equality after
identifying equal opens (and hence their section rings); it does not choose an isomorphism.
Source: Stacks Project, Tags 00A0(1),(2),(4),(5), 00A1(1)-(4), 008S and 008W
(blueprint: lem-weil-pbc-open-module-section-functors).

Proof:
1. A cover of a subopen of `U` and its intersections are the same in `X`. Thus the
   restricted commutative ring presheaf is a sheaf, namely `X.sheaf.over U`.
2. Retaining the original modules and restrictions gives restriction on presheaves:
   identities, composition and semilinearity are inherited from the input presheaf
   (`def-weil-presheaf-modules-sheafification`).
3. For direct image, restrict scalars along `O(V) → O(U ∩ V)`. Ring-homomorphism
   laws imply the module axioms; composition of ring restrictions and semilinearity
   of the input give the displayed semilinearity identity (Tag 008S).
4. Evaluate morphisms on subopens or intersected opens. Their original linearity,
   naturality, identities and compositions give the two presheaf functors.
5. The matching-family equalizer for a restricted presheaf is the original equalizer
   for the same cover; this includes the empty cover of the empty open.
6. Intersecting a cover of `V` with `U` covers `U ∩ V`, with the same intersections.
   The input sheaf equalizer therefore proves that direct image is a sheaf (Tag 008W).
   These are the equalizers of `def-weil-pbc-sites-and-cohomology`.
7. The sectionwise linear morphisms restrict the functors to the module-sheaf categories
   (`def-weil-sheaf-of-modules-category`). If `W ≤ U`, then `U ∩ W = W`, so both
   scalar restriction and module restriction retain the original data on `W`.
   Finally `U ∩ (U ∩ V) = U ∩ V`, so the last restriction is the identity.
-/
theorem open_module_section_functors (X : RingedSpace.{u}) (U : Opens X) :
    (∀ (P : PresheafOfModules.{w} (moduleRings X).obj),
      Presheaf.IsSheaf (Opens.grothendieckTopology X) P.presheaf →
        Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
          ((modulePresheafOpenRestriction X U).obj P).presheaf) ∧
    (∀ (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj),
      Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U) Q.presheaf →
        Presheaf.IsSheaf (Opens.grothendieckTopology X)
          ((modulePresheafOpenDirectImage X U).obj Q).presheaf) ∧
    (moduleSheafOpenRestriction.{u, w} X U ⋙ SheafOfModules.forget _ =
      SheafOfModules.forget _ ⋙ modulePresheafOpenRestriction X U) ∧
    (moduleSheafOpenDirectImage.{u, w} X U ⋙ SheafOfModules.forget _ =
      SheafOfModules.forget _ ⋙ modulePresheafOpenDirectImage X U) ∧
    (∀ (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
      (V : Opens X) (a : (moduleRings X).obj.obj (op V))
      (t : Q.obj (op ((Over.star U).obj V))),
      @SMul.smul ((moduleRings X).obj.obj (op V))
        (((modulePresheafOpenDirectImage X U).obj Q).obj (op V))
        inferInstance a t =
        (moduleRings X).obj.map (prod.snd : U ⨯ V ⟶ V).op a • t) ∧
    (∀ (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
      (V V' : Opens X) (i : V' ⟶ V) (a : (moduleRings X).obj.obj (op V))
      (t : Q.obj (op ((Over.star U).obj V))),
      Q.map ((Over.star U).map i).op
          ((moduleRings X).obj.map (prod.snd : U ⨯ V ⟶ V).op a • t) =
        (moduleRings X).obj.map (prod.snd : U ⨯ V' ⟶ V').op
          ((moduleRings X).obj.map i.op a) • Q.map ((Over.star U).map i).op t) ∧
    (∀ (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj) (W : Over U),
      HEq (((modulePresheafOpenDirectImage X U).obj Q).obj (op W.left))
        (Q.obj (op W))) ∧
    (∀ (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
      (W W' : Over U) (i : W' ⟶ W),
      HEq ((((modulePresheafOpenDirectImage X U).obj Q).presheaf.map i.left.op))
        (Q.presheaf.map i.op)) ∧
    (∀ (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj) (V : Opens X),
      HEq (((modulePresheafOpenDirectImage X U).obj Q).presheaf.map
        (prod.snd : U ⨯ V ⟶ V).op)
        (𝟙 (Q.presheaf.obj (op ((Over.star U).obj V))))) := by
  have star_eq (W : Over U) : (Over.star U).obj W.left = W :=
    CostructuredArrow.obj_ext _ _
      (le_antisymm (leOfHom (prod.snd : U ⨯ W.left ⟶ W.left))
        (leOfHom (prod.lift W.hom (𝟙 W.left)))) (Subsingleton.elim _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact ((moduleSheafOpenRestriction X U).obj ⟨P, hP⟩).isSheaf
  · intro Q hQ
    exact ((moduleSheafOpenDirectImage X U).obj ⟨Q, hQ⟩).isSheaf
  · rfl
  · rfl
  · intro Q V a t
    rfl
  · intro Q V V' i a t
    exact ((modulePresheafOpenDirectImage X U).obj Q).map_smul i.op a t
  · intro Q W
    have hobj (A B : Over U) (f : A.left ⟶ B.left) (e : A = B) :
        HEq ((ModuleCat.restrictScalars ((moduleRings X).obj.map f.op).hom).obj
          (Q.obj (op A))) (Q.obj (op B)) := by
      subst A
      have hf : f = 𝟙 B.left := Subsingleton.elim _ _
      subst f
      simp only [op_id]
      have hr : ((moduleRings X).obj.map (𝟙 (op B.left))).hom = RingHom.id _ :=
        congrArg RingCat.Hom.hom ((moduleRings X).obj.map_id (op B.left))
      rw [hr]
      rfl
    exact hobj _ W prod.snd (star_eq W)
  · intro Q W W' i
    change HEq (Q.presheaf.map ((Over.star U).map i.left).op) (Q.presheaf.map i.op)
    have hmap (A B A' B' : Over U) (f : A ⟶ B) (g : A' ⟶ B')
        (hA : A = A') (hB : B = B') :
        HEq (Q.presheaf.map f.op) (Q.presheaf.map g.op) := by
      subst A'
      subst B'
      have hf : f = g := Over.OverMorphism.ext (Subsingleton.elim _ _)
      subst g
      rfl
    exact hmap _ _ W' W _ i (star_eq W') (star_eq W)
  · intro Q V
    change HEq (Q.presheaf.map ((Over.star U).map
      (prod.snd : U ⨯ V ⟶ V)).op) (𝟙 _)
    have hmap (A B : Over U) (f : A ⟶ B) (e : A = B) :
        HEq (Q.presheaf.map f.op) (𝟙 (Q.presheaf.obj (op B))) := by
      subst A
      have hf : f = 𝟙 B := Over.OverMorphism.ext (Subsingleton.elim _ _)
      subst f
      simp
    exact hmap _ _ _ (star_eq ((Over.star U).obj V))

end TopologicalSpace.Opens
