/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Module
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! # Linear open transposes for module presheaves

Source: Stacks Project, Sheaves, Tags 008U and 00A0
(blueprint: lem-weil-pbc-open-module-transpose-morphisms).

The site `Over U` consists of opens contained in `U`. Its equivalence with opens of
the subspace is `U.overEquivalence`. The two functors below are specializations of
Mathlib's presheaf functors, with no new module-presheaf structure.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace TopologicalSpace.Opens

/-- Restriction retains sections and actions on opens contained in `U`.
Source: Stacks, Tag 00A0 (1)
(blueprint: lem-weil-pbc-open-module-transpose-morphisms). -/
abbrev openPresheafModuleRestriction (X : RingedSpace.{u}) (U : Opens X) :=
  PresheafOfModules.pushforward₀.{w} (Over.forget U) (moduleRings X).obj

/-- Direct image evaluates on the intersection with `U`, with scalar action through
ring restriction. Source: Stacks, Tags 008U and 00A0
(blueprint: lem-weil-pbc-open-module-transpose-morphisms). -/
noncomputable abbrev openPresheafModuleDirectImage (X : RingedSpace.{u}) (U : Opens X) :=
  PresheafOfModules.pushforward.{w} (SheafOfModules.pushforwardOver (R := moduleRings X) U).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The displayed forward and reverse section maps are linear module-presheaf morphisms,
and the forward maps commute with precomposition and postcomposition, with their stated
common component. Both functors preserve module sheaves.

Source: Stacks, Tag 008U, specialized to the section model of Tag 00A0
(blueprint: lem-weil-pbc-open-module-transpose-morphisms).

Proof (the node's six steps):
1. Put `A = V ∩ U`. Restriction in `P` is additive and semilinear over ring restriction;
   `α_A` is linear. Their composite is additive and linear for the restricted scalar
   action on `D Q(V)`, including preservation of zero
   (`def-weil-presheaf-modules-sheafification`).
2. Naturality of `α` and composition of restrictions identify both restrictions of this
   composite to `V' ∩ U`, giving a module-presheaf morphism.
3. On an open `W` contained in `U`, the canonical identification `W ∩ U = W` identifies
   the scalar restriction with the identity. Thus `β_W` gives a linear map to `Q(W)`;
   naturality of `β` gives the reverse morphism. In the `Over U` encoding this
   identification is restriction along the unit of `Over.forgetAdjStar U`.
4. Restricting `μ` and evaluating `ν` on intersections gives linear natural maps.
   Expanding the forward composite gives `ν_A (α_A (μ_A (s|_A)))`.
5. Naturality of `μ` rewrites `μ_V(s)|_A` as `μ_A(s|_A)`. This proves equality of
   the two morphisms and the displayed common-component formula.
6. The notion of morphism for module sheaves is the same underlying linear natural
   map (`def-weil-sheaf-of-modules-category`). A cover of an open inside `U` is the
   same cover in `X`, so restriction preserves gluing. Intersecting a cover with `U`
   gives a cover of the intersection, so direct image also preserves gluing.
-/
theorem exists_openModuleTransposeMorphisms (X : RingedSpace.{u}) (U : Opens X) :
    ∃ (Φ : ∀ (P : PresheafOfModules.{w} (moduleRings X).obj)
        (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj),
        ((openPresheafModuleRestriction X U).obj P ⟶ Q) →
          (P ⟶ (openPresheafModuleDirectImage X U).obj Q))
      (Ψ : ∀ (P : PresheafOfModules.{w} (moduleRings X).obj)
        (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj),
        (P ⟶ (openPresheafModuleDirectImage X U).obj Q) →
          ((openPresheafModuleRestriction X U).obj P ⟶ Q)),
      (∀ (P : PresheafOfModules.{w} (moduleRings X).obj)
        (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
        (α : (openPresheafModuleRestriction X U).obj P ⟶ Q)
        (V : Opens X) (s : P.obj (op V)),
        (Φ P Q α).app (op V) s =
          α.app (op ((Over.star U).obj V)) (P.map (prod.snd : U ⨯ V ⟶ V).op s)) ∧
      (∀ (P : PresheafOfModules.{w} (moduleRings X).obj)
        (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
        (β : P ⟶ (openPresheafModuleDirectImage X U).obj Q)
        (W : Over U) (s : P.obj (op W.left)),
        (Ψ P Q β).app (op W) s =
          Q.map ((Over.forgetAdjStar U).unit.app W).op (β.app (op W.left) s)) ∧
      (∀ (P' P : PresheafOfModules.{w} (moduleRings X).obj)
        (Q Q' : PresheafOfModules.{w} ((moduleRings X).over U).obj)
        (μ : P' ⟶ P) (ν : Q ⟶ Q')
        (α : (openPresheafModuleRestriction X U).obj P ⟶ Q),
        Φ P' Q' ((openPresheafModuleRestriction X U).map μ ≫ α ≫ ν) =
          μ ≫ Φ P Q α ≫ (openPresheafModuleDirectImage X U).map ν) ∧
      (∀ (P' P : PresheafOfModules.{w} (moduleRings X).obj)
        (Q Q' : PresheafOfModules.{w} ((moduleRings X).over U).obj)
        (μ : P' ⟶ P) (ν : Q ⟶ Q')
        (α : (openPresheafModuleRestriction X U).obj P ⟶ Q)
        (V : Opens X) (s : P'.obj (op V)),
        (Φ P' Q' ((openPresheafModuleRestriction X U).map μ ≫ α ≫ ν)).app (op V) s =
          ν.app (op ((Over.star U).obj V))
            (α.app (op ((Over.star U).obj V))
              (μ.app (op ((Over.star U).obj V).left)
                (P'.map (prod.snd : U ⨯ V ⟶ V).op s)))) ∧
      (∀ (M : CategoryTheory.ringedSiteModules.{w} (moduleRings X)),
        Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
          ((openPresheafModuleRestriction X U).obj M.val).presheaf) ∧
      (∀ (N : CategoryTheory.ringedSiteModules.{w} ((moduleRings X).over U)),
        Presheaf.IsSheaf (Opens.grothendieckTopology X)
          ((openPresheafModuleDirectImage X U).obj N.val).presheaf) := by
  let Φ := fun (P : PresheafOfModules.{w} (moduleRings X).obj)
      (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
      (α : (openPresheafModuleRestriction X U).obj P ⟶ Q) ↦
    (show P ⟶ (openPresheafModuleDirectImage X U).obj Q from
      { app := fun V ↦ ModuleCat.ofHom
          (X := P.obj V) (Y := ((openPresheafModuleDirectImage X U).obj Q).obj V)
          { toFun := fun s ↦ α.app (op ((Over.star U).obj V.unop))
              (P.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s)
            map_add' := by
              intro s t
              rw [map_add]
              exact map_add (α.app _).hom _ _
            map_smul' := by
              intro a s
              rw [P.map_smul]
              exact (α.app _).hom.map_smul _ _ }
        naturality := fun {V V'} f ↦ by
          ext s
          change α.app (op ((Over.star U).obj V'.unop))
            (P.map (prod.snd : U ⨯ V'.unop ⟶ V'.unop).op (P.map f s)) =
              Q.map ((Over.star U).map f.unop).op
                (α.app (op ((Over.star U).obj V.unop))
                  (P.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s))
          erw [← PresheafOfModules.naturality_apply α]
          change α.app (op ((Over.star U).obj V'.unop))
            (P.map (prod.snd : U ⨯ V'.unop ⟶ V'.unop).op (P.map f s)) =
              α.app _ (P.map ((Over.forget U).map ((Over.star U).map f.unop)).op
                (P.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s))
          congr 1
          erw [← P.map_comp_apply, ← P.map_comp_apply]
          apply P.congr_map_apply
          apply Subsingleton.elim })
  let Ψ := fun (P : PresheafOfModules.{w} (moduleRings X).obj)
      (Q : PresheafOfModules.{w} ((moduleRings X).over U).obj)
      (β : P ⟶ (openPresheafModuleDirectImage X U).obj Q) ↦
    (show (openPresheafModuleRestriction X U).obj P ⟶ Q from
      { app := fun W ↦ ModuleCat.ofHom
          (X := ((openPresheafModuleRestriction X U).obj P).obj W) (Y := Q.obj W)
          { toFun := fun s ↦ Q.map ((Over.forgetAdjStar U).unit.app W.unop).op
              (β.app (op W.unop.left) s)
            map_add' := by
              intro s t
              rw [map_add]
              exact map_add (Q.map _).hom _ _
            map_smul' := by
              intro a s
              rw [map_smul]
              change Q.map _ ((moduleRings X).obj.map
                (prod.snd : U ⨯ W.unop.left ⟶ W.unop.left).op a • _) = _
              rw [Q.map_smul]
              congr 1
              change (moduleRings X).obj.map _ ((moduleRings X).obj.map _ a) = a
              rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
              have h : (prod.snd : U ⨯ W.unop.left ⟶ W.unop.left).op ≫
                  ((Over.forget U).map ((Over.forgetAdjStar U).unit.app W.unop)).op =
                    𝟙 (op W.unop.left) := Subsingleton.elim _ _
              change (moduleRings X).obj.map
                ((prod.snd : U ⨯ W.unop.left ⟶ W.unop.left).op ≫
                  ((Over.forget U).map ((Over.forgetAdjStar U).unit.app W.unop)).op) a = a
              rw [h]
              exact ConcreteCategory.congr_hom ((moduleRings X).obj.map_id _) a }
        naturality := fun {W W'} f ↦ by
          ext s
          change Q.map ((Over.forgetAdjStar U).unit.app W'.unop).op
            (β.app (op W'.unop.left) (P.map ((Over.forget U).map f.unop).op s)) =
              Q.map f (Q.map ((Over.forgetAdjStar U).unit.app W.unop).op
                (β.app (op W.unop.left) s))
          erw [PresheafOfModules.naturality_apply β]
          change Q.map ((Over.forgetAdjStar U).unit.app W'.unop).op
            (Q.map ((Over.star U).map ((Over.forget U).map f.unop)).op
              (β.app (op W.unop.left) s)) =
                Q.map f (Q.map ((Over.forgetAdjStar U).unit.app W.unop).op
                  (β.app (op W.unop.left) s))
          erw [← Q.map_comp_apply, ← Q.map_comp_apply]
          apply Q.congr_map_apply
          apply Quiver.Hom.unop_inj
          simpa only [unop_comp, Quiver.Hom.unop_op, Functor.comp_map, Functor.id_map] using
            ((Over.forgetAdjStar U).unit.naturality f.unop).symm })
  refine ⟨Φ, Ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    rfl
  · intros
    rfl
  · intro P' P Q Q' μ ν α
    ext V s
    change ν.app (op ((Over.star U).obj V.unop))
      (α.app _ (μ.app (op (U ⨯ V.unop))
        (P'.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s))) =
          ν.app (op ((Over.star U).obj V.unop))
            (α.app (op ((Over.star U).obj V.unop))
              (P.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op (μ.app V s)))
    erw [PresheafOfModules.naturality_apply μ]
  · intros
    rfl
  · intro M
    exact (M.over U).isSheaf
  · intro N
    exact ((SheafOfModules.pushforward
      (SheafOfModules.pushforwardOver (R := moduleRings X) U)).obj N).isSheaf

end TopologicalSpace.Opens
