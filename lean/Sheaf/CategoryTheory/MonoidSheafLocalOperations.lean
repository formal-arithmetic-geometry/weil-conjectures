/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Sites.Over

import Sheaf.CategoryTheory.OverSheafMapGluing
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-! # Local operations on a sheaf of sets

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory

/-- Multiplication and identity transported through compatible local trivializations
extend to natural operations on the original section sets.

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps; steps 1--3 of
lem-trf-monoid-sheaf-structure-gluing
(blueprint: lem-trf-monoid-sheaf-local-operations).

Proof: form the sectionwise product presheaf F × F and the singleton presheaf.
They are sheaves, since limits of set sheaves are computed sectionwise. On each
slice transport multiplication and identity through e and its inverse. These
are natural transformations. The overlap equation for e, and preservation of
multiplication and identity by phi, show equality of the transported operations
on double overlaps, including repeated indices. Apply map gluing (04TQ) to
each of the two natural transformations. Its restriction equations give the
local clauses below, and naturality gives the restriction clauses. This does
not assert any global algebraic laws, uniqueness of monoid structures, or the
existence of a structural map. On an empty cover the target sheaf has singleton
section sets, so both operations still exist uniquely. -/
theorem monoidSheafLocalOperations
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {I : Type (max u v w)}
    (U : C) (X : I → C) (f : ∀ a, X a ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U)
    (A : ∀ a, Sheaf (J.over (X a)) CommMonCat.{max u v w})
    (phi : ∀ a b,
      (J.overMapPullback CommMonCat (pullback.fst (f a) (f b))).obj (A a) ≅
        (J.overMapPullback CommMonCat (pullback.snd (f a) (f b))).obj (A b))
    (F : Sheaf (J.over U) (Type (max u v w)))
    (e : ∀ a, (Over.map (f a)).op ⋙ F.obj ≅ (A a).obj ⋙ forget CommMonCat)
    (he : ∀ (a b : I) (V : Over (pullback (f a) (f b)))
      (x : F.obj.obj (op ((Over.map (pullback.snd (f a) (f b)) ⋙
        Over.map (f b)).obj V))),
      (e b).hom.app _ x = (phi a b).hom.hom.app (op V)
        ((e a).hom.app _
          (F.obj.map (((Over.mapComp _ _).symm ≪≫
          Over.mapCongr _ _ (pullback.condition (f := f a) (g := f b)) ≪≫
          Over.mapComp _ _).hom.app V).op x))) :
    ∃ (mul : ∀ V : (Over U)ᵒᵖ, F.obj.obj V → F.obj.obj V → F.obj.obj V)
      (one : ∀ V : (Over U)ᵒᵖ, F.obj.obj V),
      ((∀ (V W : (Over U)ᵒᵖ) (k : V ⟶ W) (x y : F.obj.obj V),
          F.obj.map k (mul V x y) = mul W (F.obj.map k x) (F.obj.map k y)) ∧
        (∀ (V W : (Over U)ᵒᵖ) (k : V ⟶ W), F.obj.map k (one V) = one W)) ∧
      ((∀ (a : I) (V : (Over (X a))ᵒᵖ)
          (x y : F.obj.obj ((Over.map (f a)).op.obj V)),
          (e a).hom.app V (mul _ x y) = (e a).hom.app V x * (e a).hom.app V y) ∧
        (∀ (a : I) (V : (Over (X a))ᵒᵖ), (e a).hom.app V (one _) = 1)) := by
  classical
  let P : Sheaf (J.over U) (Type (max u v w)) :=
    ⟨F.obj ⊗ F.obj, Sheaf.tensorProd_isSheaf (J.over U) F F⟩
  let T : Sheaf (J.over U) (Type (max u v w)) :=
    ⟨𝟙_ _, Sheaf.tensorUnit_isSheaf (J.over U)⟩
  have en (a : I) {V W : (Over (X a))ᵒᵖ} (k : V ⟶ W)
      (x : F.obj.obj ((Over.map (f a)).op.obj V)) :
      (e a).hom.app W (F.obj.map ((Over.map (f a)).op.map k) x) =
        (A a).obj.map k ((e a).hom.app V x) := by
    exact ConcreteCategory.congr_hom ((e a).hom.naturality k) x
  have eni (a : I) {V W : (Over (X a))ᵒᵖ} (k : V ⟶ W)
      (x : (A a).obj.obj V) :
      F.obj.map ((Over.map (f a)).op.map k) ((e a).inv.app V x) =
        (e a).inv.app W ((A a).obj.map k x) := by
    exact (ConcreteCategory.congr_hom ((e a).inv.naturality k) x).symm
  let m (a : I) : (Over.map (f a)).op ⋙ P.obj ⟶
      (Over.map (f a)).op ⋙ F.obj :=
    { app := fun V ↦ ↾fun x ↦ (e a).inv.app V
        ((e a).hom.app V x.1 * (e a).hom.app V x.2)
      naturality := by
        intro V W k
        ext x
        change (e a).inv.app W
          ((e a).hom.app W (F.obj.map _ x.1) *
            (e a).hom.app W (F.obj.map _ x.2)) =
          F.obj.map _ ((e a).inv.app V
            ((e a).hom.app V x.1 * (e a).hom.app V x.2))
        rw [eni, map_mul ((A a).obj.map k).hom, en, en] }
  let j (a : I) : (Over.map (f a)).op ⋙ T.obj ⟶
      (Over.map (f a)).op ⋙ F.obj :=
    { app := fun V ↦ ↾fun _ ↦ (e a).inv.app V 1
      naturality := by
        intro V W k
        ext x
        change (e a).inv.app W 1 = F.obj.map _ ((e a).inv.app V 1)
        rw [eni, map_one ((A a).obj.map k).hom] }
  have ei (a : I) (V : (Over (X a))ᵒᵖ) :
      Function.Injective ((e a).hom.app V) := ((e a).app V).toEquiv.injective
  have phi_inj (a b : I) (V : Over (pullback (f a) (f b))) :
      Function.Injective ((phi a b).hom.hom.app (op V)) :=
    ((forget CommMonCat).mapIso
      (((sheafToPresheaf _ _).mapIso (phi a b)).app (op V))).toEquiv.injective
  obtain ⟨mg, hmg, _⟩ := overSheafMapGluing J U X f hcov P F m (by
    intro a b V x
    change F.obj.obj _ × F.obj.obj _ at x
    change F.obj.map _ ((e b).inv.app _
      ((e b).hom.app _ x.1 * (e b).hom.app _ x.2)) =
        (e a).inv.app _ ((e a).hom.app _ (F.obj.map _ x.1) *
          (e a).hom.app _ (F.obj.map _ x.2))
    apply ei a _
    apply phi_inj a b V
    erw [← he, Iso.inv_hom_id_app_apply, Iso.inv_hom_id_app_apply,
      map_mul ((phi a b).hom.hom.app (op V)).hom, ← he, ← he])
  obtain ⟨jg, hjg, _⟩ := overSheafMapGluing J U X f hcov T F j (by
    intro a b V x
    change F.obj.map _ ((e b).inv.app _ 1) = (e a).inv.app _ 1
    apply ei a _
    apply phi_inj a b V
    erw [← he, Iso.inv_hom_id_app_apply, Iso.inv_hom_id_app_apply,
      map_one ((phi a b).hom.hom.app (op V)).hom])
  change F.obj ⊗ F.obj ⟶ F.obj at mg
  change 𝟙_ _ ⟶ F.obj at jg
  have hmg' (a : I) (V : (Over (X a))ᵒᵖ)
      (x y : F.obj.obj ((Over.map (f a)).op.obj V)) :
      mg.app _ (x, y) = (e a).inv.app V
        ((e a).hom.app V x * (e a).hom.app V y) := hmg a V (x, y)
  have hjg' (a : I) (V : (Over (X a))ᵒᵖ) :
      jg.app ((Over.map (f a)).op.obj V) PUnit.unit = (e a).inv.app V 1 :=
    hjg a V PUnit.unit
  refine ⟨fun V x y ↦ mg.app V (x, y), fun V ↦ jg.app V PUnit.unit,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro V W k x y
    have hn := ConcreteCategory.congr_hom (C := Type (max u v w))
      (mg.naturality k) ((x, y) : F.obj.obj V × F.obj.obj V)
    exact hn.symm
  · intro V W k
    exact (ConcreteCategory.congr_hom (jg.naturality k) PUnit.unit).symm
  · intro a V x y
    change (e a).hom.app V (mg.app _ (x, y)) = _
    rw [hmg']
    exact Iso.inv_hom_id_app_apply (e a) V _
  · intro a V
    change (e a).hom.app V (jg.app _ PUnit.unit) = 1
    rw [hjg']
    exact Iso.inv_hom_id_app_apply (e a) V _

end CategoryTheory
