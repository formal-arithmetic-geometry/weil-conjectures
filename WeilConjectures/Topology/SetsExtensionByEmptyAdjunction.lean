/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.SetsExtensionByEmpty
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# Extension by the empty set: adjunction and stalks

Source: `literature/stacks-project/sheaves.tex`, Lemmas 00A0 and 00A3
(blueprint: `lem-weil-pbc-sets-extension-by-empty-adjunction`).

## Main results

* `TopCat.extensionByEmptyAdjunction`: `j_{U!}` is left adjoint to the restriction
  `j_U^{-1}` (Mathlib's `Sheaf.pullback` along the open inclusion). Morphisms `j_{U!} G ⟶ F`
  correspond to morphisms of presheaves `j_{U,p!} G ⟶ F`, i.e. to `G ⟶ F|_U`.
* `TopCat.extensionByEmpty_adjunction_stalks`: the adjunction, the stalks of `j_{U!} G`, and
  `G ≅ j_U^{-1} j_{U!} G`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

noncomputable section

variable {X : TopCat.{u}} (U : Opens X)


/-- Transporting a morphism in both objects is conjugation by equality morphisms. -/
private theorem cast_hom' {A B A' B' : Type u} (hA : A = A') (hB : B = B')
    (h : (A' ⟶ B') = (A ⟶ B)) (f : A ⟶ B) :
    h.mpr f = eqToHom hA.symm ≫ f ≫ eqToHom hB := by
  subst A'
  subst B'
  simp

/-- On an open `V ⊆ U`, the sections of `j_{U,p!} G` are `G(V)`. -/
theorem extensionByEmptyPresheaf_obj_of_le (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    {V : Opens X} (hV : V ≤ U) :
    ((extensionByEmptyPresheaf U).obj G).obj (op V) =
      G.presheaf.obj (op ((Opens.map U.inclusion').obj V)) := by
  simp [extensionByEmptyPresheaf, extensionByEmptyPresheafObj, hV]

/-- On an open `V ⊄ U`, the presheaf `j_{U,p!} G` has no sections. -/
theorem isEmpty_extensionByEmptyPresheaf_obj (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    {V : Opens X} (hV : ¬ V ≤ U) :
    IsEmpty (((extensionByEmptyPresheaf U).obj G).obj (op V)) := by
  simp only [extensionByEmptyPresheaf, extensionByEmptyPresheafObj, if_neg hV]
  infer_instance

/-- On opens inside `U`, the restriction maps of `j_{U,p!} G` are those of `G`. -/
theorem extensionByEmptyPresheaf_map_of_le (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    {V W : Opens X} (i : W ⟶ V) (hV : V ≤ U) :
    ((extensionByEmptyPresheaf U).obj G).map i.op =
      eqToHom (extensionByEmptyPresheaf_obj_of_le U G hV) ≫
        G.presheaf.map ((Opens.map U.inclusion').map i).op ≫
          eqToHom (extensionByEmptyPresheaf_obj_of_le U G (i.le.trans hV)).symm := by
  simp only [extensionByEmptyPresheaf, extensionByEmptyPresheafObj, extensionByEmptyMap,
    unop_op, dif_pos hV]
  rw [cast_hom' (if_pos hV).symm (if_pos (i.le.trans hV)).symm]
  rfl

/-- On opens inside `U`, the components of `j_{U,p!} α` are those of `α`. -/
theorem extensionByEmptyPresheaf_map_app_of_le
    {G G' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)} (α : G ⟶ G')
    {V : Opens X} (hV : V ≤ U) :
    ((extensionByEmptyPresheaf U).map α).app (op V) =
      eqToHom (extensionByEmptyPresheaf_obj_of_le U G hV) ≫
        α.hom.app (op ((Opens.map U.inclusion').obj V)) ≫
          eqToHom (extensionByEmptyPresheaf_obj_of_le U G' hV).symm := by
  simp only [extensionByEmptyPresheaf, extensionByEmptyPresheafHom, extensionByEmptyPresheafApp,
    unop_op, dif_pos hV]
  exact cast_hom' (if_pos hV).symm (if_pos hV).symm _ _

/-- The image of an open of `U` under the inclusion is contained in `U`. -/
theorem isOpenEmbedding_functor_obj_le (W : Opens ((toTopCat X).obj U)) :
    U.isOpenEmbedding.functor.obj W ≤ U := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

set_option backward.isDefEq.respectTransparency false in
/-- Restricting `j_{U,p!} G` back to `U` recovers `G`, naturally in `G`. -/
def extensionByEmptyPresheafRestrictIso :
    extensionByEmptyPresheaf U ⋙
        (Functor.whiskeringLeft _ _ (Type u)).obj U.isOpenEmbedding.functor.op ≅
      Sheaf.forget (Type u) _ :=
  NatIso.ofComponents (fun G ↦ NatIso.ofComponents (fun W ↦ eqToIso
    ((extensionByEmptyPresheaf_obj_of_le U G (isOpenEmbedding_functor_obj_le U W.unop)).trans
      (congrArg (fun V ↦ G.presheaf.obj (op V)) (map_functor_eq W.unop)))) (fun {W W'} f ↦ by
        have h : (Opens.map U.inclusion').map (U.isOpenEmbedding.functor.map f.unop) =
            eqToHom (map_functor_eq _) ≫ f.unop ≫ eqToHom (map_functor_eq _).symm :=
          Subsingleton.elim _ _
        dsimp
        rw [← f.op_unop, extensionByEmptyPresheaf_map_of_le U G _
          (isOpenEmbedding_functor_obj_le U W.unop), Quiver.Hom.unop_op, h]
        simp [eqToHom_map]
        rfl))
    (fun {G G'} α ↦ by
      ext W : 2
      dsimp
      rw [extensionByEmptyPresheaf_map_app_of_le U α (isOpenEmbedding_functor_obj_le U W.unop)]
      simp only [Category.assoc, eqToHom_trans]
      rw [eqToHom_naturality (fun V : Opens _ ↦ α.hom.app (op V)) (map_functor_eq W.unop)]
      simp
      rfl)

/-- A presheaf maps an inclusion between equal opens to an equality morphism. -/
private theorem presheaf_map_eq_eqToHom {Y : TopCat.{u}} {C : Type*} [Category C]
    (P : Y.Presheaf C) {A B : Opens Y} (i : A ⟶ B) (h : A = B) :
    P.map i.op = eqToHom (by rw [h]) := by
  subst h
  rw [Subsingleton.elim i (𝟙 _)]
  simp

/-- An open contained in `U` is contained in the image of its preimage in `U`. -/
theorem le_functor_map_obj_of_le {V : Opens X} (hV : V ≤ U) :
    V ≤ U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) := by
  rw [functor_map_eq_inf]
  exact le_inf le_rfl hV

/-- The components of the presheaf morphism `j_{U,p!} G ⟶ P` corresponding to a morphism
`G ⟶ P|_U`: on opens inside `U` they are the components of `β`, elsewhere the empty map. -/
def extensionByEmptyPresheafDescApp {G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)}
    {P : Presheaf (Type u) X} (β : G.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ P)
    (V : (Opens X)ᵒᵖ) : ((extensionByEmptyPresheaf U).obj G).obj V ⟶ P.obj V :=
  @dite _ (V.unop ≤ U) (Classical.propDecidable _)
    (fun h ↦ eqToHom (extensionByEmptyPresheaf_obj_of_le U G h) ≫
      β.app (op ((Opens.map U.inclusion').obj V.unop)) ≫
        P.map (homOfLE (le_functor_map_obj_of_le U h)).op)
    (fun h ↦ TypeCat.ofHom fun x ↦ (isEmpty_extensionByEmptyPresheaf_obj U G h).elim x)

/-- On opens inside `U`, `extensionByEmptyPresheafDescApp` is given by `β`. -/
theorem extensionByEmptyPresheafDescApp_of_le {G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)}
    {P : Presheaf (Type u) X} (β : G.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ P)
    {V : Opens X} (h : V ≤ U) :
    extensionByEmptyPresheafDescApp U β (op V) =
      eqToHom (extensionByEmptyPresheaf_obj_of_le U G h) ≫
        β.app (op ((Opens.map U.inclusion').obj V)) ≫
          P.map (homOfLE (le_functor_map_obj_of_le U h)).op :=
  dif_pos h

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf morphism `j_{U,p!} G ⟶ P` corresponding to a morphism `G ⟶ P|_U`. -/
def extensionByEmptyPresheafDesc {G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)}
    {P : Presheaf (Type u) X} (β : G.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ P) :
    (extensionByEmptyPresheaf U).obj G ⟶ P where
  app := extensionByEmptyPresheafDescApp U β
  naturality {V V'} i := by
    by_cases h : V.unop ≤ U
    · have h' : V'.unop ≤ U := i.unop.le.trans h
      rw [← i.op_unop, extensionByEmptyPresheafDescApp_of_le U β h,
        extensionByEmptyPresheafDescApp_of_le U β h',
        extensionByEmptyPresheaf_map_of_le U G _ h]
      have := β.naturality ((Opens.map U.inclusion').map i.unop).op
      dsimp at this
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% this, ← P.map_comp, ← P.map_comp]
      rfl
    · have := isEmpty_extensionByEmptyPresheaf_obj U G h
      ext x
      exact isEmptyElim x

/-- A component of a natural transformation at an object equal to `Y` is the component at `Y`
conjugated by equality morphisms. -/
private theorem app_eq_eqToHom_comp {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G)
    {A B : C} (h : A = B) :
    α.app A = eqToHom (congrArg F.obj h) ≫ α.app B ≫ eqToHom (congrArg G.obj h).symm := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms `j_{U,p!} G ⟶ P` of presheaves on `X` correspond to morphisms `G ⟶ P|_U`. -/
def extensionByEmptyPresheafHomEquiv (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    (P : Presheaf (Type u) X) :
    ((extensionByEmptyPresheaf U).obj G ⟶ P) ≃
      (G.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ P) where
  toFun α := ((extensionByEmptyPresheafRestrictIso U).app G).inv ≫
    Functor.whiskerLeft U.isOpenEmbedding.functor.op α
  invFun β := extensionByEmptyPresheafDesc U β
  left_inv α := by
    ext V : 1
    by_cases h : V ≤ U
    · dsimp [extensionByEmptyPresheafDesc]
      rw [extensionByEmptyPresheafDescApp_of_le U _ h]
      have hφ : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) ≤ U :=
        isOpenEmbedding_functor_obj_le U _
      have := α.naturality (homOfLE (le_functor_map_obj_of_le U h)).op
      rw [extensionByEmptyPresheaf_map_of_le U G _ hφ,
        presheaf_map_eq_eqToHom _ _ (map_functor_eq _).symm] at this
      simp only [extensionByEmptyPresheafRestrictIso]
      dsimp
      simp only [Category.assoc]
      rw [← this]
      simp
    · have := isEmpty_extensionByEmptyPresheaf_obj U G h
      ext x
      exact isEmptyElim x
  right_inv β := by
    ext W : 1
    dsimp [extensionByEmptyPresheafDesc]
    rw [extensionByEmptyPresheafDescApp_of_le U _ (isOpenEmbedding_functor_obj_le U W),
      presheaf_map_eq_eqToHom _ _
        (congrArg U.isOpenEmbedding.functor.obj (map_functor_eq W)).symm,
      app_eq_eqToHom_comp β (congrArg op (map_functor_eq W))]
    simp [extensionByEmptyPresheafRestrictIso]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf hom equivalence is natural in the sheaf `G`. -/
theorem extensionByEmptyPresheafHomEquiv_naturality_left
    {G G' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)} (f : G ⟶ G')
    {P : Presheaf (Type u) X} (α : (extensionByEmptyPresheaf U).obj G' ⟶ P) :
    extensionByEmptyPresheafHomEquiv U G P ((extensionByEmptyPresheaf U).map f ≫ α) =
      f.hom ≫ extensionByEmptyPresheafHomEquiv U G' P α := by
  have := (extensionByEmptyPresheafRestrictIso U).inv.naturality f
  dsimp [extensionByEmptyPresheafHomEquiv]
  rw [Functor.whiskerLeft_comp]
  exact (reassoc_of% this) _ |>.symm

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf hom equivalence is natural in the presheaf `P`. -/
theorem extensionByEmptyPresheafHomEquiv_naturality_right
    (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    {P P' : Presheaf (Type u) X} (α : (extensionByEmptyPresheaf U).obj G ⟶ P) (g : P ⟶ P') :
    extensionByEmptyPresheafHomEquiv U G P' (α ≫ g) =
      extensionByEmptyPresheafHomEquiv U G P α ≫
        Functor.whiskerLeft U.isOpenEmbedding.functor.op g := by
  dsimp [extensionByEmptyPresheafHomEquiv]
  rw [Functor.whiskerLeft_comp]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms `j_{U!} G ⟶ F` correspond to morphisms from `G` to the restriction of `F`. -/
def extensionByEmptyHomEquiv (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    (F : X.Sheaf (Type u)) :
    ((extensionByEmpty U).obj G ⟶ F) ≃ (G ⟶ (U.isOpenEmbedding.sheafPullback (Type u)).obj F) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) (Type u)).homEquiv _ F).trans
    ((extensionByEmptyPresheafHomEquiv U G F.obj).trans
      (Sheaf.homEquiv (X := G) (Y := (U.isOpenEmbedding.sheafPullback (Type u)).obj F)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- `extensionByEmptyHomEquiv` is natural in the sheaf on `U`. -/
theorem extensionByEmptyHomEquiv_naturality_left
    {G G' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)} (f : G ⟶ G') {F : X.Sheaf (Type u)}
    (h : (extensionByEmpty U).obj G' ⟶ F) :
    extensionByEmptyHomEquiv U G F ((extensionByEmpty U).map f ≫ h) =
      f ≫ extensionByEmptyHomEquiv U G' F h := by
  apply CategoryTheory.Sheaf.hom_ext
  dsimp [extensionByEmptyHomEquiv, extensionByEmpty]
  erw [Adjunction.homEquiv_naturality_left, extensionByEmptyPresheafHomEquiv_naturality_left]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `extensionByEmptyHomEquiv` is natural in the sheaf on `X`. -/
theorem extensionByEmptyHomEquiv_naturality_right
    (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) {F F' : X.Sheaf (Type u)}
    (h : (extensionByEmpty U).obj G ⟶ F) (g : F ⟶ F') :
    extensionByEmptyHomEquiv U G F' (h ≫ g) =
      extensionByEmptyHomEquiv U G F h ≫ (U.isOpenEmbedding.sheafPullback (Type u)).map g := by
  apply CategoryTheory.Sheaf.hom_ext
  dsimp [extensionByEmptyHomEquiv]
  erw [Adjunction.homEquiv_naturality_right, extensionByEmptyPresheafHomEquiv_naturality_right]
  rfl

/-- The adjunction `j_{U!} ⊣ j_U^{-1}`, with the naive pullback along the open embedding. -/
def extensionByEmptyAdjunctionNaive :
    extensionByEmpty U ⊣ U.isOpenEmbedding.sheafPullback (Type u) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extensionByEmptyHomEquiv U
      homEquiv_naturality_left_symm {G' G F} f g := by
        apply (extensionByEmptyHomEquiv U G' F).injective
        rw [Equiv.apply_symm_apply, extensionByEmptyHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right {G F F'} f g :=
        extensionByEmptyHomEquiv_naturality_right U G f g }

/-- The adjunction `j_{U!} ⊣ j_U^{-1}` (Stacks, Lemma 00A3). -/
def extensionByEmptyAdjunction :
    extensionByEmpty U ⊣ Sheaf.pullback (Type u) (inclusion' U) :=
  (extensionByEmptyAdjunctionNaive U).ofNatIsoRight
    (U.isOpenEmbedding.sheafPullbackIso (Type u)).symm

/-- The stalks of `j_{U!} G` are those of the presheaf `j_{U,p!} G`. -/
def extensionByEmptyStalkIso (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) (x : X) :
    ((extensionByEmptyPresheaf U).obj G).stalk x ≅ ((extensionByEmpty U).obj G).presheaf.stalk x :=
  @asIso _ _ _ _ ((Presheaf.stalkFunctor (Type u) x).map
    (toSheafify (Opens.grothendieckTopology X) ((extensionByEmptyPresheaf U).obj G)))
    (Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) _)

/-- Restricting a presheaf along the open embedding of `U` does not change the stalks. -/
def restrictOpenStalkIso (P : Presheaf (Type u) X) (y : (toTopCat X).obj U) :
    Presheaf.stalk (X := (toTopCat X).obj U) (U.isOpenEmbedding.functor.op ⋙ P) y ≅
      P.stalk y.1 :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, P⟩ U.isOpenEmbedding y

/-- The stalks of `j_{U!} G` at points outside `U` are empty. -/
theorem isEmpty_extensionByEmpty_stalk (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) {x : X}
    (hx : x ∉ U) : IsEmpty (ToType (((extensionByEmpty U).obj G).presheaf.stalk x)) := by
  have : IsEmpty (((extensionByEmptyPresheaf U).obj G).stalk x) := by
    refine ⟨fun s ↦ ?_⟩
    obtain ⟨V, hxV, t, rfl⟩ :=
      Presheaf.exists_germ_eq ((extensionByEmptyPresheaf U).obj G) (x := x) s
    have := isEmpty_extensionByEmptyPresheaf_obj U G (fun h ↦ hx (h hxV))
    exact isEmptyElim t
  exact (extensionByEmptyStalkIso U G x).toEquiv.symm.isEmpty

/-- The stalks of `j_{U!} G` at points of `U` are those of `G`. -/
def extensionByEmptyStalkIsoOfMem (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) {x : X}
    (hx : x ∈ U) : G.presheaf.stalk ⟨x, hx⟩ ≅ ((extensionByEmpty U).obj G).presheaf.stalk x :=
  (Presheaf.stalkFunctor (Type u) _).mapIso ((extensionByEmptyPresheafRestrictIso U).app G).symm ≪≫
    restrictOpenStalkIso U _ ⟨x, hx⟩ ≪≫ extensionByEmptyStalkIso U G x

/-- `restrictOpenStalkIso` sends a germ to the germ on the image open. -/
theorem germ_restrictOpenStalkIso_hom (P : Presheaf (Type u) X) (V : Opens ((toTopCat X).obj U))
    (y : (toTopCat X).obj U) (hy : y ∈ V) :
    Presheaf.germ (X := (toTopCat X).obj U) (U.isOpenEmbedding.functor.op ⋙ P) V y hy ≫
        (restrictOpenStalkIso U P y).hom =
      P.germ (U.isOpenEmbedding.functor.obj V) y.1 ⟨y, hy, rfl⟩ :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ ⟨X, P⟩ U.isOpenEmbedding V y hy

set_option backward.isDefEq.respectTransparency false in
/-- The identification of stalks of a restriction is natural in the presheaf. -/
theorem restrictOpenStalkIso_hom_naturality {P Q : Presheaf (Type u) X} (t : P ⟶ Q)
    (y : (toTopCat X).obj U) :
    (Presheaf.stalkFunctor (Type u) y).map (Functor.whiskerLeft U.isOpenEmbedding.functor.op t) ≫
        (restrictOpenStalkIso U Q y).hom =
      (restrictOpenStalkIso U P y).hom ≫ (Presheaf.stalkFunctor (Type u) y.1).map t := by
  refine Presheaf.stalk_hom_ext _ fun V hy ↦ ?_
  rw [Presheaf.stalkFunctor_map_germ_assoc, germ_restrictOpenStalkIso_hom,
    reassoc_of% germ_restrictOpenStalkIso_hom, Presheaf.stalkFunctor_map_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit `G ⟶ j_U^{-1} j_{U!} G`, with the naive pullback. -/
def extensionByEmptyUnitNaive (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) :
    G ⟶ (U.isOpenEmbedding.sheafPullback (Type u)).obj ((extensionByEmpty U).obj G) :=
  (Sheaf.homEquiv (X := G)
    (Y := (U.isOpenEmbedding.sheafPullback (Type u)).obj ((extensionByEmpty U).obj G))).symm
    (((extensionByEmptyPresheafRestrictIso U).app G).inv ≫
      Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (toSheafify (Opens.grothendieckTopology X) ((extensionByEmptyPresheaf U).obj G)))

set_option backward.isDefEq.respectTransparency false in
/-- The naive unit `G ⟶ j_U^{-1} j_{U!} G` is an isomorphism, as it is so on stalks. -/
instance (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) :
    IsIso (extensionByEmptyUnitNaive U G) := by
  suffices ∀ y, IsIso ((Presheaf.stalkFunctor (Type u) y).map
      (extensionByEmptyUnitNaive U G).1) from Presheaf.isIso_of_stalkFunctor_map_iso _
  intro y
  have := Presheaf.stalkFunctor_map_unit_toSheafify_isIso y.1 (Type u)
    ((extensionByEmptyPresheaf U).obj G)
  have h := restrictOpenStalkIso_hom_naturality U
    (toSheafify (Opens.grothendieckTopology X) ((extensionByEmptyPresheaf U).obj G)) y
  rw [← Iso.eq_comp_inv] at h
  have e : (extensionByEmptyUnitNaive U G).1 = ((extensionByEmptyPresheafRestrictIso U).app G).inv ≫
      Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (toSheafify (Opens.grothendieckTopology X) ((extensionByEmptyPresheaf U).obj G)) := rfl
  rw [e, Functor.map_comp, h]
  infer_instance

/--
Source: Stacks Project, Lemma 00A3 (blueprint: lem-weil-pbc-sets-extension-by-empty-adjunction).
The proof composes the presheaf extension and restriction bijection with
sheafification, computes stalks from neighbourhood colimits, and applies the
stalk criterion for sheaf isomorphisms.
-/
theorem extensionByEmpty_adjunction_stalks
    (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) :
    Nonempty
        (extensionByEmpty U ⊣ Sheaf.pullback (Type u) (inclusion' U)) ∧
      (∀ (x : X), x ∉ U →
        IsEmpty (ToType (((extensionByEmpty U).obj G).presheaf.stalk x))) ∧
      (∀ (x : X) (hx : x ∈ U),
        Nonempty
          (G.presheaf.stalk ⟨x, hx⟩ ≃
            ToType (((extensionByEmpty U).obj G).presheaf.stalk x))) ∧
      Nonempty
        (G ≅ (Sheaf.pullback (Type u) (inclusion' U)).obj ((extensionByEmpty U).obj G)) := by
  exact ⟨⟨extensionByEmptyAdjunction U⟩, fun _ hx ↦ isEmpty_extensionByEmpty_stalk U G hx,
    fun _ hx ↦ ⟨(extensionByEmptyStalkIsoOfMem U G hx).toEquiv⟩,
    ⟨asIso (extensionByEmptyUnitNaive U G) ≪≫
      ((U.isOpenEmbedding.sheafPullbackIso (Type u)).app _).symm⟩⟩

end
end TopCat
