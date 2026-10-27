/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FppfSchemeDataSheafGluing
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Locally representable fppf sheaves and scheme descent data

Source: Stacks Project, Descent, Tag 02W5, including clauses (1) and (2)
(blueprint: lem-trf-fppf-sheaf-representability-descent-data).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u z v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem constraint_hom
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {T U W : C} (f : U ⟶ T) (a : W ⟶ U) (p : W ⟶ T)
    (h : a ≫ f = p)
    (H : Sheaf (J.over T) (Type z)) (V : Over W) :
    (((J.pseudofunctorOver (Type z)).mapComp'
      f.op.toLoc a.op.toLoc p.op.toLoc (by subst p; rfl)).hom.toNatTrans.app H).hom.app
        (op V) = H.obj.map (Over.homMk
          (U := (Over.map f).obj ((Over.map a).obj V))
          (V := (Over.map p).obj V) (𝟙 V.left) (by simp [Category.assoc, h])).op := by
  subst p
  change ((J.overMapPullbackComp (Type z) a f).inv.app H).hom.app (op V) = _
  rw [GrothendieckTopology.overMapPullbackComp_inv_app_hom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem constraint_inv
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {T U W : C} (f : U ⟶ T) (a : W ⟶ U) (p : W ⟶ T)
    (h : a ≫ f = p)
    (H : Sheaf (J.over T) (Type z)) (V : Over W) :
    (((J.pseudofunctorOver (Type z)).mapComp'
      f.op.toLoc a.op.toLoc p.op.toLoc (by subst p; rfl)).inv.toNatTrans.app H).hom.app
        (op V) = H.obj.map (Over.homMk
          (V := (Over.map f).obj ((Over.map a).obj V))
          (U := (Over.map p).obj V) (𝟙 V.left) (by simp [Category.assoc, h])).op := by
  subst p
  change ((J.overMapPullbackComp (Type z) a f).hom.app H).hom.app (op V) = _
  rw [GrothendieckTopology.overMapPullbackComp_hom_app_hom_app]
  rfl

/-- Descent transport for a global sheaf is restriction along the identity test map. -/
private theorem global_transport
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {I : Type*} {T : C} {U : I → C}
    {f : ∀ i, U i ⟶ T}
    (H : Sheaf (J.over T) (Type z))
    {W : C} (p : W ⟶ T) {i j : I}
    (a : W ⟶ U i) (b : W ⟶ U j) (ha : a ≫ f i = p) (hb : b ≫ f j = p)
    (V : Over W) :
    ((((J.pseudofunctorOver (Type z)).toDescentData f).obj H).hom
      p a b ha hb).hom.app (op V) =
        H.obj.map (Over.homMk (U := (Over.map (f j)).obj ((Over.map b).obj V))
          (V := (Over.map (f i)).obj ((Over.map a).obj V)) (𝟙 V.left)
          (by simp [Category.assoc, ha, hb])).op := by
  change
    (((J.pseudofunctorOver (Type z)).mapComp'
      (f i).op.toLoc a.op.toLoc p.op.toLoc _).inv.toNatTrans.app H).hom.app (op V) ≫
    (((J.pseudofunctorOver (Type z)).mapComp'
      (f j).op.toLoc b.op.toLoc p.op.toLoc _).hom.toNatTrans.app H).hom.app (op V) = _
  rw [constraint_inv (f i) a p ha H V, constraint_hom (f j) b p hb H V,
    ← H.obj.map_comp, ← op_comp]
  congr 1
  apply congrArg Quiver.Hom.op
  apply Over.OverMorphism.ext
  simp

/-- Evaluate the pullback compatibility of descent transitions. -/
private theorem transition_pullback
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {I : Type*} {T : C} {U : I → C} {f : ∀ i, U i ⟶ T}
    (D : (J.pseudofunctorOver (Type z)).DescentData f)
    {W : C} (p : W ⟶ T) {i j : I} (a : W ⟶ U i) (b : W ⟶ U j)
    (ha : a ≫ f i = p) (hb : b ≫ f j = p) (V : Over W) :
    (D.hom p a b ha hb).hom.app (op V) =
      (D.obj i).obj.map (Over.homMk
        (U := (Over.map (V.hom ≫ a)).obj (Over.mk (𝟙 V.left)))
        (V := (Over.map a).obj V) (𝟙 V.left) (by simp)).op ≫
      (D.hom (V.hom ≫ p) (V.hom ≫ a) (V.hom ≫ b)
        (by simp [Category.assoc, ha]) (by simp [Category.assoc, hb])).hom.app
          (op (Over.mk (𝟙 V.left))) ≫
      (D.obj j).obj.map (Over.homMk
        (V := (Over.map (V.hom ≫ b)).obj (Over.mk (𝟙 V.left)))
        (U := (Over.map b).obj V) (𝟙 V.left) (by simp)).op := by
  have h := Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
    (D.hom p a b ha hb) V.hom (V.hom ≫ a) (V.hom ≫ b) rfl rfl
  rw [D.pullHom_hom V.hom p (V.hom ≫ p) rfl a b ha hb
    (V.hom ≫ a) (V.hom ≫ b) rfl rfl] at h
  have h' := congrArg (fun z ↦ z.hom.app (op (Over.mk (𝟙 V.left)))) h
  change _ =
    (((J.pseudofunctorOver (Type z)).mapComp'
      a.op.toLoc V.hom.op.toLoc (V.hom ≫ a).op.toLoc _).inv.toNatTrans.app
        (D.obj i)).hom.app (op (Over.mk (𝟙 V.left))) ≫
    (D.hom (V.hom ≫ p) (V.hom ≫ a) (V.hom ≫ b) _ _).hom.app
      (op (Over.mk (𝟙 V.left))) ≫
    (((J.pseudofunctorOver (Type z)).mapComp'
      b.op.toLoc V.hom.op.toLoc (V.hom ≫ b).op.toLoc _).hom.toNatTrans.app
        (D.obj j)).hom.app (op (Over.mk (𝟙 V.left))) at h'
  rw [constraint_inv a V.hom (V.hom ≫ a) rfl,
    constraint_hom b V.hom (V.hom ≫ b) rfl] at h'
  rcases V with ⟨V, ⟨⟨⟩⟩, v⟩
  dsimp [GrothendieckTopology.pseudofunctorOver,
    GrothendieckTopology.overMapPullback, Over.map, Comma.mapRight, Over.mk,
    Discrete.natTrans, Over.left, Over.hom] at h' ⊢
  convert h' using 1 <;> congr 3 <;> try simp
  all_goals congr 5 <;> first | exact proof_irrel_heq _ _ | simp [Over.hom]

/-- Inverse representing bijections commute with restriction on underlying maps. -/
private theorem representation_map_left
    {C : Type*} [Category* C] {B : C} {F : (Over B)ᵒᵖ ⥤ Type*} {Y V W : Over B}
    (r : F.RepresentableBy Y) (g : V ⟶ W) (x : F.obj (op W)) :
    (r.homEquiv.symm (F.map g.op x)).left = g.left ≫ (r.homEquiv.symm x).left := by
  exact (congrArg Over.Hom.left (r.comp_homEquiv_symm x g)).symm

/-- The comparison of two representing objects preserves represented elements. -/
private theorem comparison_comp
    {C : Type*} [Category* C] {F : Cᵒᵖ ⥤ Type*} {X Y W : C}
    (b : F.RepresentableBy X) (b' : F.RepresentableBy Y) (x : W ⟶ X) :
    x ≫ (b.uniqueUpToIso b').hom = b'.homEquiv.symm (b.homEquiv x) := by
  change x ≫ b'.homEquiv.symm (b.homEquiv (𝟙 X)) = _
  rw [b'.comp_homEquiv_symm, ← b.homEquiv_comp]
  simp only [Category.comp_id]

/-- Restricting a representation to a slice is represented by the pullback. -/
private noncomputable def restrictRepresentation
    {C : Type*} [Category* C] [HasPullbacks C] {T U : C} (f : U ⟶ T)
    {F : (Over T)ᵒᵖ ⥤ Type z} {X : Over T}
    (b : F.RepresentableBy X) :
    ((Over.map f).op ⋙ F).RepresentableBy ((Over.pullback f).obj X) where
  homEquiv := ((Over.mapPullbackAdj f).homEquiv _ _).symm.trans b.homEquiv
  homEquiv_comp g x := by
    dsimp
    rw [Adjunction.homEquiv_naturality_left_symm, b.homEquiv_comp]

/-- The inverse restricted representation has its specified global component. -/
private theorem restricted_fst
    {C : Type*} [Category* C] [HasPullbacks C] {T U : C} (f : U ⟶ T)
    {F : (Over T)ᵒᵖ ⥤ Type z} {X : Over T}
    (b : F.RepresentableBy X) {V : Over U}
    (x : F.obj (op ((Over.map f).obj V))) :
    ((restrictRepresentation f b).homEquiv.symm x).left ≫ pullback.fst X.hom f =
      (b.homEquiv.symm x).left := by
  dsimp [restrictRepresentation, Over.mapPullbackAdj, Adjunction.homEquiv]
  simp

/-- A Cartesian square represents the restricted functor of points. -/
private noncomputable def pullbackRepresentation
    {C : Type v} [Category.{w} C] {T U : C} (f : U ⟶ T) (V : Over U) (X : Over T)
    (q : V.left ⟶ X.left) (h : IsPullback q V.hom X.hom f) :
    ((Over.map f).op ⋙ uliftYoneda.{z}.obj X).RepresentableBy V where
  homEquiv := fun {W} ↦
    { toFun := fun x ↦ ULift.up (Over.homMk (x.left ≫ q) (by
        change (x.left ≫ q) ≫ X.hom = W.hom ≫ f
        rw [Category.assoc, h.w, ← Category.assoc, Over.w]))
      invFun := fun x ↦ Over.homMk
        (h.lift x.down.left W.hom (Over.w x.down))
      left_inv := fun x ↦ by
        apply Over.OverMorphism.ext
        apply h.hom_ext <;> simp
      right_inv := fun x ↦ by
        apply ULift.ext
        apply Over.OverMorphism.ext
        simp }
  homEquiv_comp g x := by
    apply ULift.ext
    apply Over.OverMorphism.ext
    simp

/-- A global representation gives Cartesian local realizations. -/
private theorem effective_of_representation
    {C : Type v} [Category.{w} C] [HasPullbacks C] {J : GrothendieckTopology C}
    {I : Type*} {T : C} {U : I → C}
    {f : ∀ i, U i ⟶ T} (D : (J.pseudofunctorOver (Type z)).DescentData f)
    (Y : ∀ i, Over (U i)) (r : ∀ i, (D.obj i).obj.RepresentableBy (Y i))
    (H : Sheaf (J.over T) (Type z))
    (e : ((J.pseudofunctorOver (Type z)).toDescentData f).obj H ≅
      D) (hH : H.obj.IsRepresentable) : ∃ (X : Over T) (q : ∀ i, (Y i).left ⟶ X.left),
      (∀ i, IsPullback (q i) (Y i).hom X.hom (f i)) ∧
      ∀ (W : C) (p : W ⟶ T) (i j : I)
        (a : W ⟶ U i) (b : W ⟶ U j) (ha : a ≫ f i = p) (hb : b ≫ f j = p)
        (x : (D.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 W))))),
        ((r j).homEquiv.symm
          ((D.hom p a b ha hb).hom.app (op (Over.mk (𝟙 W))) x)).left ≫ q j =
          ((r i).homEquiv.symm x).left ≫ q i := by
  let := hH
  let X := H.obj.reprX
  let b := H.obj.representableBy
  let c (i : I) :
      (((J.overMapPullback (Type z) (f i)).obj H).obj ≅
        (D.obj i).obj) :=
    (sheafToPresheaf _ _).mapIso
      { hom := e.hom.hom i
        inv := e.inv.hom i
        hom_inv_id := by
          have h := congrArg (fun z ↦ z.hom i) e.hom_inv_id
          simpa only [Pseudofunctor.DescentData.comp_hom,
            Pseudofunctor.DescentData.id_hom] using h
        inv_hom_id := by
          have h := congrArg (fun z ↦ z.hom i) e.inv_hom_id
          simpa only [Pseudofunctor.DescentData.comp_hom,
            Pseudofunctor.DescentData.id_hom] using h }
  let k (i : I) : Y i ≅ (Over.pullback (f i)).obj X :=
    (r i).uniqueUpToIso ((restrictRepresentation (f i) b).ofIso (c i))
  let q (i : I) := (k i).hom.left ≫ pullback.fst X.hom (f i)
  refine ⟨X, q, ?_, ?_⟩
  · intro i
    exact (IsPullback.of_hasPullback X.hom (f i)).of_iso'
      ((Over.forget (U i)).mapIso (k i)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [q]) (by simpa using Over.w (k i).hom) (by simp) (by simp)
  · intro W p i j a a' ha ha' x
    have coord (i : I) (W : Over (U i)) (x : W ⟶ Y i) :
        x.left ≫ q i =
          (b.homEquiv.symm ((c i).inv.app (op W)
            ((r i).homEquiv x))).left := by
      have hk := comparison_comp (r i)
        ((restrictRepresentation (f i) b).ofIso (c i)) x
      have hk' := congrArg
        (fun z ↦ z.left ≫ pullback.fst X.hom (f i)) hk
      have hk'' := (restricted_fst (f i) b
        ((c i).inv.app (op W) ((r i).homEquiv x)))
      have h₁ : x.left ≫ q i =
          (((restrictRepresentation (f i) b).ofIso (c i)).homEquiv.symm
            ((r i).homEquiv x)).left ≫ pullback.fst X.hom (f i) := by
        simpa only [Over.comp_left, Category.assoc] using hk'
      exact h₁.trans hk''
    rw [coord, coord]
    have hc := e.inv.comm p a a' ha ha'
    have hx := congrArg (fun z ↦ z.hom.app (op (Over.mk (𝟙 W))) x) hc
    change _ ≫ _ = _ at hc
    change
      ((((J.pseudofunctorOver (Type z)).toDescentData f).obj H).hom
        p a a' ha ha').hom.app (op (Over.mk (𝟙 W)))
        ((e.inv.hom i).hom.app (op ((Over.map a).obj (Over.mk (𝟙 W)))) x) =
      (e.inv.hom j).hom.app (op ((Over.map a').obj (Over.mk (𝟙 W))))
        ((D.hom p a a' ha ha').hom.app (op (Over.mk (𝟙 W))) x) at hx
    rw [global_transport H p a a' ha ha'] at hx
    simp only [Equiv.apply_symm_apply]
    change _ = _ at hx
    change (b.homEquiv.symm ((e.inv.hom j).hom.app _
      ((D.hom p a a' ha ha').hom.app _ x))).left =
      (b.homEquiv.symm ((e.inv.hom i).hom.app _ x)).left
    have h₂ := congrArg (fun y ↦ (b.homEquiv.symm y).left) hx.symm
    let m : (Over.map (f j)).obj ((Over.map a').obj (Over.mk (𝟙 W))) ⟶
        (Over.map (f i)).obj ((Over.map a).obj (Over.mk (𝟙 W))) :=
      Over.homMk (𝟙 W) (by simp [ha, ha'])
    have hm := congrArg Over.Hom.left
      (b.comp_homEquiv_symm
        ((e.inv.hom i).hom.app (op ((Over.map a).obj (Over.mk (𝟙 W)))) x) m)
    have h₃ : (b.homEquiv.symm (H.obj.map m.op
        ((e.inv.hom i).hom.app (op ((Over.map a).obj (Over.mk (𝟙 W)))) x))).left =
        (b.homEquiv.symm
          ((e.inv.hom i).hom.app (op ((Over.map a).obj (Over.mk (𝟙 W)))) x)).left := by
      simpa [m] using hm.symm
    exact h₂.trans h₃

/-- A geometric realization represents the sheaf obtained by descent. -/
private theorem representation_of_effective
    {C : Type v} [Category.{w} C] [HasPullbacks C] {J : GrothendieckTopology C}
    [J.Subcanonical] {I : Type*} {T : C} {U : I → C}
    {f : ∀ i, U i ⟶ T} (D : (J.pseudofunctorOver (Type (max z w))).DescentData f)
    (Y : ∀ i, Over (U i)) (r : ∀ i, (D.obj i).obj.RepresentableBy (Y i))
    (H : Sheaf (J.over T) (Type (max z w)))
    (e : ((J.pseudofunctorOver (Type (max z w))).toDescentData f).obj H ≅
      D)
    (hL : ((J.pseudofunctorOver (Type (max z w))).toDescentData f).FullyFaithful)
    (X : Over T) (q : ∀ i, (Y i).left ⟶ X.left)
    (hq : ∀ i, IsPullback (q i) (Y i).hom X.hom (f i))
    (ht : ∀ (W : C) (p : W ⟶ T) (i j : I)
      (a : W ⟶ U i) (b : W ⟶ U j) (ha : a ≫ f i = p) (hb : b ≫ f j = p)
      (x : (D.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 W))))),
      ((r j).homEquiv.symm
        ((D.hom p a b ha hb).hom.app (op (Over.mk (𝟙 W))) x)).left ≫ q j =
          ((r i).homEquiv.symm x).left ≫ q i) : H.obj.IsRepresentable := by
  classical
  let K : Sheaf (J.over T) (Type (max z w)) :=
    ⟨uliftYoneda.{z}.obj X, (isSheaf_iff_isSheaf_of_type _ _).2
      ((Presieve.isSheaf_comp_uliftFunctor_iff _).2
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)))⟩
  let c (i : I) : (D.obj i).obj ≅
      ((J.overMapPullback (Type (max z w)) (f i)).obj K).obj :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{z} _ _ (r i)).symm ≪≫
      (Functor.RepresentableBy.equivUliftYonedaIso.{z} _ _
        (pullbackRepresentation (f i) (Y i) X (q i) (hq i)))
  let d : D ≅
      ((J.pseudofunctorOver (Type (max z w))).toDescentData f).obj K :=
    Pseudofunctor.DescentData.isoMk (fun i ↦
      (fullyFaithfulSheafToPresheaf _ _).preimageIso (c i)) (by
        intro W p i j a b ha hb
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        apply ConcreteCategory.hom_ext
        intro x
        change
          ((((J.pseudofunctorOver (Type (max z w))).toDescentData f).obj K).hom
            p a b ha hb).hom.app V
            ((c i).hom.app (op ((Over.map a).obj V.unop)) x) =
          (c j).hom.app (op ((Over.map b).obj V.unop))
            ((D.hom p a b ha hb).hom.app V x)
        rw [global_transport K p a b ha hb]
        dsimp [c, Functor.RepresentableBy.equivUliftYonedaIso, pullbackRepresentation]
        apply ULift.ext
        apply Over.OverMorphism.ext
        rw [transition_pullback D p a b ha hb V.unop]
        dsimp [K, uliftYoneda]
        simp only [Category.id_comp]
        rw [representation_map_left]
        simp only [Over.homMk_left]
        let k : (Over.map (V.unop.hom ≫ a)).obj (Over.mk (𝟙 V.unop.left)) ⟶
            (Over.map a).obj V.unop := Over.homMk (𝟙 V.unop.left) (by simp)
        have h := ht V.unop.left (V.unop.hom ≫ p) i j
          (V.unop.hom ≫ a) (V.unop.hom ≫ b)
          (by simp [Category.assoc, ha]) (by simp [Category.assoc, hb])
          ((D.obj i).obj.map k.op x)
        rw [representation_map_left] at h
        dsimp [k] at h
        erw [Category.id_comp ((r i).homEquiv.symm x).left] at h
        conv_rhs => lhs; erw [Category.id_comp]
        exact h.symm)
  let z := hL.preimageIso (e ≪≫ d)
  exact isRepresentable_of_natIso K.obj
    ((sheafToPresheaf _ _).mapIso z.symm)

/-- An equivalence between scheme descent data and locally representable fppf sheaves,
compatible with all local schemes and transitions, and with geometric effectivity.
Source: Stacks Project, Descent, Tag 02W5, including clauses (1) and (2)
(blueprint: lem-trf-fppf-sheaf-representability-descent-data).

The natural isomorphism of functors identifies the entire given local descent datum with
restriction of the global sheaf, so fixes the overlap maps as well as the local objects.
The second clause explicitly identifies the schemes representing `h_{U_i} × H`.
The last clause uses geometric effectivity, defined using Cartesian scheme squares.

Proof, following the nine steps of the node:
1. Every fppf covering is fpqc. Flatness is part of def-pc-fppf-site; after restricting to
   an affine open, lem-pc-fppf-affine-refinement gives the finitely many affine opens
   required by def-weil-pbc-fpqc-covering (Stacks Tags 022C and 021P).
2. Representable presheaves over every base are fppf sheaves by
   lem-weil-pbc-fpqc-representable-descent. The glued map remains over the base by
   uniqueness applied to the base scheme. This is the sheaf axiom of
   def-weil-pbc-sites-and-cohomology.
3. A representation of h_{U_i} × H induces X_i → U_i by lem-pc-yoneda. Fibres over each
   W → U_i give the representing bijection for H restricted to the slice. Conversely,
   separating maps by their composite to U_i gives the product representation. These
   identifications commute with restrictions (def-pur-localized-ringed-site).
4. By def-pc-fibre-product, both overlap schemes represent h_{U_i} × H × h_{U_j}.
   Lem-pc-representable-unique gives their comparison, preserving both base coordinates.
   Both triple-overlap composites preserve these coordinates and the H coordinate;
   lem-pc-yoneda gives their equality. The same argument defines local maps for sheaf
   maps and proves identities and composition, giving the functor to scheme data.
5. Conversely the local schemes represent sheaves on the slices. The scheme transition
   isomorphisms give compatible sheaf isomorphisms on double slices and satisfy the
   cocycle. Apply lem-pe-set-sheaf-cover-descent (Tags 04TR and 04TQ), with fibre products
   and terminal object T, in def-weil-size-convention's universes, to glue a sheaf H_D.
6. The local representing bijections assemble over all W → U_i into the representation
   of h_{U_i} × H_D by X_i. The gluing equality on double slices identifies the resulting
   transition with the specified one; lem-pc-yoneda gives the full datum isomorphism.
7. Compatible scheme maps induce compatible maps of the local represented sheaves.
   The morphism clause of lem-pe-set-sheaf-cover-descent glues them uniquely. Uniqueness
   gives identities and composition and makes the datum comparison natural.
8. Starting with H, the local identifications glue to G(R(H)) ≅ H. Glue their inverses
   too; uniqueness makes the composites identities. Naturality follows by checking on
   slices and using the same uniqueness. Together with step 7 this gives the equivalence
   and the natural comparison of its restriction with the given descent datum.
9. If H is represented by X, def-pc-fibre-product represents each local product by
   X ×_T U_i; lem-pc-representable-unique identifies its transitions with the canonical
   ones, so the datum is effective in the sense of def-pd-descent-datum. Conversely a
   geometric realization supplies compatible local isomorphisms h_X ≅ H. By step 2
   h_X is a sheaf; lem-pe-set-sheaf-cover-descent glues these maps and their inverses,
   and uniqueness proves that they are inverse. Thus H is representable. -/
theorem fppfSheafRepresentabilityDescentData
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T) :
    ∃ e : SchemeCoverDescent f ≌ (IsLocallyRepresentableFppfSheaf f).FullSubcategory,
      Nonempty
        (e.functor ⋙ (IsLocallyRepresentableFppfSheaf f).ι ⋙
            (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f ≅
          schemeCoverDescentForget f) ∧
      (∀ (D : SchemeCoverDescent f) (i : I),
        Nonempty
          ((Limits.prod (uliftYoneda.{u + 1}.obj (Over.mk (f i)))
            (e.functor.obj D).obj.obj).RepresentableBy
              ((Over.map (f i)).obj (D.localScheme i)))) ∧
      (∀ D : SchemeCoverDescent f,
        (e.functor.obj D).obj.obj.IsRepresentable ↔ D.IsEffective) := by
  classical
  let A := (IsLocallyRepresentableFppfSheaf f).FullSubcategory
  let L := (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f
  have hcov' : Sieve.ofArrows U f ∈ Scheme.fppfTopology T :=
    Scheme.fppfPrecoverage.generate_mem_toGrothendieck hcov
  obtain ⟨_, ⟨hL⟩⟩ := setSheafCoverDescent Scheme.fppfTopology T U f hcov'
  let := hL.full
  let := hL.faithful
  obtain ⟨G, e, β, _, _⟩ := fppfSchemeDataSheafGluing T U f hcov
  let localObj (H : A) (i : I) : Over (U i) := by
    let := H.property i
    exact Functor.reprX
      (((Scheme.fppfTopology.overMapPullback (Type (u + 1)) (f i)).obj H.obj).obj)
  let localRep (H : A) (i : I) :
      Functor.RepresentableBy
        (((Scheme.fppfTopology.overMapPullback (Type (u + 1)) (f i)).obj H.obj).obj)
        (localObj H i) := by
    let := H.property i
    exact Functor.representableBy _
  let RH (H : A) : SchemeCoverDescent f :=
    { data := L.obj H.obj, localScheme := localObj H, representation := localRep H }
  let hForget : (schemeCoverDescentForget f).FullyFaithful :=
    fullyFaithfulInducedFunctor (SchemeCoverDescentDatum.data (f := f))
  let := hForget.full
  let := hForget.faithful
  let hG : (G ⋙ (IsLocallyRepresentableFppfSheaf f).ι ⋙ L).FullyFaithful :=
    hForget.ofIso e.symm
  let hG' : G.FullyFaithful := hG.ofCompFaithful
  let := hG'.full
  let := hG'.faithful
  let : G.EssSurj := ⟨fun H ↦ by
    refine ⟨RH H, ⟨?_⟩⟩
    apply (Functor.FullyFaithful.ofFullyFaithful
      ((IsLocallyRepresentableFppfSheaf f).ι ⋙ L)).preimageIso
    exact e.app (RH H)⟩
  let : G.IsEquivalence := {}
  refine ⟨G.asEquivalence, ⟨e⟩, fun D i ↦ ⟨β D i⟩, ?_⟩
  intro D
  constructor
  · exact effective_of_representation D.data D.localScheme D.representation
      (G.obj D).obj (e.app D)
  · intro hD
    obtain ⟨X, q, hq, ht⟩ := hD
    exact representation_of_effective.{u + 1, u + 1, u, u + 1} D.data D.localScheme D.representation
      (G.obj D).obj (e.app D) hL X q hq ht

end AlgebraicGeometry
