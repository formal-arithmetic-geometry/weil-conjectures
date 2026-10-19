/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.CategoryTheory.SiteCoveringAxioms

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Geometric stalks as inverse images of topos points

Source: Stacks Project, Tags 0991, 04FM, and 00Y8
(blueprint: lem-fix-geometric-stalk-topos-point).

The two clauses cover the small etale and small pro-etale sites. The right adjoint's
underlying presheaf is specified as functions on lifts, including all its restriction maps.
The pro-etale stalk functor uses the already defined pointed-neighbourhood colimit.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The function presheaves attached to a lift functor `L`: the value at `U` is
`L(U) → T`, restriction is precomposition with `L.map`, and a map of sets acts by
postcomposition. This is the presheaf `p_*T` of the statement.
Source: Stacks Project, Tag 00Y8 (blueprint: lem-fix-geometric-stalk-topos-point). -/
def geometricLiftFunctionPresheaf {C : Type v} [Category.{w} C] (L : C ⥤ Type u) :
    Type (u + 1) ⥤ (Cᵒᵖ ⥤ Type (u + 1)) where
  obj T :=
    { obj U := L.obj U.unop → T
      map f := ↾fun a x ↦ a (L.map f.unop x)
    }
  map t := { app U := ↾fun a x ↦ t (a x) }

private theorem liftFunction_isSheaf
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C) (L : C ⥤ Type u)
    [IsCofiltered L.Elements]
    (hl : ∀ (X : C) (R : Sieve X), R ∈ J X → ∀ x : L.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : L.obj Y), L.map f y = x)
    (T : Type (u + 1)) :
    Presheaf.IsSheaf J ((geometricLiftFunctionPresheaf L).obj T) := by
  classical
  rw [isSheaf_iff_isSheaf_of_type]
  intro X R hR x hx
  choose Y f hf y hy using hl X R hR
  let a : L.obj X → T := fun z ↦ x (f z) (hf z) (y z)
  have hv {V : C} (g : V ⟶ X) (hg : R g) (z : L.obj V) :
      a (L.map g z) = x g hg z := by
    let α : L.elementsMk V z ⟶ L.elementsMk X (L.map g z) := ⟨g, rfl⟩
    let β : L.elementsMk (Y (L.map g z)) (y (L.map g z)) ⟶
        L.elementsMk X (L.map g z) := ⟨f _, hy _⟩
    obtain ⟨q, q₁, q₂, hq⟩ := IsCofiltered.cospan α β
    have he : q₁.val ≫ g = q₂.val ≫ f (L.map g z) := by
      exact congrArg Subtype.val hq
    have h₁ : L.map q₁.val q.snd = z := q₁.prop
    have h₂ : L.map q₂.val q.snd = y (L.map g z) := q₂.prop
    have h := congrFun (hx q₁.val q₂.val hg (hf _) he) q.snd
    change x g hg (L.map q₁.val q.snd) =
      x (f _) (hf _) (L.map q₂.val q.snd) at h
    simpa [a, h₁, h₂] using h.symm
  refine ⟨a, ?_, ?_⟩
  · intro V g hg
    funext z
    exact hv g hg z
  · intro b hb
    funext z
    have h := congrFun (hb (f z) (hf z)) (y z)
    change b (L.map (f z) (y z)) = a z at h
    simpa [hy z] using h

private noncomputable def liftFunctionSheafFunctor
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C) (L : C ⥤ Type u)
    [IsCofiltered L.Elements]
    (hl : ∀ (X : C) (R : Sieve X), R ∈ J X → ∀ x : L.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : L.obj Y), L.map f y = x) :
    Type (u + 1) ⥤ Sheaf J (Type (u + 1)) where
  obj T := ⟨(geometricLiftFunctionPresheaf L).obj T, liftFunction_isSheaf J L hl T⟩
  map f := ⟨(geometricLiftFunctionPresheaf L).map f⟩

private noncomputable def pointLiftFunctionHomEquiv
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{u} J)
    (F : Sheaf J (Type (u + 1))) (T : Type (u + 1)) :
    (Φ.sheafFiber.obj F ⟶ T) ≃
      (F ⟶ (liftFunctionSheafFunctor J Φ.fiber
        (fun _ R hR x ↦ Φ.jointly_surjective R hR x)).obj T) where
  toFun a := ⟨{ app U := ↾fun s x ↦ a (Φ.toPresheafFiber U.unop x F.obj s)
                naturality {U V} g := by
                  apply ConcreteCategory.hom_ext
                  intro s
                  funext x
                  exact congrArg a (ConcreteCategory.congr_hom
                    (Φ.toPresheafFiber_w g.unop x F.obj) s) }⟩
  invFun b := Φ.presheafFiberDesc (fun U x ↦ ↾fun s ↦ b.hom.app (op U) s x) (by
    intro U V f x
    ext s
    exact congrFun (ConcreteCategory.congr_hom (b.hom.naturality f.op) s) x)
  left_inv a := by
    apply Φ.presheafFiber_hom_ext
    intro U x
    simp
    rfl
  right_inv b := by
    ext U s
    funext x
    exact ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_presheafFiberDesc
        (fun U x ↦ ↾fun s ↦ b.hom.app (op U) s x) _ U.unop x) s

private noncomputable def pointLiftFunctionAdjunction
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{u} J) :
    Φ.sheafFiber (A := Type (u + 1)) ⊣
      liftFunctionSheafFunctor J Φ.fiber
        (fun _ R hR x ↦ Φ.jointly_surjective R hR x) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pointLiftFunctionHomEquiv Φ
      homEquiv_naturality_left_symm := by
        intro F G T f b
        apply Φ.presheafFiber_hom_ext
        intro U x
        change Φ.toPresheafFiber U x F.obj ≫
          Φ.presheafFiberDesc _ _ = Φ.toPresheafFiber U x F.obj ≫
          Φ.presheafFiber.map f.hom ≫ Φ.presheafFiberDesc _ _
        rw [Φ.toPresheafFiber_naturality_assoc]
        simp
        rfl
      homEquiv_naturality_right := by
        intro F T T' a t
        rfl }

set_option backward.isDefEq.respectTransparency false in
private theorem proEtaleLift_surjective
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (U : Y.ProEt) (R : Sieve U)
    (hR : R ∈ ProEt.topology Y U)
    (x : (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))).obj U) :
    ∃ (V : Y.ProEt) (f : V ⟶ U) (_ : R f)
      (z : (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))).obj V),
      (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))).map f z = x := by
  have : (ProEt.precoverage Y).IsStableUnderComposition := by
    dsimp [ProEt.precoverage]
    infer_instance
  have : (ProEt.precoverage Y).IsStableUnderBaseChange := by
    dsimp [ProEt.precoverage]
    infer_instance
  have : (ProEt.precoverage Y).HasIsos := by
    dsimp [ProEt.precoverage]
    infer_instance
  obtain ⟨P, hP, hle⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hR
  obtain ⟨ι, V, f, rfl⟩ := P.exists_eq_ofArrows
  change (Presieve.ofArrows V f).map (ProEt.forget Y ⋙ Over.forget Y) ∈
    proetalePrecoverage U.left at hP
  rw [Presieve.map_ofArrows] at hP
  have h := (ofArrows_mem_precoverage_iff _).mp hP.2
  obtain ⟨i, z, hz⟩ := h.1 (x.left (default : Spec (.of Ω)))
  have : WeaklyEtale (f i).left := h.2 i
  let Q := pullback x.left (f i).left
  let q : Q ⟶ Spec (.of Ω) := pullback.fst _ _
  have : WeaklyEtale q := by dsimp [q, Q]; infer_instance
  obtain ⟨zq, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := x.left) (g := (f i).left) (default : Spec (.of Ω)) z hz.symm
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_weaklyEtale q zq
  refine ⟨V i, f i, hle _ _ ⟨i⟩,
    Over.homMk (s ≫ pullback.snd x.left (f i).left) ?_, ?_⟩
  · change (s ≫ pullback.snd x.left (f i).left) ≫ (V i).hom = y
    have hf : (f i).left ≫ U.hom = (V i).hom := Over.w (f i).hom
    rw [← hf, ← Category.assoc, Category.assoc s, ← pullback.condition,
      ← Category.assoc, hs, Category.id_comp]
    exact Over.w x
  · change Over.homMk (s ≫ pullback.snd x.left (f i).left) _ ≫
      (ProEt.forget Y).map (f i) = x
    apply CommaMorphism.ext
    · change (s ≫ pullback.snd x.left (f i).left) ≫ (f i).left = x.left
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]
    · apply Subsingleton.elim

/-- The set-valued pro-etale geometric stalk as a functor. Its object at `F` is
`proEtaleGeometricSetStalk y F`; maps are the colimit maps induced by sectionwise maps.
Source: Stacks Project, Tag 0991 (blueprint: lem-fix-geometric-stalk-topos-point). -/
noncomputable def proEtaleGeometricSetStalkFunctor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    Sheaf (ProEt.topology Y) (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafToPresheaf (ProEt.topology Y) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
      (proEtaleGeometricNeighbourhoodForget y).op ⋙ colim

private instance proEtaleLift_isCofiltered
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    IsCofiltered (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))).Elements :=
  Functor.isCofiltered_elements _

private noncomputable def proEtaleFunctionSheafFunctor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    Type (u + 1) ⥤ Sheaf (ProEt.topology Y) (Type (u + 1)) :=
  liftFunctionSheafFunctor _ (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y)))
    (proEtaleLift_surjective y)

private noncomputable def proEtaleGerm
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (U : Y.ProEt)
    (x : Over.mk y ⟶ (ProEt.forget Y).obj U)
    (F : Sheaf (ProEt.topology Y) (Type (u + 1))) :
    F.obj.obj (op U) ⟶ (proEtaleGeometricSetStalkFunctor y).obj F :=
  colimit.ι (proEtaleGeometricStalkDiagram y F) (op (StructuredArrow.mk x))

private theorem proEtaleGerm_w
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {U V : Y.ProEt} (f : U ⟶ V)
    (x : Over.mk y ⟶ (ProEt.forget Y).obj U)
    (F : Sheaf (ProEt.topology Y) (Type (u + 1))) :
    F.obj.map f.op ≫ proEtaleGerm y U x F =
      proEtaleGerm y V (x ≫ (ProEt.forget Y).map f) F :=
  colimit.w (proEtaleGeometricStalkDiagram y F)
    (show StructuredArrow.mk x ⟶
      StructuredArrow.mk (x ≫ (ProEt.forget Y).map f) from
      StructuredArrow.homMk f rfl).op

private noncomputable def proEtaleFunctionHomEquiv
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (Type (u + 1))) (T : Type (u + 1)) :
    ((proEtaleGeometricSetStalkFunctor y).obj F ⟶ T) ≃
      (F ⟶ (proEtaleFunctionSheafFunctor y).obj T) where
  toFun a := ⟨{ app U := ↾fun s x ↦ a (proEtaleGerm y U.unop x F s)
                naturality {U V} g := by
                  apply ConcreteCategory.hom_ext
                  intro s
                  funext x
                  exact congrArg a (ConcreteCategory.congr_hom
                    (proEtaleGerm_w y g.unop x F) s) }⟩
  invFun b := colimit.desc _
    { pt := T
      ι :=
        { app n := ↾fun s ↦ b.hom.app (op n.unop.right) s n.unop.hom
          naturality {n m} f := by
            apply ConcreteCategory.hom_ext
            intro s
            have h := congrFun (ConcreteCategory.congr_hom
              (b.hom.naturality f.unop.right.op) s) m.unop.hom
            change b.hom.app _ (F.obj.map f.unop.right.op s) m.unop.hom =
              b.hom.app _ s (m.unop.hom ≫ (ProEt.forget Y).map f.unop.right) at h
            change b.hom.app _ (F.obj.map f.unop.right.op s) m.unop.hom =
              b.hom.app _ s n.unop.hom
            simpa only [StructuredArrow.w f.unop] using h } }
  left_inv a := by
    apply colimit.hom_ext
    rintro ⟨⟨⟨⟨⟩⟩, U, x⟩⟩
    simp
    rfl
  right_inv b := by
    ext U s
    funext x
    change (colimit.ι (proEtaleGeometricStalkDiagram y F)
      (op (StructuredArrow.mk x)) ≫ _) s = _
    erw [colimit.ι_desc]
    rfl

private noncomputable def proEtaleFunctionAdjunction
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    proEtaleGeometricSetStalkFunctor y ⊣ proEtaleFunctionSheafFunctor y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := proEtaleFunctionHomEquiv y
      homEquiv_naturality_left_symm := by
        intro F G T f b
        apply colimit.hom_ext
        intro n
        dsimp [proEtaleFunctionHomEquiv, proEtaleGeometricSetStalkFunctor]
        rw [colimit.ι_desc, ι_colimMap_assoc, colimit.ι_desc]
        rfl
      homEquiv_naturality_right := by
        intro F T T' a t
        rfl }

/-- On either small site the prescribed function presheaves form a sheaf-valued functor
right adjoint to the geometric stalk, and that stalk preserves finite limits. Existence
of the sheaf-valued functor with the displayed underlying presheaf equality states that
`p_*T` is a sheaf for every `T`. The adjunction with its left exact left adjoint is the
specified morphism of topoi from sets.
Source: Stacks Project, Tags 0991, 04FM, and 00Y8
(blueprint: lem-fix-geometric-stalk-topos-point).

Proof:
1. The index is the opposite pointed-neighbourhood category. It is filtered by
   lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered or
   def-weil-proetale-geometric-stalk. The chosen size bound makes the index small in
   the larger universe. Colimit maps of sectionwise natural transformations give the
   stalk functor, with identity and composition from colimit uniqueness.
2. Etale covers lift the geometric point with the same field by
   lem-weil-pbc-etale-cover-geometric-point-lift.
3. For a pro-etale covering sieve, take a covering family contained in it and choose
   a covering point above the image of the given geometric lift. The pullback to
   Spec Omega has a point and its projection is weakly etale. The existing
   exists_comp_eq_id_of_weaklyEtale gives a section through this nonempty pullback.
   Its composite with the other projection is the required lift, with the lift
   equation following from the pullback equation and the section equation.
4. The category of elements of the lift functor is cofiltered. A matching family
   of functions glues by choosing a covering lift of each element and evaluating
   there. A common pointed refinement compares this value with any other covering
   lift, proving compatibility and independence. Covering surjectivity proves
   uniqueness. Postcomposition defines the sheaf-valued functor.
5. A map a from the stalk to T gives the sheaf map s ↦ (u ↦ a(ι_(U,u)(s))). The
   pointed-arrow cocone identity proves naturality under restriction.
6. Conversely a sheaf map b gives the cocone s ↦ b_U(s)(u). The colimit universal
   property gives its unique map to T. These constructions are inverse and natural in
   the sheaf and in T, hence define the adjunction.
7. Sheaf limits are sectionwise by lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
   The canonical comparison between the stalk of a finite limit and the limit of the
   stalks is invertible by lem-weil-pbc-filtered-colimits-commute-finite-limits, with
   the same filtered index for every sheaf. This includes the empty finite diagram.
   The adjunction is therefore a morphism of topoi with the specified inverse image. -/
theorem geometricStalkToposPoint
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    (∃ R : Type (u + 1) ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)),
      R ⋙ sheafToPresheaf Y.smallEtaleTopology (Type (u + 1)) =
        geometricLiftFunctionPresheaf (pointSmallEtale y).fiber ∧
      Nonempty ((pointSmallEtale y).sheafFiber (A := Type (u + 1)) ⊣ R) ∧
      PreservesFiniteLimits ((pointSmallEtale y).sheafFiber (A := Type (u + 1)))) ∧
    (∃ R : Type (u + 1) ⥤ Sheaf (ProEt.topology Y) (Type (u + 1)),
      R ⋙ sheafToPresheaf (ProEt.topology Y) (Type (u + 1)) =
        geometricLiftFunctionPresheaf
          (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))) ∧
      Nonempty (proEtaleGeometricSetStalkFunctor y ⊣ R) ∧
      PreservesFiniteLimits (proEtaleGeometricSetStalkFunctor y)) := by
  constructor
  · let Φ := pointSmallEtale y
    have : PreservesFiniteLimits (Φ.sheafFiber (A := Type (u + 1))) := by
      have : PreservesFiniteLimits
          (Φ.presheafFiber (A := Type (u + 1))) := by
        dsimp [CategoryTheory.GrothendieckTopology.Point.presheafFiber]
        infer_instance
      dsimp [CategoryTheory.GrothendieckTopology.Point.sheafFiber]
      infer_instance
    refine ⟨liftFunctionSheafFunctor _ Φ.fiber
      (fun _ R hR x ↦ Φ.jointly_surjective R hR x), rfl,
      ⟨pointLiftFunctionAdjunction Φ⟩, inferInstance⟩
  · have : PreservesFiniteLimits (proEtaleGeometricSetStalkFunctor y) := by
      dsimp [proEtaleGeometricSetStalkFunctor]
      infer_instance
    exact ⟨proEtaleFunctionSheafFunctor y, rfl, ⟨proEtaleFunctionAdjunction y⟩,
      inferInstance⟩

end AlgebraicGeometry.Scheme
