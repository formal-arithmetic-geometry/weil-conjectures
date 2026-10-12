/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal

/-! # Left derived values invert the multiplicative system

Source: Stacks Project, Derived Categories, Lemma 05SB(2)
(blueprint: lem-pur-derived-functor-inverts-05sb).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private theorem denominator_cofiltered
    {C : Type u} [Category.{v} C] (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) : IsCofiltered (S.Over ⊤ X) := by
  refine {
    nonempty := ⟨MorphismProperty.Over.mk (P := S) ⊤ (𝟙 X) (S.id_mem X)⟩
    cone_objs := ?_
    cone_maps := ?_ }
  · intro a b
    obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk a.hom b.hom b.prop).exists_rightFraction
    let q := MorphismProperty.Over.mk (P := S) ⊤ (ψ.s ≫ a.hom)
      (S.comp_mem _ _ ψ.hs a.prop)
    exact ⟨q, MorphismProperty.Over.homMk ψ.s,
      MorphismProperty.Over.homMk ψ.f hψ.symm, trivial⟩
  · intro a b f g
    obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
      f.left g.left b.hom b.prop (f.w.trans g.w.symm)
    let q := MorphismProperty.Over.mk (P := S) ⊤ (t ≫ a.hom)
      (S.comp_mem _ _ ht a.prop)
    exact ⟨q, MorphismProperty.Over.homMk t, MorphismProperty.Over.Hom.ext heq⟩

private def denominatorPostcompose
    {C : Type u} [Category.{v} C] (S : MorphismProperty C) [S.IsMultiplicative]
    {X Y : C} (s : X ⟶ Y) (hs : S s) : S.Over ⊤ X ⥤ S.Over ⊤ Y where
  obj a := MorphismProperty.Over.mk (P := S) ⊤ (a.hom ≫ s)
    (S.comp_mem _ _ a.prop hs)
  map f := MorphismProperty.Over.homMk f.left (by
    change f.left ≫ (_ ≫ s) = _ ≫ s
    rw [← Category.assoc, MorphismProperty.Over.w f])
  map_id a := MorphismProperty.Over.Hom.ext rfl
  map_comp f g := MorphismProperty.Over.Hom.ext rfl

private theorem denominatorPostcompose_initial
    {C : Type u} [Category.{v} C] (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] {X Y : C} (s : X ⟶ Y) (hs : S s) :
    (denominatorPostcompose S s hs).Initial := by
  let := denominator_cofiltered S X
  apply Functor.initial_of_exists_of_isCofiltered
  · intro b
    obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk s b.hom b.prop).exists_rightFraction
    exact ⟨MorphismProperty.Over.mk (P := S) ⊤ ψ.s ψ.hs,
      ⟨MorphismProperty.Over.homMk ψ.f hψ.symm⟩⟩
  · intro b a f g
    obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
      f.left g.left b.hom b.prop (f.w.trans g.w.symm)
    let q := MorphismProperty.Over.mk (P := S) ⊤ (t ≫ a.hom)
      (S.comp_mem _ _ ht a.prop)
    exact ⟨q, MorphismProperty.Over.homMk t, MorphismProperty.Over.Hom.ext heq⟩

private theorem proConeIsLimit
    {J : Type u} [Category.{v} J] {D : Type uD} [Category.{vD} D]
    (G : J ⥤ D) (L : D) (u : (Functor.const J).obj L ⟶ G)
    (hu : ∃ j₀ : J, ∃ r : G.obj j₀ ⟶ L, u.app j₀ ≫ r = 𝟙 L ∧
      ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
        G.map b = G.map a ≫ r ≫ u.app j) : Nonempty (IsLimit (Cone.mk L u)) := by
  classical
  obtain ⟨j₀, r, hr, hfactor⟩ := hu
  exact ⟨{
    lift := fun v ↦ v.π.app j₀ ≫ r
    fac := by
      intro v j
      obtain ⟨k, a, b, hab⟩ := hfactor j
      calc
        (v.π.app j₀ ≫ r) ≫ u.app j =
            (v.π.app k ≫ G.map a) ≫ r ≫ u.app j := by rw [v.w a, Category.assoc]
        _ = v.π.app k ≫ G.map b := by rw [Category.assoc, ← hab]
        _ = v.π.app j := v.w b
    uniq := by
      intro v m hm
      calc
        m = m ≫ (u.app j₀ ≫ r) := by rw [hr, Category.comp_id]
        _ = v.π.app j₀ ≫ r := by rw [← Category.assoc, hm j₀] }⟩

/-- In Situation 05S8, the left derived functor is defined at the two ends of every
morphism in the multiplicative system simultaneously, and its induced map is an isomorphism.

Source: Stacks Project, Derived Categories, Lemma 05SB(2)
(blueprint: lem-pur-derived-functor-inverts-05sb).

Proof: (1) Write `J_X = S/X` and `J_Y = S/Y`. For `s : X ⟶ Y` in `S`, MS1
of `def-pur-saturated-triangulated-localization` gives the postcomposition functor
`c : J_X ⥤ J_Y`, sending `u` to `u ≫ s`; restricting the `J_Y` pro-diagram along
`c` gives the `J_X` pro-diagram. The second MS2 clause gives, for every denominator
`t : Z ⟶ Y`, a denominator `u : W ⟶ X` and a map `v : W ⟶ Z` with
`u ≫ s = v ≫ t`, hence an arrow `c(u) ⟶ t`. For two such arrows, cofilteredness
of `J_X` gives a common source; the second MS3 clause applied to `t` then gives
an earlier denominator on which their maps to `Z` agree. Thus `c` is initial.
Stacks Categories Lemma 0A1T transfers essential constancy in both directions,
proving the iff of definedness.
(2) When both values exist, `lem-pur-derived-functor-morphisms-05sa`, rendered by
`leftDerived_value_morphism`, gives the unique compatible map `LF(s)`. For each
`Y' ⟶ Y` in `S`, the reverse MS2 comparison gives `X' ⟶ X` in `S` and a map
`X' ⟶ Y'` forming a denominator square. Applying `F` and the cone maps constructs
an inverse comparison `LF(Y) ⟶ LF(X)`. MS3 makes the construction independent
of the square. After a common refinement, MS3 makes both composites satisfy the
identity comparison equations. The uniqueness clause of 05SA(2) identifies them
with the two identity maps, so `LF(s)` is an isomorphism. -/
theorem leftDerived_inverts
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    {X Y : C} (s : X ⟶ Y) (hs : S s) :
    (F.IsTriangulatedLeftDerivedDefinedAt S hS X ↔
      F.IsTriangulatedLeftDerivedDefinedAt S hS Y) ∧
      (F.IsTriangulatedLeftDerivedDefinedAt S hS X →
        ∀ (LX LY : D),
          F.IsTriangulatedLeftDerivedValue S hS X LX →
          F.IsTriangulatedLeftDerivedValue S hS Y LY →
          ∀ (uX : (Functor.const (S.Over ⊤ X)).obj LX ⟶
              MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
            (uY : (Functor.const (S.Over ⊤ Y)).obj LY ⟶
              MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F),
            (∃ s₀ : S.Over ⊤ X, ∃ r : F.obj s₀.left ⟶ LX,
              uX.app s₀ ≫ r = 𝟙 LX ∧
                ∀ t : S.Over ⊤ X, ∃ q : S.Over ⊤ X, ∃ a : q ⟶ s₀,
                  ∃ b : q ⟶ t, F.map b.left = F.map a.left ≫ r ≫ uX.app t) →
            (∃ s₀ : S.Over ⊤ Y, ∃ r : F.obj s₀.left ⟶ LY,
              uY.app s₀ ≫ r = 𝟙 LY ∧
                ∀ t : S.Over ⊤ Y, ∃ q : S.Over ⊤ Y, ∃ a : q ⟶ s₀,
                  ∃ b : q ⟶ t, F.map b.left = F.map a.left ≫ r ≫ uY.app t) →
            ∃ (lf : LX ⟶ LY),
              (∀ (a : S.Over ⊤ X) (b : S.Over ⊤ Y)
                  (f : a.left ⟶ b.left),
                  a.hom ≫ s = f ≫ b.hom →
                    uX.app a ≫ F.map f = lf ≫ uY.app b ∧
                      (uX.app a ≫ F.map a.hom) ≫ F.map s =
                        lf ≫ uY.app b ≫ F.map b.hom) ∧
                IsIso lf) := by
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let := denominator_cofiltered S X
  let := denominator_cofiltered S Y
  let c := denominatorPostcompose S s hs
  let : c.Initial := denominatorPostcompose_initial S s hs
  let GX := MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F
  let GY := MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F
  have heq : c ⋙ GY = GX := by rfl
  have hvalue (L : D) : F.IsTriangulatedLeftDerivedValue S hS X L ↔
      F.IsTriangulatedLeftDerivedValue S hS Y L := by
    have h := (initial_iff_essentiallyConstantProDiagram c GY L).1
    rw [heq] at h
    exact h.symm
  constructor
  · exact ⟨fun ⟨L, hL⟩ ↦ ⟨L, (hvalue L).mp hL⟩,
      fun ⟨L, hL⟩ ↦ ⟨L, (hvalue L).mpr hL⟩⟩
  · intro _ LX LY _ _ uX uY huX huY
    obtain ⟨hX⟩ := proConeIsLimit GX LX uX huX
    obtain ⟨hY⟩ := proConeIsLimit GY LY uY huY
    let hYr := (Functor.Initial.isLimitWhiskerEquiv c (Cone.mk LY uY)).symm hY
    let e := hX.conePointUniqueUpToIso hYr
    refine ⟨e.hom, ?_, inferInstance⟩
    intro a b f hf
    have hleg := hX.conePointUniqueUpToIso_hom_comp hYr a
    change e.hom ≫ uY.app (c.obj a) = uX.app a at hleg
    let g : c.obj a ⟶ b := MorphismProperty.Over.homMk f hf.symm
    have hn := uY.naturality g
    change 𝟙 LY ≫ uY.app b = uY.app (c.obj a) ≫ F.map f at hn
    rw [Category.id_comp] at hn
    have hfirst : uX.app a ≫ F.map f = e.hom ≫ uY.app b := by
      rw [hn, ← Category.assoc, hleg]
    refine ⟨hfirst, ?_⟩
    calc
      (uX.app a ≫ F.map a.hom) ≫ F.map s = uX.app a ≫ F.map (a.hom ≫ s) := by
        rw [F.map_comp, Category.assoc]
      _ = uX.app a ≫ F.map (f ≫ b.hom) := by rw [hf]
      _ = e.hom ≫ uY.app b ≫ F.map b.hom := by
        rw [F.map_comp, ← Category.assoc, hfirst, Category.assoc]

end CategoryTheory.Functor
