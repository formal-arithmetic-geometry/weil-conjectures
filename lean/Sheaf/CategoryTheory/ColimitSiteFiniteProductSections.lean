/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.ColimitSiteScalarSectionComparison
import Mathlib.CategoryTheory.Filtered.Final
import Sheaf.CategoryTheory.ColimitSiteSections

/-! # Finite products of sections on a filtered colimit of sites

Source: Stacks Project, Sites, Tags 09YM and 09YN; Cohomology on Sites, Tag 09YP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_precomp {C : Type*} [Category C] {W X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} (h : Arrow.mk f = Arrow.mk g) (p : W ⟶ X) :
    Arrow.mk (p ≫ f) = Arrow.mk (p ≫ g) := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  apply (Arrow.mk_eq_mk_iff _ _).mpr
  exact ⟨rfl, hY, by simp [hf, Category.assoc]⟩

private theorem arrow_factors {C : Type*} [Category C] {W X Y Z : C}
    {f : W ⟶ Y} {p : W ⟶ X} {g : X ⟶ Z}
    (h : Arrow.mk f = Arrow.mk (p ≫ g)) :
    ∃ g' : X ⟶ Y, f = p ≫ g' := by
  obtain ⟨hW, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  exact ⟨g ≫ eqToHom hY.symm, by simpa [Category.assoc] using hf⟩

private theorem arrow_factors_three {C : Type*} [Category C] {U W X Y Z : C}
    {f : U ⟶ Y} {p : U ⟶ W} {q : W ⟶ X} {g : X ⟶ Z}
    (h : Arrow.mk f = Arrow.mk (p ≫ q ≫ g)) :
    ∃ g' : X ⟶ Y, f = (p ≫ q) ≫ g' := by
  exact arrow_factors (p := p ≫ q) (g := g) (by simpa only [Category.assoc] using h)

private def coordinateInclusion {A : Type u} [DecidableEq A]
    (B : A → AddCommGrpCat.{u}) (t : A) : B t ⟶ AddCommGrpCat.of (∀ t, B t) :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦ Pi.single (M := fun s ↦ ↥(B s)) t x
      map_zero' := by ext s; by_cases h : s = t <;> simp [h]
      map_add' := by
        intro x y
        ext s
        by_cases h : s = t
        · subst s; simp
        · simp [h] }

private theorem product_colimit_of_scalar
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {A : Type u} [Finite A] (D : I ⥤ AddCommGrpCat.{u}) (K : Cocone D)
    (B : I → A → AddCommGrpCat.{u}) (C : A → AddCommGrpCat.{u})
    (eD : ∀ a, D.obj a ≅ AddCommGrpCat.of (∀ t, B a t))
    (eK : K.pt ≅ AddCommGrpCat.of (∀ t, C t))
    (ρ : ∀ {a a'}, (a ⟶ a') → ∀ t, B a t ⟶ B a' t)
    (μ : ∀ a t, B a t ⟶ C t)
    (hρ : ∀ {a a'} (b : a ⟶ a') t,
      D.map b ≫ (eD a').hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ ρ b t)
    (hμ : ∀ a t,
      K.ι.app a ≫ eK.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ μ a t)
    (hsurj : ∀ (t : A) (x : C t), ∃ (a : I) (z : B a t), μ a t z = x)
    (hzero : ∀ (a : I) (t : A) (z : B a t), μ a t z = 0 →
      ∃ (a' : I) (b : a ⟶ a'), ρ b t z = 0) : Nonempty (IsColimit K) := by
  classical
  let := Fintype.ofFinite A
  let p := fun a t ↦ (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)
  let q := fun t ↦ eK.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)
  have hp (a : I) (x y : D.obj a) (h : ∀ t, p a t x = p a t y) : x = y := by
    apply (ConcreteCategory.isIso_iff_bijective (eD a).hom).mp inferInstance |>.1
    exact funext h
  have hq (x y : K.pt) (h : ∀ t, q t x = q t y) : x = y := by
    apply (ConcreteCategory.isIso_iff_bijective eK.hom).mp inferInstance |>.1
    exact funext h
  have hρ' {a a' : I} (b : a ⟶ a') (t : A) :
      D.map b ≫ p a' t = p a t ≫ ρ b t := hρ b t
  have hμ' (a : I) (t : A) : K.ι.app a ≫ q t = p a t ≫ μ a t := hμ a t
  have hμρ {a a' : I} (b : a ⟶ a') (t : A) (z : B a t) :
      μ a' t (ρ b t z) = μ a t z := by
    let inc := coordinateInclusion (B a) t ≫ (eD a).inv
    have hinc : inc ≫ p a t = 𝟙 _ := by
      dsimp [inc, p, coordinateInclusion]
      ext x
      simp
    have hw : p a t ≫ ρ b t ≫ μ a' t = p a t ≫ μ a t := by
      calc
        p a t ≫ ρ b t ≫ μ a' t = D.map b ≫ p a' t ≫ μ a' t := by
          rw [← Category.assoc, ← hρ', Category.assoc]
        _ = D.map b ≫ K.ι.app a' ≫ q t := by rw [← hμ']
        _ = K.ι.app a ≫ q t := by rw [← Category.assoc, K.w b]
        _ = p a t ≫ μ a t := hμ' a t
    have hh : ρ b t ≫ μ a' t = μ a t := by
      simpa only [← Category.assoc, hinc, Category.id_comp] using
        congrArg (fun f ↦ inc ≫ f) hw
    exact ConcreteCategory.congr_hom hh z
  let : ReflectsColimit D (forget AddCommGrpCat) :=
    reflectsColimit_of_reflectsIsomorphisms D (forget AddCommGrpCat)
  apply Nonempty.intro
  apply isColimitOfReflects (forget AddCommGrpCat)
  refine Types.FilteredColimit.isColimitOf' (D ⋙ forget _) ((forget _).mapCocone K) ?_ ?_
  · intro x
    choose a z hz using fun t ↦ hsurj t (q t x)
    obtain ⟨a', ha'⟩ := IsFiltered.sup_objs_exists (Finset.univ.image a)
    let b : ∀ t, a t ⟶ a' := fun t ↦ (ha' (Finset.mem_image_of_mem a (Finset.mem_univ t))).some
    let y : D.obj a' := (eD a').inv (fun t ↦ ρ (b t) t (z t))
    refine ⟨a', y, ?_⟩
    apply hq
    intro t
    change q t x = (K.ι.app a' ≫ q t) y
    rw [hμ']
    change q t x = μ a' t (p a' t y)
    have hy : p a' t y = ρ (b t) t (z t) := by simp [p, y]
    rw [hy, hμρ, hz]
  · intro a x y hxy
    change K.ι.app a x = K.ι.app a y at hxy
    have hz : ∀ t, μ a t (p a t (x - y)) = 0 := by
      intro t
      have ht := ConcreteCategory.congr_hom (hμ' a t) (x - y)
      change q t (K.ι.app a (x - y)) = μ a t (p a t (x - y)) at ht
      rw [← ht, map_sub, hxy, sub_self, map_zero]
    choose a' b hb using fun t ↦ hzero a t (p a t (x - y)) (hz t)
    obtain ⟨a'', f, g, hg⟩ := IsFiltered.wideSpan b
    refine ⟨a'', f, ?_⟩
    change D.map f x = D.map f y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hp a'' _ 0
    intro t
    rw [map_zero]
    change (D.map f ≫ p a'' t) (x - y) = 0
    rw [← hg t, D.map_comp, Category.assoc]
    rw [hρ', ← Category.assoc, hρ', Category.assoc]
    change ρ (g t) t (ρ (b t) t (p a t (x - y))) = 0
    rw [hb, map_zero]

private theorem scalar_laws_of_projections
    {I : Type u} [SmallCategory I] (D : I ⥤ AddCommGrpCat.{u}) (K : Cocone D)
    (B : I → AddCommGrpCat.{u}) (C : AddCommGrpCat.{u})
    (p : ∀ a, D.obj a ⟶ B a) (inc : ∀ a, B a ⟶ D.obj a) (q : K.pt ⟶ C)
    (hsplit : ∀ a, inc a ≫ p a = 𝟙 _)
    (ρ : ∀ {a a'}, (a ⟶ a') → (B a ⟶ B a')) (μ : ∀ a, B a ⟶ C)
    (hρ : ∀ {a a'} (b : a ⟶ a'), D.map b ≫ p a' = p a ≫ ρ b)
    (hμ : ∀ a, K.ι.app a ≫ q = p a ≫ μ a) :
    (∀ a, ρ (𝟙 a) = 𝟙 (B a)) ∧
    (∀ {a a' a''} (b : a ⟶ a') (b' : a' ⟶ a''), ρ (b ≫ b') = ρ b ≫ ρ b') ∧
    (∀ {a a'} (b : a ⟶ a'), ρ b ≫ μ a' = μ a) := by
  have cancel (a : I) {Z : AddCommGrpCat.{u}} (f g : B a ⟶ Z)
      (h : p a ≫ f = p a ≫ g) : f = g := by
    simpa only [← Category.assoc, hsplit, Category.id_comp] using
      congrArg (fun k ↦ inc a ≫ k) h
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply cancel a
    rw [← hρ, D.map_id, Category.id_comp, Category.comp_id]
  · intro a a' a'' b b'
    apply cancel a
    rw [← hρ, D.map_comp, Category.assoc, hρ, ← Category.assoc, hρ, Category.assoc]
  · intro a a' b
    apply cancel a
    rw [← Category.assoc, ← hρ, Category.assoc, ← hμ,
      ← Category.assoc, K.w b, hμ]

/-- Finite products of stage sections have their canonical colimit universal property.
Source: Stacks Project, Sites, Tags 09YM and 09YN; Cohomology on Sites, proof of
Tag 09YP, the finite-product step of the displayed Čech comparison.
(blueprint: lem-weil-pbc-colimit-site-finite-product-sections).

Proof: first fix one object X(t) of F.obj i. The section formula 09YM computes
sections of each inverse image H(j) as the filtered colimit over later-stage
presentations of that object. Insert these formulas into the sectionwise
colimit of H. The category of simultaneous refinements is filtered: finite
objects, arrows and their equalities lift to a common stage by hobjects and
harrows. Its diagonal refinement functor is final, giving the colimit over
Under i of G(a.right)(F(a.hom)(X(t))). Under this comparison the coprojections
are beta followed by c's coprojections, and transition maps are theta, by the
assumed compatibility and the adjunction-unit equations. Every Q-cover is the
image of a finite stage cover by hQ and hfinite. Filtered sheaf colimits are
therefore computed on sections: filtered colimits commute with their finite
sheaf equalizer diagrams (09YN, and the abelian version 03CO). Thus the scalar
section comparison is an isomorphism, compatibly with these exact maps.
Now A is finite, so filtered colimits of abelian groups commute with the product
over A. Apply the scalar comparison to every X(t). The stated projection
identities identify D and K, via eD and eK, with that finite product diagram and
its canonical cocone. Product projections jointly determine homomorphisms, so
this identification respects all transitions and coprojections. Transfer the
colimit universal property across these isomorphisms to obtain IsColimit K.
For A empty, both identified objects are zero and every cocone has its unique
mediating zero map; no nonempty-cover assumption is used. For a singleton A
this is exactly the scalar formula. The choices of X(t) need not be products
or belong to a covering. This theorem asserts only a universal property for
already supplied objects, never a construction from arbitrary existence.
-/
theorem colimitSite_finiteProduct_sections_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H), IsColimit c →
    ∀ (i : J) {A : Type u} [Finite A] (X : A → F.obj i)
      (D : Under i ⥤ AddCommGrpCat.{u})
      (eD : ∀ a : Under i, D.obj a ≅ AddCommGrpCat.of
        (∀ t : A, (G a.right).obj.obj (op ((F.map a.hom).toFunctor.obj (X t)))))
      (K : Cocone D)
      (eK : K.pt ≅ AddCommGrpCat.of
        (∀ t : A, c.pt.obj.obj (op ((V.ι.app i).toFunctor.obj (X t))))),
      (∀ (a a' : Under i) (b : a ⟶ a') (t : A),
        Arrow.mk ((eD a).inv ≫ D.map b ≫ (eD a').hom ≫
          AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
        Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
          (fun t ↦ (G a.right).obj.obj
            (op ((F.map a.hom).toFunctor.obj (X t)))) t) ≫
          (θ a.right a'.right b.right).app
            (op ((F.map a.hom).toFunctor.obj (X t))))) →
      (∀ (a : Under i) (t : A),
        Arrow.mk ((eD a).inv ≫ K.ι.app a ≫ eK.hom ≫
          AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
        Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
          (fun t ↦ (G a.right).obj.obj
            (op ((F.map a.hom).toFunctor.obj (X t)))) t) ≫
          β a.right ((F.map a.hom).toFunctor.obj (X t)) ≫
          (c.ι.app a.right).hom.app
            (op ((V.ι.app a.right).toFunctor.obj
              ((F.map a.hom).toFunctor.obj (X t)))))) →
      Nonempty (IsColimit K) := by
  classical
  dsimp only
  intro hβ c hc i A _ X D eD K eK hD hK
  let B := fun (a : Under i) (t : A) ↦
    (G a.right).obj.obj (op ((F.map a.hom).toFunctor.obj (X t)))
  let C := fun t : A ↦ c.pt.obj.obj (op ((V.ι.app i).toFunctor.obj (X t)))
  let p := fun (a : Under i) (t : A) ↦
    (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)
  let inc := fun (a : Under i) (t : A) ↦ coordinateInclusion (B a) t ≫ (eD a).inv
  let q := fun t : A ↦ eK.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)
  have hsplit (a : Under i) (t : A) : inc a t ≫ p a t = 𝟙 (B a t) := by
    dsimp [inc, p, coordinateInclusion, B]
    ext x
    simp
  have heval (a : Under i) (t : A) :
      coordinateInclusion (B a) t ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) = 𝟙 (B a t) := by
    dsimp [coordinateInclusion, B]
    ext x
    simp
  let ρ : ∀ {a a' : Under i}, (a ⟶ a') → ∀ t : A, B a t ⟶ B a' t :=
    fun {a} {a'} b t ↦ inc a t ≫ D.map b ≫ p a' t
  let μ := fun (a : Under i) (t : A) ↦ inc a t ≫ K.ι.app a ≫ q t
  have hρθ {a a' : Under i} (b : a ⟶ a') (t : A) :
      Arrow.mk (ρ b t) = Arrow.mk ((θ a.right a'.right b.right).app
        (op ((F.map a.hom).toFunctor.obj (X t)))) := by
    have hh := arrow_precomp (hD a a' b t) (coordinateInclusion (B a) t)
    simpa only [ρ, inc, p, B, Category.assoc, (reassoc_of% (heval a t)),
      Category.id_comp] using hh
  have hμβ (a : Under i) (t : A) :=
    arrow_precomp (hK a t) (coordinateInclusion (B a) t)
  simp only [Category.assoc, B, (reassoc_of% (heval _ _))] at hμβ
  have hρ {a a' : Under i} (b : a ⟶ a') (t : A) :
      D.map b ≫ p a' t = p a t ≫ ρ b t := by
    have hh := arrow_precomp (hD a a' b t) (eD a).hom
    simp only [Iso.hom_inv_id_assoc] at hh
    obtain ⟨g, hg⟩ := arrow_factors_three hh
    change D.map b ≫ p a' t = p a t ≫ inc a t ≫ D.map b ≫ p a' t
    change D.map b ≫ p a' t = p a t ≫ g at hg
    rw [hg]
    rw [← Category.assoc (inc a t) (p a t) g, hsplit, Category.id_comp]
  have hμ (a : Under i) (t : A) : K.ι.app a ≫ q t = p a t ≫ μ a t := by
    have hh := arrow_precomp (hK a t) (eD a).hom
    simp only [Iso.hom_inv_id_assoc] at hh
    obtain ⟨g, hg⟩ := arrow_factors_three hh
    change K.ι.app a ≫ q t = p a t ≫ inc a t ≫ K.ι.app a ≫ q t
    change K.ι.app a ≫ q t = p a t ≫ g at hg
    rw [hg]
    rw [← Category.assoc (inc a t) (p a t) g, hsplit, Category.id_comp]
  have hs (t : A) := scalar_laws_of_projections D K (fun a ↦ B a t) (C t)
    (fun a ↦ p a t) (fun a ↦ inc a t) (q t) (fun a ↦ hsplit a t)
    (fun b ↦ ρ b t) (fun a ↦ μ a t) (fun b ↦ hρ b t) (fun a ↦ hμ a t)
  have hscalar (t : A) := colimitSite_scalar_sections_representatives_and_zero
    F P hfinite hcover hpullback V hobjects harrows Q hQ G θ H E hβ c hc i (X t)
    (fun b ↦ ρ b t) (fun a ↦ μ a t) (hs t).1 (hs t).2.1 (hs t).2.2
    (fun b ↦ hρθ b t) (fun a ↦ hμβ a t)
  exact product_colimit_of_scalar D K B C eD eK ρ μ hρ hμ
    (fun t ↦ (hscalar t).1) (fun a t ↦ (hscalar t).2 a)


end CategoryTheory
