/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Category.Cat
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.CategoryTheory.SiteSystemStrictificationCategory
import Sheaf.CategoryTheory.SiteSystemFiniteSheafTransport
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Finset.Order

/-!
# The finite colimit construction for coherent affine étale sites

Source: Stacks Project, Categories 004A; Sites 0A34 and 09YL; Étale Cohomology 0EYL.
(blueprint: lem-weil-pbc-affine-etale-finite-colimit-construction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem finite_covering_family_iso
    {A : Type (u + 1)} [Category.{u} A] (Q : Precoverage A)
    [Q.IsStableUnderFiniteBaseChange] {n : ℕ}
    {X Y : A} (t : X ≅ Y) {B B' : Fin n → A} (s : ∀ a, B a ≅ B' a)
    (f : ∀ a, B a ⟶ X) (g : ∀ a, B' a ⟶ Y)
    (hf : Presieve.ofArrows B f ∈ Q X)
    (h : ∀ a, f a ≫ t.hom = (s a).hom ≫ g a) :
    Presieve.ofArrows B' g ∈ Q Y := by
  have hf' : Presieve.ofArrows (fun a : ULift.{u + 1} (Fin n) ↦ B a.down)
      (fun a ↦ f a.down) ∈ Q X := by
    exact (Presieve.ofArrows_comp_eq_of_surjective f
      (a := fun a : ULift.{u + 1} (Fin n) ↦ a.down) ULift.down_surjective).symm ▸ hf
  have hc := Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
    (J := Q) (fun a : ULift.{u + 1} (Fin n) ↦ f a.down) hf' t.inv
    (fun a ↦ g a.down) (fun a ↦ (s a.down).inv) (fun a ↦
      IsPullback.of_vert_isIso ⟨by
        apply (cancel_mono t.hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [h a.down]
        simp⟩)
  exact (Presieve.ofArrows_comp_eq_of_surjective g
    (a := fun a : ULift.{u + 1} (Fin n) ↦ a.down) ULift.down_surjective) ▸ hc
namespace PresentationPairs

open CategoryTheory.SiteSystemPairs
variable {I : Type u} [Preorder I] (C : I → Cat.{u, u + 1})
  (U : ∀ i j, i ≤ j → C i ⥤ C j)
  (gamma : ∀ i j k (h : i ≤ j) (h' : j ≤ k), U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
  (T : Type (u + 1)) [Category.{u} T] (v : ∀ i, C i ⥤ T)
  (delta : ∀ i j (h : i ≤ j), U i j h ⋙ v j ≅ v i)
private abbrev Label := Σ i, C i
private abbrev LimitCategory := InducedCategory T (fun X : Label C ↦ (v X.1).obj X.2)
private def toLimit (i : I) : Fiber C U i ⥤ LimitCategory C T v where
  obj X := ⟨X.stage, X.obj⟩
  map f := InducedCategory.homMk ((coefficients C U T v delta i).map f)
  map_id X := by apply InducedCategory.hom_ext; exact (coefficients C U T v delta i).map_id X
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (coefficients C U T v delta i).map_comp f g
private abbrev toTarget : LimitCategory C T v ⥤ T := inducedFunctor _
private theorem toLimit_target (i : I) :
    toLimit C U T v delta i ⋙ toTarget C T v = coefficients C U T v delta i := rfl
variable (hdelta : ∀ i j k (h : i ≤ j) (h' : j ≤ k) (A : C i),
  (v k).map ((gamma i j k h h').hom.app A) ≫ (delta i k (h.trans h')).hom.app A =
    (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A)
include hdelta in
private theorem toLimit_compatible (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ toLimit C U T v delta j =
      toLimit C U T v delta i := by
  refine Functor.hext (fun X ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  apply InducedCategory.hom_ext
  change (coefficients C U T v delta j).map ((transition C U gamma i j h).map f) =
    (coefficients C U T v delta i).map f
  simpa using Functor.congr_hom
    (transition_coefficients C U gamma T v delta hdelta i j h) f
include hdelta in
private theorem coefficient_transition_map (i j : I) (h : i ≤ j)
    {X Y : Fiber C U i} (f : X ⟶ Y) :
    (coefficients C U T v delta j).map ((transition C U gamma i j h).map f) =
      (coefficients C U T v delta i).map f := by
  simpa using Functor.congr_hom
    (transition_coefficients C U gamma T v delta hdelta i j h) f
include hdelta in
private theorem pair_arrow_descent
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (i : I) (X Y : Fiber C U i)
    (f : (coefficients C U T v delta i).obj X ⟶
      (coefficients C U T v delta i).obj Y) :
    ∃ (j : I) (h : i ≤ j) (g : (transition C U gamma i j h).obj X ⟶
      (transition C U gamma i j h).obj Y),
      (coefficients C U T v delta j).map g = f := by
  change (v X.stage).obj X.obj ⟶ (v Y.stage).obj Y.obj at f
  obtain ⟨j, h, g, hg⟩ := hd i (evalObj C U i X) (evalObj C U i Y)
    ((delta X.stage i X.le).hom.app X.obj ≫ f ≫ (delta Y.stage i Y.le).inv.app Y.obj)
  refine ⟨j, h, InducedCategory.homMk
    ((gamma X.stage i j X.le h).inv.app X.obj ≫ g ≫
      (gamma Y.stage i j Y.le h).hom.app Y.obj), ?_⟩
  change (delta X.stage j (X.le.trans h)).inv.app X.obj ≫
    (v j).map ((gamma X.stage i j X.le h).inv.app X.obj ≫ g ≫
      (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
    (delta Y.stage j (Y.le.trans h)).hom.app Y.obj = f
  apply (cancel_epi ((v j).map ((gamma X.stage i j X.le h).hom.app X.obj) ≫
    (delta X.stage j (X.le.trans h)).hom.app X.obj)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [← Category.assoc ((v j).map ((gamma X.stage i j X.le h).hom.app X.obj)),
    hdelta X.stage i j X.le h X.obj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [hdelta Y.stage i j Y.le h Y.obj]
  have hh := congrArg (fun z ↦ (delta i j h).hom.app (evalObj C U i X) ≫ z ≫
    (delta Y.stage i Y.le).hom.app Y.obj) hg
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id] using hh.symm
private theorem pair_arrow_equality
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (i : I) (X Y : Fiber C U i) (f g : X ⟶ Y)
    (h : (coefficients C U T v delta i).map f =
      (coefficients C U T v delta i).map g) :
    ∃ (j : I) (h : i ≤ j), (transition C U gamma i j h).map f =
      (transition C U gamma i j h).map g := by
  have h' : (v i).map f.hom = (v i).map g.hom := by
    apply (cancel_mono ((delta Y.stage i Y.le).hom.app Y.obj)).mp
    apply (cancel_epi ((delta X.stage i X.le).inv.app X.obj)).mp
    exact h
  obtain ⟨j, h, hh⟩ := he i (evalObj C U i X) (evalObj C U i Y) f.hom g.hom h'
  refine ⟨j, h, ?_⟩
  apply InducedCategory.hom_ext
  change (gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
    (gamma Y.stage i j Y.le h).hom.app Y.obj =
    (gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map g.hom ≫
    (gamma Y.stage i j Y.le h).hom.app Y.obj
  rw [hh]
variable [Nonempty I] [IsDirected I (· ≤ ·)]
include hdelta in
private theorem finite_pair_arrow_descent
    {E : Type w} [Finite E]
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (i : I) (X Y : E → Fiber C U i)
    (f : ∀ a, (coefficients C U T v delta i).obj (X a) ⟶
      (coefficients C U T v delta i).obj (Y a)) :
    ∃ (j : I) (h : i ≤ j) (g : ∀ a, (transition C U gamma i j h).obj (X a) ⟶
      (transition C U gamma i j h).obj (Y a)),
      ∀ a, (coefficients C U T v delta j).map (g a) = f a := by
  classical
  let := Fintype.ofFinite E
  choose j hij g hg using fun a ↦ pair_arrow_descent C U gamma T v delta hdelta hd i
    (X a) (Y a) (f a)
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (a : E) : j a ≤ k := hk (j a) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  refine ⟨k, hik, fun a ↦ (transition C U gamma (j a) k (hjk a)).map (g a), ?_⟩
  intro a
  have h := Functor.congr_hom
    (transition_coefficients C U gamma T v delta hdelta (j a) k (hjk a)) (g a)
  simpa using h.trans (by simpa using hg a)
variable (hUid : ∀ i, U i i le_rfl = 𝟭 (C i))
  (hgammaRight : ∀ i k (h : i ≤ k),
    HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
  (hgamma : ∀ i j k l (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (A : C i),
    (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
      (gamma i j l h (h'.trans h'')).hom.app A =
    (U k l h'').map ((gamma i j k h h').hom.app A) ≫
      (gamma i k l (h.trans h') h'').hom.app A)
include hgamma in
private theorem finite_pair_arrow_equality
    {E : Type w} [Finite E]
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (i : I) (X Y : E → Fiber C U i) (f g : ∀ a, X a ⟶ Y a)
    (h : ∀ a, (coefficients C U T v delta i).map (f a) =
      (coefficients C U T v delta i).map (g a)) :
    ∃ (j : I) (h : i ≤ j), ∀ a, (transition C U gamma i j h).map (f a) =
      (transition C U gamma i j h).map (g a) := by
  classical
  let := Fintype.ofFinite E
  choose j hij hj using fun a ↦ pair_arrow_equality C U gamma T v delta he i
    (X a) (Y a) (f a) (g a) (h a)
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (a : E) : j a ≤ k := hk (j a) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  refine ⟨k, hik, fun a ↦ ?_⟩
  have hf := Functor.congr_hom
    (transition_comp C U gamma hgamma i (j a) k (hij a) (hjk a)) (f a)
  have hg := Functor.congr_hom
    (transition_comp C U gamma hgamma i (j a) k (hij a) (hjk a)) (g a)
  have hh := congrArg (fun z ↦ (transition C U gamma (j a) k (hjk a)).map z) (hj a)
  simpa using hf.symm.trans (hh.trans hg)
include hdelta hgamma in
private theorem pair_iso_descent
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (i : I) (X Y : Fiber C U i)
    (f : (coefficients C U T v delta i).obj X ≅
      (coefficients C U T v delta i).obj Y) :
    ∃ (j : I) (h : i ≤ j) (g : (transition C U gamma i j h).obj X ≅
      (transition C U gamma i j h).obj Y),
      (coefficients C U T v delta j).map g.hom = f.hom := by
  obtain ⟨j, hij, g, hg⟩ := pair_arrow_descent C U gamma T v delta hdelta hd i X Y f.hom
  obtain ⟨k, hjk, g', hg'⟩ := pair_arrow_descent C U gamma T v delta hdelta hd j
    ((transition C U gamma i j hij).obj Y) ((transition C U gamma i j hij).obj X) f.inv
  let Xk := (transition C U gamma i k (hij.trans hjk)).obj X
  let Yk := (transition C U gamma i k (hij.trans hjk)).obj Y
  change Yk ⟶ Xk at g'
  let gk : Xk ⟶ Yk := (transition C U gamma j k hjk).map g
  have hgk : (coefficients C U T v delta k).map gk = f.hom := by
    have h := Functor.congr_hom (transition_coefficients C U gamma T v delta hdelta j k hjk) g
    simpa using h.trans (by simpa using hg)
  let Z : Bool → Fiber C U k := fun b ↦ if b then Yk else Xk
  let fs : ∀ b, Z b ⟶ Z b := fun b ↦ by
    cases b
    · exact gk ≫ g'
    · exact g' ≫ gk
  have hfs : ∀ b, (coefficients C U T v delta k).map (fs b) =
      (coefficients C U T v delta k).map (𝟙 (Z b)) := by
    intro b
    rw [(coefficients C U T v delta k).map_id]
    cases b <;> simp only [fs, Functor.map_comp, hgk, hg',
      Iso.hom_inv_id, Iso.inv_hom_id]
  obtain ⟨l, hkl, hl⟩ := finite_pair_arrow_equality C U gamma T v delta hgamma he k
    Z Z fs (fun b ↦ 𝟙 (Z b)) hfs
  let gl := (transition C U gamma k l hkl).map gk
  let gil := (transition C U gamma k l hkl).map g'
  have hgl : gl ≫ gil = 𝟙 _ := by
    have hh := hl false
    change (transition C U gamma k l hkl).map (gk ≫ g') =
      (transition C U gamma k l hkl).map (𝟙 Xk) at hh
    rw [(transition C U gamma k l hkl).map_id] at hh
    simpa only [Functor.map_comp] using hh
  have hgil : gil ≫ gl = 𝟙 _ := by
    have hh := hl true
    change (transition C U gamma k l hkl).map (g' ≫ gk) =
      (transition C U gamma k l hkl).map (𝟙 Yk) at hh
    rw [(transition C U gamma k l hkl).map_id] at hh
    simpa only [Functor.map_comp] using hh
  refine ⟨l, hij.trans (hjk.trans hkl), ⟨gl, gil, hgl, hgil⟩, ?_⟩
  have h := Functor.congr_hom (transition_coefficients C U gamma T v delta hdelta k l hkl) gk
  simpa using h.trans (by simpa using hgk)
include hdelta hgamma in
private theorem finite_pair_iso_descent
    {E : Type w} [Finite E]
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (i : I) (X Y : E → Fiber C U i)
    (f : ∀ a, (coefficients C U T v delta i).obj (X a) ≅
      (coefficients C U T v delta i).obj (Y a)) :
    ∃ (j : I) (h : i ≤ j) (g : ∀ a, (transition C U gamma i j h).obj (X a) ≅
      (transition C U gamma i j h).obj (Y a)),
      ∀ a, (coefficients C U T v delta j).map (g a).hom = (f a).hom := by
  classical
  let := Fintype.ofFinite E
  choose j hij g hg using fun a ↦ pair_iso_descent C U gamma T v delta hdelta hgamma hd he i
    (X a) (Y a) (f a)
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (a : E) : j a ≤ k := hk (j a) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  refine ⟨k, hik, fun a ↦ (transition C U gamma (j a) k (hjk a)).mapIso (g a), ?_⟩
  intro a
  have h := Functor.congr_hom
    (transition_coefficients C U gamma T v delta hdelta (j a) k (hjk a)) (g a).hom
  simpa using h.trans (by simpa using hg a)
include hdelta hgamma in
private theorem pair_cover_eventually
    (Q : ∀ i, Precoverage (Fiber C U i))
    [∀ i, (Q i).IsStableUnderFiniteBaseChange]
    (P : Precoverage T)
    (hcover : ∀ i j (h : i ≤ j) (X : Fiber C U i) (R : Presieve X),
      R ∈ Q i X → R.map (transition C U gamma i j h) ∈
        Q j ((transition C U gamma i j h).obj X))
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (hdesc : ∀ (n : ℕ) (A : T) (B : Fin n → T) (f : ∀ a, B a ⟶ A),
      Presieve.ofArrows B f ∈ P A →
        ∃ (i : I) (Ai : Fiber C U i) (Bi : Fin n → Fiber C U i) (fi : ∀ a, Bi a ⟶ Ai)
          (t : (coefficients C U T v delta i).obj Ai ≅ A)
          (s : ∀ a, (coefficients C U T v delta i).obj (Bi a) ≅ B a),
          Presieve.ofArrows Bi fi ∈ Q i Ai ∧
            ∀ a, (coefficients C U T v delta i).map (fi a) ≫ t.hom = (s a).hom ≫ f a)
    (i : I) (n : ℕ) (X : Fiber C U i) (Y : Fin n → Fiber C U i) (g : ∀ a, Y a ⟶ X)
    (hg : (Presieve.ofArrows Y g).map (coefficients C U T v delta i) ∈
      P ((coefficients C U T v delta i).obj X)) :
    ∃ (j : I) (h : i ≤ j),
      (Presieve.ofArrows Y g).map (transition C U gamma i j h) ∈
        Q j ((transition C U gamma i j h).obj X) := by
  rw [Presieve.map_ofArrows] at hg
  obtain ⟨j, Aj, Bj, fj, t, s, hc, hcomm⟩ := hdesc n _ _ _ hg
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let Ti := transition C U gamma i k hik
  let Tj := transition C U gamma j k hjk
  let A : Option (Fin n) → Fiber C U k
    | none => Tj.obj Aj
    | some a => Tj.obj (Bj a)
  let B : Option (Fin n) → Fiber C U k
    | none => Ti.obj X
    | some a => Ti.obj (Y a)
  let e : ∀ a, (coefficients C U T v delta k).obj (A a) ≅
      (coefficients C U T v delta k).obj (B a)
    | none => t
    | some a => s a
  obtain ⟨l, hkl, r, hr⟩ := finite_pair_iso_descent C U gamma T v delta hdelta hgamma hd he
    k A B e
  let Tkl := transition C U gamma k l hkl
  let f' : ∀ a, Tkl.obj (Tj.obj (Bj a)) ⟶ Tkl.obj (Tj.obj Aj) :=
    fun a ↦ Tkl.map (Tj.map (fj a))
  let g' : ∀ a, Tkl.obj (Ti.obj (Y a)) ⟶ Tkl.obj (Ti.obj X) :=
    fun a ↦ Tkl.map (Ti.map (g a))
  let t' : Tkl.obj (Tj.obj Aj) ≅ Tkl.obj (Ti.obj X) := r none
  let s' (a : Fin n) : Tkl.obj (Tj.obj (Bj a)) ≅ Tkl.obj (Ti.obj (Y a)) := r (some a)
  have hc' : Presieve.ofArrows (fun a ↦ Tkl.obj (Tj.obj (Bj a))) f' ∈
      Q l (Tkl.obj (Tj.obj Aj)) := by
    have h := hcover k l hkl _ _ (hcover j k hjk _ _ hc)
    simpa only [Presieve.map_ofArrows] using h
  have hrel (a : Fin n) :
      (coefficients C U T v delta l).map (f' a ≫ t'.hom) =
        (coefficients C U T v delta l).map ((s' a).hom ≫ g' a) := by
    simp only [Functor.map_comp]
    have ht : (coefficients C U T v delta l).map t'.hom = t.hom := hr none
    have hs : (coefficients C U T v delta l).map (s' a).hom = (s a).hom := hr (some a)
    rw [ht, hs]
    simpa only [f', g', Tkl, Ti, Tj,
      coefficient_transition_map C U gamma T v delta hdelta] using hcomm a
  obtain ⟨m, hlm, hm⟩ := finite_pair_arrow_equality C U gamma T v delta hgamma he l
    (fun a ↦ Tkl.obj (Tj.obj (Bj a))) (fun _ ↦ Tkl.obj (Ti.obj X))
    (fun a ↦ f' a ≫ t'.hom) (fun a ↦ (s' a).hom ≫ g' a) hrel
  let Tlm := transition C U gamma l m hlm
  have hc'' := hcover l m hlm _ _ hc'
  rw [Presieve.map_ofArrows] at hc''
  have hg' := finite_covering_family_iso (Q m) (Tlm.mapIso t')
    (fun a ↦ Tlm.mapIso (s' a)) (fun a ↦ Tlm.map (f' a)) (fun a ↦ Tlm.map (g' a)) hc''
    (fun a ↦ by
      change Tlm.map (f' a) ≫ Tlm.map t'.hom = Tlm.map (s' a).hom ≫ Tlm.map (g' a)
      simpa only [Functor.map_comp] using hm a)
  refine ⟨m, hik.trans (hkl.trans hlm), ?_⟩
  rw [Presieve.map_ofArrows]
  have htrans : Ti ⋙ Tkl ⋙ Tlm = transition C U gamma i m (hik.trans (hkl.trans hlm)) := by
    dsimp only [Ti, Tkl, Tlm]
    rw [transition_comp C U gamma hgamma k l m hkl hlm,
      transition_comp C U gamma hgamma i k m hik (hkl.trans hlm)]
  change Presieve.ofArrows (fun a ↦ (Ti ⋙ Tkl ⋙ Tlm).obj (Y a))
    (fun a ↦ (Ti ⋙ Tkl ⋙ Tlm).map (g a)) ∈ Q m ((Ti ⋙ Tkl ⋙ Tlm).obj X) at hg'
  rw [htrans] at hg'
  exact hg'

include hdelta hgamma in
private theorem finite_presieve_lift
    (Q : ∀ i, Precoverage (Fiber C U i))
    [∀ i, (Q i).IsStableUnderFiniteBaseChange]
    (P : Precoverage T)
    (hcover : ∀ i j (h : i ≤ j) (X : Fiber C U i) (R : Presieve X),
      R ∈ Q i X → R.map (transition C U gamma i j h) ∈
        Q j ((transition C U gamma i j h).obj X))
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (hdesc : ∀ (n : ℕ) (A : T) (B : Fin n → T) (f : ∀ a, B a ⟶ A),
      Presieve.ofArrows B f ∈ P A →
        ∃ (i : I) (Ai : Fiber C U i) (Bi : Fin n → Fiber C U i) (fi : ∀ a, Bi a ⟶ Ai)
          (t : (coefficients C U T v delta i).obj Ai ≅ A)
          (s : ∀ a, (coefficients C U T v delta i).obj (Bi a) ≅ B a),
          Presieve.ofArrows Bi fi ∈ Q i Ai ∧
            ∀ a, (coefficients C U T v delta i).map (fi a) ≫ t.hom = (s a).hom ≫ f a)
    (A : LimitCategory C T v) (R : Presieve A) (hfin : Finite R.uncurry)
    (hR : R.map (toTarget C T v) ∈ P ((toTarget C T v).obj A)) :
    ∃ (i : I) (Ai : Fiber C U i) (Ri : Presieve Ai)
      (h : (toLimit C U T v delta i).obj Ai = A),
      Ri ∈ Q i Ai ∧ h ▸ Ri.map (toLimit C U T v delta i) = R := by
  classical
  let := Fintype.ofFinite R.uncurry
  let e := Fintype.equivFin R.uncurry
  let n := Fintype.card R.uncurry
  let B : Fin n → LimitCategory C T v := fun a ↦ (e.symm a).val.1
  let f : ∀ a, B a ⟶ A := fun a ↦ (e.symm a).val.2
  have hEq : R = Presieve.ofArrows B f := by
    apply le_antisymm
    · intro Z g hg
      let a : R.uncurry := ⟨⟨Z, g⟩, hg⟩
      have h := Presieve.ofArrows.mk (f := f) (e a)
      change Presieve.ofArrows B f (e.symm (e a)).val.2 at h
      rw [e.symm_apply_apply] at h
      exact h
    · rintro Z g ⟨a⟩
      exact (e.symm a).property
  rw [hEq, Presieve.map_ofArrows] at hR
  obtain ⟨k, hk⟩ := Finset.exists_le (insert A.1 (Finset.univ.image (fun a ↦ (B a).1)))
  have hAk : A.1 ≤ k := hk A.1 (Finset.mem_insert_self _ _)
  have hBk (a : Fin n) : (B a).1 ≤ k := hk (B a).1 (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  let X : Fiber C U k := ⟨A.1, hAk, A.2⟩
  let Y : Fin n → Fiber C U k := fun a ↦ ⟨(B a).1, hBk a, (B a).2⟩
  obtain ⟨l, hkl, g, hg⟩ := finite_pair_arrow_descent C U gamma T v delta hdelta hd k Y
    (fun _ ↦ X) (fun a ↦ (f a).hom)
  let L := transition C U gamma k l hkl
  have hgcover : (Presieve.ofArrows (fun a ↦ L.obj (Y a)) g).map
      (coefficients C U T v delta l) ∈ P ((coefficients C U T v delta l).obj (L.obj X)) := by
    rw [Presieve.map_ofArrows]
    change Presieve.ofArrows (fun a ↦ (v (B a).1).obj (B a).2)
      (fun a ↦ (coefficients C U T v delta l).map (g a)) ∈ P ((v A.1).obj A.2)
    simp only [hg]
    exact hR
  obtain ⟨m, hlm, hm⟩ := pair_cover_eventually C U gamma T v delta hdelta hgamma
    Q P hcover hd he hdesc l n (L.obj X) (fun a ↦ L.obj (Y a)) g hgcover
  let M := transition C U gamma l m hlm
  let Z : Fiber C U m := M.obj (L.obj X)
  let V : Fin n → Fiber C U m := fun a ↦ M.obj (L.obj (Y a))
  let q := toLimit C U T v delta m
  have hf (a : Fin n) : q.map (M.map (g a)) = f a := by
    apply InducedCategory.hom_ext
    exact (coefficient_transition_map C U gamma T v delta hdelta l m hlm (g a)).trans (hg a)
  rw [Presieve.map_ofArrows] at hm
  refine ⟨m, Z, Presieve.ofArrows V (fun a ↦ M.map (g a)), rfl, hm, ?_⟩
  rw [Presieve.map_ofArrows, hEq]
  change Presieve.ofArrows B (fun a ↦ q.map (M.map (g a))) = Presieve.ofArrows B f
  simp only [hf]

include hdelta hgamma in
private theorem finite_precoverage_stage_images
    (Q : ∀ i, Precoverage (Fiber C U i))
    [∀ i, (Q i).IsStableUnderFiniteBaseChange]
    (P : Precoverage T)
    (hcover : ∀ i j (h : i ≤ j) (X : Fiber C U i) (R : Presieve X),
      R ∈ Q i X → R.map (transition C U gamma i j h) ∈
        Q j ((transition C U gamma i j h).obj X))
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (hdesc : ∀ (n : ℕ) (A : T) (B : Fin n → T) (f : ∀ a, B a ⟶ A),
      Presieve.ofArrows B f ∈ P A →
        ∃ (i : I) (Ai : Fiber C U i) (Bi : Fin n → Fiber C U i) (fi : ∀ a, Bi a ⟶ Ai)
          (t : (coefficients C U T v delta i).obj Ai ≅ A)
          (s : ∀ a, (coefficients C U T v delta i).obj (Bi a) ≅ B a),
          Presieve.ofArrows Bi fi ∈ Q i Ai ∧
            ∀ a, (coefficients C U T v delta i).map (fi a) ≫ t.hom = (s a).hom ≫ f a)
    (hQfinite : ∀ i (A : Fiber C U i) (R : Presieve A), R ∈ Q i A → Finite R.uncurry)
    (hcoeff : ∀ i (A : Fiber C U i) (R : Presieve A), R ∈ Q i A →
      R.map (coefficients C U T v delta i) ∈ P ((coefficients C U T v delta i).obj A))
    (A : LimitCategory C T v) (R : Presieve A) :
    R ∈ finiteEquivalencePrecoverage (toTarget C T v) P A ↔
      ∃ (i : I) (Ai : Fiber C U i) (Ri : Presieve Ai)
        (h : (toLimit C U T v delta i).obj Ai = A),
        Ri ∈ Q i Ai ∧ h ▸ Ri.map (toLimit C U T v delta i) = R := by
  constructor
  · intro hR
    exact finite_presieve_lift C U gamma T v delta hdelta hgamma Q P hcover hd he hdesc
      A R hR.1.to_subtype hR.2
  · rintro ⟨i, Ai, Ri, rfl, hRi, rfl⟩
    have hfin := hQfinite i Ai Ri hRi
    let := hfin
    have hEq : Ri = Presieve.ofArrows (fun a : Ri.uncurry ↦ a.val.1)
        (fun a ↦ a.val.2) := by
      apply le_antisymm
      · intro Z f hf
        exact Presieve.ofArrows.mk (⟨⟨Z, f⟩, hf⟩ : Ri.uncurry)
      · rintro Z f ⟨a⟩
        exact a.property
    refine ⟨?_, ?_⟩
    · rw [hEq, Presieve.map_ofArrows]
      exact Precoverage.ofArrows_mem_finite _ _
    · change Ri ∈ (P.comap (toTarget C T v)).comap (toLimit C U T v delta i) Ai
      rw [← Precoverage.comap_comp, toLimit_target]
      exact hcoeff i Ai Ri hRi

private def limitCocone : Cocone (diagram C U gamma hUid hgammaRight hgamma) where
  pt := Cat.of (LimitCategory C T v)
  ι :=
    { app := fun i ↦ (toLimit C U T v delta i).toCatHom
      naturality := fun i j f ↦ by
        apply Cat.ext
        exact toLimit_compatible C U gamma T v delta hdelta i j (leOfHom f) }
omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private theorem toLimit_obj_injective (i : I) :
    Function.Injective (toLimit C U T v delta i).obj := by
  intro X Y h
  cases X with
  | mk a ha A =>
    cases Y with
    | mk b hb B =>
      change (⟨a, A⟩ : Σ i, C i) = ⟨b, B⟩ at h
      cases h
      rfl
private noncomputable def limitCocone_objects_isColimit :
    IsColimit (Cat.objects.mapCocone
      (limitCocone C U gamma T v delta hdelta hUid hgammaRight hgamma)) := by
  apply Types.FilteredColimit.isColimitOf'
  · rintro ⟨i, A⟩
    exact ⟨i, ⟨i, le_rfl, A⟩, rfl⟩
  · intro i X Y h
    have : X = Y := toLimit_obj_injective C U T v delta i h
    subst Y
    exact ⟨i, 𝟙 i, rfl⟩
private noncomputable def limitCocone_arrows_isColimit
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g) :
    IsColimit (Cat.arrows.mapCocone
      (limitCocone C U gamma T v delta hdelta hUid hgammaRight hgamma)) := by
  apply Types.FilteredColimit.isColimitOf'
  · rintro ⟨⟨i, A⟩, ⟨j, B⟩, f⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let X : Fiber C U k := ⟨i, hik, A⟩
    let Y : Fiber C U k := ⟨j, hjk, B⟩
    obtain ⟨l, h, g, hg⟩ := pair_arrow_descent C U gamma T v delta hdelta hd k X Y f.hom
    refine ⟨l, Arrow.mk g, ?_⟩
    change Arrow.mk f = Arrow.mk ((toLimit C U T v delta l).map g)
    apply congrArg Arrow.mk
    apply InducedCategory.hom_ext
    exact hg.symm
  · rintro i ⟨X, Y, f⟩ ⟨X', Y', g⟩ h
    have hx : X = X' := toLimit_obj_injective C U T v delta i (congrArg Arrow.left h)
    have hy : Y = Y' := toLimit_obj_injective C U T v delta i (congrArg Arrow.right h)
    subst X'
    subst Y'
    have hh : (coefficients C U T v delta i).map f =
        (coefficients C U T v delta i).map g := by
      have hh := (Arrow.mk_injective _ _) h
      change (toLimit C U T v delta i).map f = (toLimit C U T v delta i).map g at hh
      have hhh := congrArg (fun a : (toLimit C U T v delta i).obj X ⟶
        (toLimit C U T v delta i).obj Y ↦ a.hom) hh
      exact hhh
    obtain ⟨j, h, hh⟩ := pair_arrow_equality C U gamma T v delta he i X Y f g hh
    exact ⟨j, homOfLE h, congrArg Arrow.mk hh⟩
omit [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] in
private theorem toTarget_isEquivalence
    (ho : ∀ A : T, ∃ (i : I) (Ai : C i), Nonempty ((v i).obj Ai ≅ A)) :
    (toTarget C T v).IsEquivalence := by
  have : (toTarget C T v).EssSurj := ⟨fun A ↦ by
    obtain ⟨i, Ai, ⟨e⟩⟩ := ho A
    exact ⟨⟨i, Ai⟩, ⟨e⟩⟩⟩
  exact { faithful := inferInstanceAs (inducedFunctor _).Faithful
          full := inferInstanceAs (inducedFunctor _).Full
          essSurj := this }
include hdelta hgamma in
private theorem exists_pairs_finite_colimit_site
    (Q : ∀ i, Precoverage (Fiber C U i))
    [∀ i, (Q i).IsStableUnderFiniteBaseChange]
    (P : Precoverage T) [P.HasIsos] [P.IsStableUnderFiniteComposition]
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (ho : ∀ A : T, ∃ (i : I) (Ai : C i), Nonempty ((v i).obj Ai ≅ A))
    (hcover : ∀ i j (h : i ≤ j) (X : Fiber C U i) (R : Presieve X),
      R ∈ Q i X → R.map (transition C U gamma i j h) ∈
        Q j ((transition C U gamma i j h).obj X))
    (hd : ∀ i (A B : C i) (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B)
    (he : ∀ i (A B : C i) (f g : A ⟶ B), (v i).map f = (v i).map g →
      ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g)
    (hdesc : ∀ (n : ℕ) (A : T) (B : Fin n → T) (f : ∀ a, B a ⟶ A),
      Presieve.ofArrows B f ∈ P A →
        ∃ (i : I) (Ai : Fiber C U i) (Bi : Fin n → Fiber C U i) (fi : ∀ a, Bi a ⟶ Ai)
          (t : (coefficients C U T v delta i).obj Ai ≅ A)
          (s : ∀ a, (coefficients C U T v delta i).obj (Bi a) ≅ B a),
          Presieve.ofArrows Bi fi ∈ Q i Ai ∧
            ∀ a, (coefficients C U T v delta i).map (fi a) ≫ t.hom = (s a).hom ≫ f a)
    (hQfinite : ∀ i (A : Fiber C U i) (R : Presieve A), R ∈ Q i A → Finite R.uncurry)
    (hcoeff : ∀ i (A : Fiber C U i) (R : Presieve A), R ∈ Q i A →
      R.map (coefficients C U T v delta i) ∈ P ((coefficients C U T v delta i).obj A))
    : ∃ (K : Cocone (diagram C U gamma hUid hgammaRight hgamma))
      (W : K.pt ⥤ T) (P' : Precoverage K.pt),
      W.IsEquivalence ∧ Nonempty (IsColimit (Cat.objects.mapCocone K)) ∧
        Nonempty (IsColimit (Cat.arrows.mapCocone K)) ∧
        (∀ i, (K.ι.app i).toFunctor ⋙ W = coefficients C U T v delta i) ∧
        (∀ (A : K.pt) (R : Presieve A), R ∈ P' A ↔
          ∃ (i : I) (Ai : Fiber C U i) (Ri : Presieve Ai)
            (h : (K.ι.app i).toFunctor.obj Ai = A),
            Ri ∈ Q i Ai ∧ h ▸ Ri.map (K.ι.app i).toFunctor = R) ∧
        P'.HasIsos ∧ P'.IsStableUnderFiniteComposition ∧
        P'.IsStableUnderFiniteBaseChange ∧ P'.HasPullbacks ∧
        ∀ (A : K.pt) (R : Presieve A), R ∈ P' A ↔
          Finite R.uncurry ∧ R.map W ∈ P (W.obj A) := by
  let K := limitCocone C U gamma T v delta hdelta hUid hgammaRight hgamma
  let W := toTarget C T v
  have hW : W.IsEquivalence := toTarget_isEquivalence C T v ho
  let P' := finiteEquivalencePrecoverage W P
  refine ⟨K, W, P', hW,
    ⟨limitCocone_objects_isColimit C U gamma T v delta hdelta hUid hgammaRight hgamma⟩,
    ⟨limitCocone_arrows_isColimit C U gamma T v delta hdelta hUid hgammaRight hgamma hd he⟩,
    (fun _ ↦ rfl), ?_, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  · exact finite_precoverage_stage_images C U gamma T v delta hdelta hgamma Q P hcover hd he
      hdesc hQfinite hcoeff
  · intro A R
    constructor
    · intro hR
      exact ⟨hR.1.to_subtype, hR.2⟩
    · rintro ⟨hf, hR⟩
      let := hf
      exact ⟨Set.toFinite _, hR⟩
end PresentationPairs


private theorem affine_precoverage_eq (S : Scheme.{u}) :
    fullAffineEtalePrecoverage S = Precoverage.finite S.FullAffineEtale ⊓
      (Scheme.precoverage @Etale).comap
        (fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S) := by
  classical
  ext A R
  constructor
  · rintro ⟨n, B, f, rfl, hf, hsurj⟩
    refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
    change (Presieve.ofArrows B f).map _ ∈ Scheme.precoverage @Etale _
    rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hsurj, hf⟩
  · rintro ⟨hfin, hR⟩
    let := hfin.fintype
    let e := Fintype.equivFin R.uncurry
    let B : Fin (Fintype.card R.uncurry) → S.FullAffineEtale :=
      fun i ↦ (e.symm i).val.1
    let f : ∀ i, B i ⟶ A := fun i ↦ (e.symm i).val.2
    have heq : R = Presieve.ofArrows B f := by
      apply le_antisymm
      · intro Z g hg
        let a : R.uncurry := ⟨⟨Z, g⟩, hg⟩
        have h := Presieve.ofArrows.mk (f := f) (e a)
        change Presieve.ofArrows B f (e.symm (e a)).val.2 at h
        rw [e.symm_apply_apply] at h
        exact h
      · rintro Z g ⟨i⟩
        exact (e.symm i).property
    refine ⟨_, B, f, heq, fun _ ↦ inferInstance, ?_⟩
    rw [heq] at hR
    change (Presieve.ofArrows B f).map _ ∈ Scheme.precoverage @Etale _ at hR
    rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff] at hR
    exact hR.1

private theorem affine_precoverage_instances (S : Scheme.{u}) :
    (fullAffineEtalePrecoverage S).HasIsos ∧
    (fullAffineEtalePrecoverage S).IsStableUnderFiniteComposition ∧
    (fullAffineEtalePrecoverage S).IsStableUnderFiniteBaseChange ∧
    (fullAffineEtalePrecoverage S).HasPullbacks := by
  let T : ObjectProperty S.Etale := fun U ↦ IsAffine U.left
  have : T.IsClosedUnderLimitsOfShape WalkingCospan := ⟨by
    rintro X ⟨h⟩
    let G := Etale.forget S ⋙ Over.forget S
    have (j : WalkingCospan) : IsAffine ((h.diag ⋙ G).obj j) := h.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (G.mapCone h.toLimitPresentation.cone)
      (isLimitOfPreserves G h.isLimit)⟩
  let p := fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S
  have : PreservesLimitsOfShape WalkingCospan p := by
    change PreservesLimitsOfShape WalkingCospan (T.ι ⋙ Etale.forget S ⋙ Over.forget S)
    infer_instance
  let P := (Scheme.precoverage @Etale).comap p
  have hEq : fullAffineEtalePrecoverage S = finiteEquivalencePrecoverage (𝟭 _) P := by
    rw [affine_precoverage_eq]
    simp only [finiteEquivalencePrecoverage, Precoverage.comap_id]
    rfl
  rw [hEq]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem affine_precoverage_finite (S : Scheme.{u})
    (A : S.FullAffineEtale) (R : Presieve A)
    (hR : R ∈ fullAffineEtalePrecoverage S A) : Finite R.uncurry := by
  obtain ⟨n, B, f, rfl, _⟩ := hR
  exact (Precoverage.ofArrows_mem_finite B f).to_subtype

private theorem adjoint_of_continuous_equivalence
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (p : A ⥤ B) (e : B ⥤ A)
    (eta : 𝟭 A ≅ p ⋙ e) (epsilon : e ⋙ p ≅ 𝟭 B)
    [p.IsContinuous JA JB] [e.IsContinuous JB JA] :
    ∃ L : Sheaf JA (Type u) ⥤ Sheaf JB (Type u),
      Nonempty (L ⊣ p.sheafPushforwardContinuous (Type u) JA JB) ∧
        PreservesFiniteLimits L := by
  have : (e ⋙ p).IsContinuous JB JB := Functor.isContinuous_comp e p JB JA JB
  have : (p ⋙ e).IsContinuous JA JA := Functor.isContinuous_comp p e JA JB JA
  let ec := e.sheafPushforwardContinuousComp p (Type u) JB JA JB ≪≫
    Functor.sheafPushforwardContinuousId' epsilon (Type u) JB
  let ea := p.sheafPushforwardContinuousComp e (Type u) JA JB JA ≪≫
    Functor.sheafPushforwardContinuousId' eta.symm (Type u) JA
  have : (p.sheafPushforwardContinuous (Type u) JA JB).IsEquivalence :=
    Functor.IsEquivalence.mk' _ ec.symm ea
  exact ⟨(p.sheafPushforwardContinuous (Type u) JA JB).inv,
    ⟨(p.sheafPushforwardContinuous (Type u) JA JB).asEquivalence.symm.toAdjunction⟩,
    inferInstance⟩

private theorem adjoint_comp
    {A B C : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (p : A ⥤ B) (q : B ⥤ C)
    [p.IsContinuous JA JB] [q.IsContinuous JB JC]
    (hp : ∃ L : Sheaf JA (Type u) ⥤ Sheaf JB (Type u),
      Nonempty (L ⊣ p.sheafPushforwardContinuous (Type u) JA JB) ∧
        PreservesFiniteLimits L)
    (hq : ∃ L : Sheaf JB (Type u) ⥤ Sheaf JC (Type u),
      Nonempty (L ⊣ q.sheafPushforwardContinuous (Type u) JB JC) ∧
        PreservesFiniteLimits L) :
    letI := Functor.isContinuous_comp p q JA JB JC
    ∃ L : Sheaf JA (Type u) ⥤ Sheaf JC (Type u),
      Nonempty (L ⊣ (p ⋙ q).sheafPushforwardContinuous (Type u) JA JC) ∧
        PreservesFiniteLimits L := by
  let := Functor.isContinuous_comp p q JA JB JC
  obtain ⟨Lp, ⟨ap⟩, hlp⟩ := hp
  obtain ⟨Lq, ⟨aq⟩, hlq⟩ := hq
  exact ⟨Lp ⋙ Lq, ⟨(ap.comp aq).ofNatIsoRight
    (p.sheafPushforwardContinuousComp q (Type u) JA JB JC)⟩, inferInstance⟩

/-- Source: Stacks Project, Categories 004A; Sites 0A34 and 09YL;
Étale Cohomology 0EYL, the finite-family part of the affine-site construction.
(blueprint: lem-weil-pbc-affine-etale-finite-colimit-construction).

The normalized coherent data and the stated descent properties give the strict
finite site system, a categorical colimit, and exactly the colimit precoverage
of finite families. The last equivalence deliberately records `Finite R.uncurry`:
finite covering images under an equivalence need not have finite inverse images.

Proof:
1. Replace stage objects by pairs (j,A) with j ≤ i. Evaluation is an equivalence,
and the current-stage inclusion is a section. Gamma conjugates transition maps;
its normalization and cocycle make this a strict diagram. Delta defines strictly
compatible coefficient functors by conjugation on arrows.
2. Intersect the finite precoverage with the inverse image of the standard étale
precoverage. Finite composition and finite base change follow by mapping the
indexed families through evaluation. Transport covering and cospan-pullback
preservation through the comparison isomorphism.
3. The finite pairwise-pullback criterion gives continuity. Evaluation and its
section induce inverse pushforwards on Type u sheaves. Their inverse equivalences
supply left adjoints preserving finite limits. Compose these adjunctions with
the supplied stage adjoints, and transport along the coefficient comparisons.
4. For the colimit, retain global labels (j,A) and take homs in the target category.
Every label is represented at its own stage. Morphism descent gives every arrow
at a later stage, after conjugation by gamma and delta; eventual equality gives
the injectivity criterion for the filtered arrow colimit. Object descent makes
the induced fully faithful target functor essentially surjective.
5. To descend a finite covering, first descend it up to isomorphism using the
hypothesis. Descend the finitely many comparison isomorphisms and their inverses;
move their inverse equations and the covering square equations to a common stage
using eventual equality. Finite base change along the comparison isomorphisms
makes the original finite family a stage cover. This includes the empty family.
6. On the labelled colimit take finite presieves whose images in the target cover.
Its site axioms follow from the target finite axioms and the target equivalence.
Step 5 proves that these are exactly images of stage covers. This establishes
all asserted clauses without asserting reflection for infinite presieves. -/
theorem exists_affineEtale_finite_colimit_construction
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (h0 : (∀ i : I, U i i le_rfl = 𝟭 _))
    (h3 : (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h))))
    (h4 : (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))))
    (h5 : (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))))
    (h8 : (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
            (gamma i j l h (h'.trans h'')).hom.app A =
          (U k l h'').map ((gamma i j k h h').hom.app A) ≫
            (gamma i k l (h.trans h') h'').hom.app A))
    (h9 : (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (v k).map ((gamma i j k h h').hom.app A) ≫
            (delta i k (h.trans h')).hom.app A =
          (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A))
    (h10 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj A)))
    (h11 : (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (U i j h)))
    (h12 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (v i) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj A)))
    (h14 : (∃ (_ : ∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology (D.obj (op j))))
        (_ : ∀ i : I, (v i).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)),
        (∀ (i j : I) (h : i ≤ j), ∃ L :
            Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
              Sheaf (fullAffineEtaleTopology (D.obj (op j))) (Type u),
          Nonempty (L ⊣ (U i j h).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i)))
            (fullAffineEtaleTopology (D.obj (op j)))) ∧ PreservesFiniteLimits L) ∧
        (∀ i : I, ∃ L : Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
            Sheaf (fullAffineEtaleTopology c.pt) (Type u),
          Nonempty (L ⊣ (v i).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)) ∧
          PreservesFiniteLimits L)))
    (h15 : (∀ A : c.pt.FullAffineEtale,
        ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale), Nonempty ((v i).obj Ai ≅ A)))
    (h16 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale)
        (f : (v i).obj A ⟶ (v i).obj B),
        ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
          f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B))
    (h17 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale) (f g : A ⟶ B),
        (v i).map f = (v i).map g →
          ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g))
    (h18 : (∀ (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
        (f : ∀ a : Fin n, B a ⟶ A),
        Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage c.pt A ↔
          ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale)
            (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai)
            (t : (v i).obj Ai ≅ A) (s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a),
            Presieve.ofArrows Bi fi ∈ fullAffineEtalePrecoverage (D.obj (op i)) Ai ∧
              ∀ a : Fin n, (v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a))
    :
      ∃ (F : I ⥤ Cat.{u, u + 1}) (Q : ∀ i : I, Precoverage (F.obj i))
        (e : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ F.obj i)
        (v' : ∀ i : I, F.obj i ⥤ c.pt.FullAffineEtale)
        (theta : ∀ (i j : I) (h : i ≤ j),
          e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
        (eta : ∀ i : I, e i ⋙ v' i ≅ v i),
        (∀ i : I, (e i).IsEquivalence) ∧
        (∃ (K : Cocone F) (W : K.pt ⥤ c.pt.FullAffineEtale) (P : Precoverage K.pt),
          W.IsEquivalence ∧ Nonempty (IsColimit (Cat.objects.mapCocone K)) ∧
            Nonempty (IsColimit (Cat.arrows.mapCocone K)) ∧
            (∀ i, (K.ι.app i).toFunctor ⋙ W = v' i) ∧
            (∀ (A : K.pt) (R : Presieve A), R ∈ P A ↔
              ∃ (i : I) (Ai : F.obj i) (Ri : Presieve Ai)
                (h : (K.ι.app i).toFunctor.obj Ai = A),
                Ri ∈ Q i Ai ∧ h ▸ Ri.map (K.ι.app i).toFunctor = R) ∧
            P.HasIsos ∧ P.IsStableUnderFiniteComposition ∧
            P.IsStableUnderFiniteBaseChange ∧ P.HasPullbacks ∧
            ∀ (A : K.pt) (R : Presieve A),
              R ∈ P A ↔ Finite R.uncurry ∧
                R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)) ∧
        (∃ (_ : ∀ i : I, (Q i).HasIsos)
          (_ : ∀ i : I, (Q i).IsStableUnderFiniteComposition)
          (_ : ∀ i : I, (Q i).IsStableUnderFiniteBaseChange)
          (_ : ∀ i : I, (Q i).HasPullbacks),
          (∀ (i : I) (A : F.obj i) (R : Presieve A), R ∈ Q i A → Finite R.uncurry) ∧
          (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
            R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A ↔
              R.map (e i) ∈ Q i ((e i).obj A)) ∧
          (∀ (i j : I) (h : i ≤ j) (A : F.obj i) (R : Presieve A), R ∈ Q i A →
            R.map (F.map (homOfLE h)).toFunctor ∈
              Q j ((F.map (homOfLE h)).toFunctor.obj A)) ∧
          (∀ (i j : I) (h : i ≤ j) (A B C : F.obj i) (f : B ⟶ A) (g : C ⟶ A),
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
          (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
          (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
            Arrow.mk ((v' j).map ((theta i j h).hom.app A) ≫
                (eta j).hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A) =
              Arrow.mk ((eta i).hom.app A)) ∧
          (∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
              (Q i).toGrothendieck (Q j).toGrothendieck)
            (_ : ∀ i : I, (v' i).IsContinuous (Q i).toGrothendieck
              (fullAffineEtaleTopology c.pt)),
            (∀ (i j : I) (h : i ≤ j), ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
                Sheaf (Q j).toGrothendieck (Type u),
              Nonempty (L ⊣ (F.map (homOfLE h)).toFunctor.sheafPushforwardContinuous
                (Type u) (Q i).toGrothendieck (Q j).toGrothendieck) ∧
                PreservesFiniteLimits L) ∧
            (∀ i : I, ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
                Sheaf (fullAffineEtaleTopology c.pt) (Type u),
              Nonempty (L ⊣ (v' i).sheafPushforwardContinuous (Type u)
                (Q i).toGrothendieck (fullAffineEtaleTopology c.pt)) ∧
                PreservesFiniteLimits L))) := by
  let C : I → Cat.{u, u + 1} := fun i ↦ Cat.of (D.obj (op i)).FullAffineEtale
  let P := fun i ↦ fullAffineEtalePrecoverage (D.obj (op i))
  have hiso : ∀ i, (P i).HasIsos := fun i ↦ (affine_precoverage_instances _).1
  have hcomp : ∀ i, (P i).IsStableUnderFiniteComposition :=
    fun i ↦ (affine_precoverage_instances _).2.1
  have hbase : ∀ i, (P i).IsStableUnderFiniteBaseChange :=
    fun i ↦ (affine_precoverage_instances _).2.2.1
  have hpull : ∀ i, (P i).HasPullbacks :=
    fun i ↦ (affine_precoverage_instances _).2.2.2
  have hfinite (i : I) := affine_precoverage_finite (D.obj (op i))
  let F := SiteSystemPairs.diagram C U gamma h0 h4 h8
  let p := SiteSystemPairs.eval C U
  let e := SiteSystemPairs.inclusion C U
  let Q := fun i ↦ finiteEquivalencePrecoverage (p i) (P i)
  have hp (i : I) : (p i).IsEquivalence :=
    SiteSystemPairs.eval_isEquivalence C U h0 i
  have he (i : I) : (e i).IsEquivalence :=
    SiteSystemPairs.inclusion_isEquivalence C U h0 i
  have hep (i : I) : e i ⋙ p i = 𝟭 (C i) :=
    (SiteSystemPairs.inclusion_eval C U i).trans (h0 i)
  let v' := SiteSystemPairs.coefficients C U c.pt.FullAffineEtale v delta
  let theta := SiteSystemPairs.theta C U gamma h0 h3
  let eta (i : I) : e i ⋙ v' i ≅ v i := eqToIso
    (SiteSystemPairs.inclusion_coefficients C U c.pt.FullAffineEtale v delta h0 h5 i)
  have hvcompat (i j : I) (h : i ≤ j) :
      (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i :=
    SiteSystemPairs.transition_coefficients C U gamma c.pt.FullAffineEtale v delta h9 i j h
  have hecover (i : I) (A : C i) (R : Presieve A) :
      R ∈ P i A ↔ R.map (e i) ∈ Q i ((e i).obj A) :=
    finiteEquivalencePrecoverage_inclusion (p i) (P i) (e i) (hep i) (hfinite i) A R
  have hcov (i j : I) (h : i ≤ j) (A : F.obj i) (R : Presieve A)
      (hR : R ∈ Q i A) : R.map (F.map (homOfLE h)).toFunctor ∈
        Q j ((F.map (homOfLE h)).toFunctor.obj A) :=
    finiteEquivalencePrecoverage_transition (p i) (P i) (p j) (P j)
      (U i j h) (h10 i j h) (SiteSystemPairs.transition C U gamma i j h)
      (SiteSystemPairs.comparison C U gamma i j h) A R hR
  have hpb (i j : I) (h : i ≤ j) (A B E : F.obj i) (f : B ⟶ A) (g : E ⟶ A) :
      PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor := by
    have := h11 i j h ((p i).obj A) ((p i).obj B) ((p i).obj E)
      ((p i).map f) ((p i).map g)
    have : PreservesLimit (cospan f g ⋙ p i) (U i j h) :=
      preservesLimit_of_iso_diagram (U i j h) (cospanCompIso (p i) f g).symm
    have : PreservesLimit (cospan f g) (p i ⋙ U i j h) := inferInstance
    have : PreservesLimit (cospan f g)
        ((F.map (homOfLE h)).toFunctor ⋙ p j) :=
      preservesLimit_of_natIso (cospan f g) (SiteSystemPairs.comparison C U gamma i j h).symm
    exact preservesLimit_of_reflects_of_preserves _ (p j)
  have hcont (i j : I) (h : i ≤ j) :
      (F.map (homOfLE h)).toFunctor.IsContinuous (Q i).toGrothendieck (Q j).toGrothendieck :=
    continuous_of_finite_pullbacks _ (Q i) (Q j)
      (finiteEquivalencePrecoverage_finite (p i) (P i)) (hcov i j h)
      (fun A B E _ _ f g _ ↦ hpb i j h A B E f g)
  have hpcont (i : I) : (p i).IsContinuous (Q i).toGrothendieck (P i).toGrothendieck :=
    continuous_of_finite_pullbacks (p i) (Q i) (P i)
      (finiteEquivalencePrecoverage_finite (p i) (P i))
      (fun _ _ hR ↦ hR.2) (by intros; infer_instance)
  have hecont (i : I) : (e i).IsContinuous (P i).toGrothendieck (Q i).toGrothendieck :=
    continuous_of_finite_pullbacks (e i) (P i) (Q i) (hfinite i)
      (fun A R hR ↦ (hecover i A R).mp hR) (by intros; infer_instance)
  have htheta (i j : I) (h : i ≤ j) (A : C i) :
      Arrow.mk ((v' j).map ((theta i j h).hom.app A) ≫
          (eta j).hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A) =
        Arrow.mk ((eta i).hom.app A) := by
    have ht := SiteSystemPairs.theta_coefficients C U gamma c.pt.FullAffineEtale
      v delta h0 h3 h5 i j h A
    have hm : (v' j).map ((theta i j h).hom.app A) =
        (delta i j h).inv.app A := (Arrow.mk_injective _ _) ht
    simp only [hm, eta, eqToIso.hom, eqToHom_app]
    change Arrow.mk (((delta i j h).inv.app A ≫ 𝟙 _) ≫
      (delta i j h).hom.app A) = Arrow.mk (𝟙 ((v i).obj A))
    rw [Category.comp_id, Iso.inv_hom_id_app]
  obtain ⟨hUcont, hvcont, hUadj, hvadj⟩ := h14
  let uc (i j : I) (h : i ≤ j) :
      (U i j h).IsContinuous (P i).toGrothendieck (P j).toGrothendieck := hUcont i j h
  let vc (i : I) :
      (v i).IsContinuous (P i).toGrothendieck (fullAffineEtaleTopology c.pt) := hvcont i
  have coeffComparison (i : I) : v' i ≅ p i ⋙ v i :=
    NatIso.ofComponents (fun X ↦ ((delta X.stage i X.le).app X.obj).symm) (by
      intro X Y f
      change ((delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom ≫
        (delta Y.stage i Y.le).hom.app Y.obj) ≫
        (delta Y.stage i Y.le).inv.app Y.obj =
        (delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom
      simp)
  have hvcont' (i : I) : (v' i).IsContinuous (Q i).toGrothendieck
      (fullAffineEtaleTopology c.pt) := by
    have : (p i ⋙ v i).IsContinuous (Q i).toGrothendieck
        (fullAffineEtaleTopology c.pt) :=
      Functor.isContinuous_comp (p i) (v i)
        (Q i).toGrothendieck (P i).toGrothendieck (fullAffineEtaleTopology c.pt)
    exact Functor.isContinuous_of_iso (coeffComparison i).symm _ _
  have adjp (i : I) : ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
      Sheaf (P i).toGrothendieck (Type u),
      Nonempty (L ⊣ (p i).sheafPushforwardContinuous (Type u)
        (Q i).toGrothendieck (P i).toGrothendieck) ∧ PreservesFiniteLimits L := by
    let a : p i ≅ (e i).inv :=
      (p i).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (e i).asEquivalence.counitIso.symm (p i) ≪≫
        Functor.associator (e i).inv (e i) (p i) ≪≫
        Functor.isoWhiskerLeft (e i).inv (eqToIso (hep i)) ≪≫ (e i).inv.rightUnitor
    let eps : 𝟭 (F.obj i) ≅ p i ⋙ e i :=
      (Functor.isoWhiskerRight a (e i) ≪≫ (e i).asEquivalence.counitIso).symm
    exact adjoint_of_continuous_equivalence _ _ (p i) (e i) eps (eqToIso (hep i))
  have adje (i : I) : ∃ L : Sheaf (P i).toGrothendieck (Type u) ⥤
      Sheaf (Q i).toGrothendieck (Type u),
      Nonempty (L ⊣ (e i).sheafPushforwardContinuous (Type u)
        (P i).toGrothendieck (Q i).toGrothendieck) ∧ PreservesFiniteLimits L := by
    let a : p i ≅ (e i).inv :=
      (p i).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (e i).asEquivalence.counitIso.symm (p i) ≪≫
        Functor.associator (e i).inv (e i) (p i) ≪≫
        Functor.isoWhiskerLeft (e i).inv (eqToIso (hep i)) ≪≫ (e i).inv.rightUnitor
    let eps : p i ⋙ e i ≅ 𝟭 (F.obj i) :=
      Functor.isoWhiskerRight a (e i) ≪≫ (e i).asEquivalence.counitIso
    exact adjoint_of_continuous_equivalence _ _ (e i) (p i) (eqToIso (hep i)).symm eps
  have hvadj' (i : I) : ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
      Sheaf (fullAffineEtaleTopology c.pt) (Type u),
      Nonempty (L ⊣ (v' i).sheafPushforwardContinuous (Type u)
        (Q i).toGrothendieck (fullAffineEtaleTopology c.pt)) ∧ PreservesFiniteLimits L := by
    have : (p i ⋙ v i).IsContinuous (Q i).toGrothendieck
        (fullAffineEtaleTopology c.pt) := Functor.isContinuous_comp (p i) (v i)
        (Q i).toGrothendieck (P i).toGrothendieck (fullAffineEtaleTopology c.pt)
    obtain ⟨L, ⟨a⟩, hL⟩ := adjoint_comp (Q i).toGrothendieck (P i).toGrothendieck
      (fullAffineEtaleTopology c.pt) (p i) (v i) (adjp i) (hvadj i)
    exact ⟨L, ⟨a.ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso (coeffComparison i).symm (Type u) _ _)⟩, hL⟩
  have hUadj' (i j : I) (h : i ≤ j) : ∃ L :
      Sheaf (Q i).toGrothendieck (Type u) ⥤ Sheaf (Q j).toGrothendieck (Type u),
      Nonempty (L ⊣ (F.map (homOfLE h)).toFunctor.sheafPushforwardContinuous
        (Type u) (Q i).toGrothendieck (Q j).toGrothendieck) ∧ PreservesFiniteLimits L := by
    let a : p j ≅ (e j).inv :=
      (p j).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (e j).asEquivalence.counitIso.symm (p j) ≪≫
        Functor.associator (e j).inv (e j) (p j) ≪≫
        Functor.isoWhiskerLeft (e j).inv (eqToIso (hep j)) ≪≫ (e j).inv.rightUnitor
    let eps : 𝟭 (F.obj j) ≅ p j ⋙ e j :=
      (Functor.isoWhiskerRight a (e j) ≪≫ (e j).asEquivalence.counitIso).symm
    let T := (F.map (homOfLE h)).toFunctor
    let t : T ≅ (p i ⋙ U i j h) ⋙ e j :=
      T.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft T eps ≪≫
        (Functor.associator T (p j) (e j)).symm ≪≫
        Functor.isoWhiskerRight (SiteSystemPairs.comparison C U gamma i j h) (e j)
    have : (p i ⋙ U i j h).IsContinuous (Q i).toGrothendieck (P j).toGrothendieck :=
      Functor.isContinuous_comp (p i) (U i j h)
        (Q i).toGrothendieck (P i).toGrothendieck (P j).toGrothendieck
    have : ((p i ⋙ U i j h) ⋙ e j).IsContinuous (Q i).toGrothendieck
        (Q j).toGrothendieck := Functor.isContinuous_comp (p i ⋙ U i j h) (e j)
          (Q i).toGrothendieck (P j).toGrothendieck (Q j).toGrothendieck
    obtain ⟨L, ⟨aL⟩, hL⟩ := adjoint_comp (Q i).toGrothendieck (P j).toGrothendieck
      (Q j).toGrothendieck (p i ⋙ U i j h) (e j)
      (adjoint_comp (Q i).toGrothendieck (P i).toGrothendieck (P j).toGrothendieck
        (p i) (U i j h) (adjp i) (hUadj i j h)) (adje j)
    exact ⟨L, ⟨aL.ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso t.symm (Type u) _ _)⟩, hL⟩
  let Pt := fullAffineEtalePrecoverage c.pt
  have : Pt.HasIsos := (affine_precoverage_instances _).1
  have : Pt.IsStableUnderFiniteComposition := (affine_precoverage_instances _).2.1
  have : Pt.IsStableUnderFiniteBaseChange := (affine_precoverage_instances _).2.2.1
  have : Pt.HasPullbacks := (affine_precoverage_instances _).2.2.2
  have hcoeff (i : I) (A : F.obj i) (R : Presieve A) (hR : R ∈ Q i A) :
      R.map (v' i) ∈ Pt ((v' i).obj A) := by
    have h := finiteEquivalencePrecoverage_transition (p i) (P i) (𝟭 _) Pt (v i)
      (h12 i) (v' i) ((v' i).rightUnitor ≪≫ coeffComparison i) A R hR
    have h' := h.2
    change R.map (v' i) ∈ Pt.comap (𝟭 _) ((v' i).obj A) at h'
    rwa [Precoverage.comap_id] at h'
  have hdesc (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
      (f : ∀ a, B a ⟶ A) (hf : Presieve.ofArrows B f ∈ Pt A) :
      ∃ (i : I) (Ai : F.obj i) (Bi : Fin n → F.obj i) (fi : ∀ a, Bi a ⟶ Ai)
        (t : (v' i).obj Ai ≅ A) (s : ∀ a, (v' i).obj (Bi a) ≅ B a),
        Presieve.ofArrows Bi fi ∈ Q i Ai ∧
          ∀ a, (v' i).map (fi a) ≫ t.hom = (s a).hom ≫ f a := by
    obtain ⟨i, Ai, Bi, fi, t, s, hfi, hcomm⟩ := (h18 n A B f).mp hf
    refine ⟨i, (e i).obj Ai, fun a ↦ (e i).obj (Bi a), fun a ↦ (e i).map (fi a),
      t, s, ?_, ?_⟩
    · have h := (hecover i Ai (Presieve.ofArrows Bi fi)).mp hfi
      rwa [Presieve.map_ofArrows] at h
    · intro a
      have hm := Functor.congr_hom
        (SiteSystemPairs.inclusion_coefficients C U c.pt.FullAffineEtale v delta h0 h5 i) (fi a)
      have hm' : (v' i).map ((e i).map (fi a)) = (v i).map (fi a) := by simpa using hm
      rw [hm']
      exact hcomm a
  have hcolimit := PresentationPairs.exists_pairs_finite_colimit_site C U gamma
    c.pt.FullAffineEtale v delta h9 h0 h4 h8 Q Pt h15 hcov h16 h17 hdesc
    (fun i ↦ finiteEquivalencePrecoverage_finite (p i) (P i)) hcoeff
  refine ⟨F, Q, e, v', theta, eta, he, hcolimit, inferInstance, inferInstance,
    inferInstance, inferInstance, (fun i ↦ finiteEquivalencePrecoverage_finite (p i) (P i)),
    hecover, hcov, hpb, hvcompat, htheta, ⟨hcont, hvcont', hUadj', hvadj'⟩⟩



end AlgebraicGeometry.Scheme
