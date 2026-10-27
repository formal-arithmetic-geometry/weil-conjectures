/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Gluing chart sections with prescribed coordinates

Source: Stacks Project, Spaces, Tags 0262, 02WV and 02WW.
(blueprint: lem-trf-scheme-descent-chart-section-lifting)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Even for a large indexing type, a specified scheme coproduct has open injections. -/
private theorem cofan_open {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j)) (i : J) :
    IsOpenImmersion (j i) := by
  classical
  let k : ∀ a, X a ⟶ X i ⨿ Y := fun a ↦
    if e : a = i then eqToHom (congrArg X e) ≫ coprod.inl else j a ≫ coprod.inr
  let δ : Y ⟶ X i ⨿ Y := Cofan.IsColimit.desc h k
  have fac (a : J) : j a ≫ δ = k a := Cofan.IsColimit.fac h k a
  have hi : j i ≫ δ = coprod.inl := by simpa [k] using fac i
  have hr : δ ≫ coprod.desc (j i) (𝟙 Y) = 𝟙 Y := by
    apply Cofan.IsColimit.hom_ext h
    intro a
    change j a ≫ δ ≫ coprod.desc (j i) (𝟙 Y) = j a ≫ 𝟙 Y
    rw [← Category.assoc, fac]
    by_cases e : a = i
    · subst a; simp [k]
    · simp [k, e, Category.assoc]
  have pb : IsPullback (𝟙 (X i)) (j i) coprod.inl δ := by
    apply IsPullback.mk' (by simpa using hi.symm)
    · intro W f g hf _
      simpa using hf
    · intro W a b hab
      refine ⟨a, by simp, ?_⟩
      have hh := congrArg (fun t ↦ t ≫ coprod.desc (j i) (𝟙 Y)) hab
      simpa [Category.assoc, hr] using hh
  exact MorphismProperty.of_isPullback pb inferInstance

private theorem cofan_covers {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j)) :
    ∀ y : Y, ∃ i x, j i x = y := by
  let : ∀ i, IsOpenImmersion (j i) := cofan_open X Y j h
  let W : Y.Opens := ⨆ i, (j i).opensRange
  let k : ∀ i, X i ⟶ W.toScheme := fun i ↦
    IsOpenImmersion.lift W.ι (j i) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨j i x, le_iSup (fun i ↦ (j i).opensRange) i ⟨x, rfl⟩⟩, rfl⟩)
  let t := Cofan.IsColimit.desc h k
  have ht : t ≫ W.ι = 𝟙 Y := by
    apply Cofan.IsColimit.hom_ext h
    intro i
    change j i ≫ t ≫ W.ι = j i ≫ 𝟙 Y
    have hf : j i ≫ t = k i := Cofan.IsColimit.fac h k i
    rw [← Category.assoc, hf]
    exact (IsOpenImmersion.lift_fac _ _ _).trans (Category.comp_id _).symm
  intro y
  have hy : y ∈ W := by
    have he := congrArg (fun f : Y ⟶ Y ↦ f y) ht
    change W.ι (t y) = y at he
    exact he ▸ (t y).property
  obtain ⟨i, x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i, x, hx⟩

private theorem sections_ext {S : Scheme.{u}} {T : Over S} {J : Type*}
    (C : J → Over S) (v : ∀ j, C j ⟶ T)
    (mem : Sieve.ofArrows C v ∈ (Scheme.fppfTopology.over S) T)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    {a b : F.obj.obj (op T)} (h : ∀ j, F.obj.map (v j).op a = F.obj.map (v j).op b) :
    a = b := by
  apply (((isSheaf_iff_isSheaf_of_type _ F.obj).1 F.property).isSheafFor
    (Presieve.ofArrows C v) mem).isSeparatedFor.ext
  rintro Y g ⟨j⟩
  exact h j

private theorem glue_chart_sections {S : Scheme.{u}} {J : Type v}
    {U X T : Over S} (f : X ⟶ U)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (q : yoneda.obj X ⟶ F.obj)
    (hinj : ∀ (B : Over S) (x y : B ⟶ X),
      q.app (op B) x = q.app (op B) y → x ≫ f = y ≫ f → x = y)
    (C : J → Over S) (w : ∀ j, C j ⟶ T)
    (mem : Sieve.ofArrows C w ∈ (Scheme.fppfTopology.over S) T)
    (z : F.obj.obj (op T)) (a : T ⟶ U) (c : ∀ j, C j ⟶ X)
    (hcq : ∀ j, q.app (op (C j)) (c j) = F.obj.map (w j).op z)
    (hcf : ∀ j, c j ≫ f = w j ≫ a) :
    ∃ x : T ⟶ X, q.app (op T) x = z ∧ x ≫ f = a := by
  have compat : Presieve.Arrows.Compatible (yoneda.obj X) w c := by
    intro j k B g h hgh
    change g ≫ c j = h ≫ c k
    apply hinj B
    · calc
        q.app (op B) (g ≫ c j) =
            F.obj.map g.op (q.app (op (C j)) (c j)) :=
          q.naturality_apply g.op (c j)
        _ = F.obj.map h.op (q.app (op (C k)) (c k)) := by
          rw [hcq, hcq, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
            ← op_comp, ← op_comp, hgh]
        _ = q.app (op B) (h ≫ c k) :=
          (q.naturality_apply h.op (c k)).symm
    · rw [Category.assoc, Category.assoc, hcf, hcf,
        ← Category.assoc, ← Category.assoc, hgh]
  let H := (Scheme.fppfTopology.over S).yoneda.obj X
  obtain ⟨x, hx, _⟩ := ((Presieve.isSheafFor_arrows_iff (yoneda.obj X) w).1
    (((isSheaf_iff_isSheaf_of_type _ H.obj).1 H.property).isSheafFor
      (Presieve.ofArrows C w) mem)) c compat
  change ∀ j, w j ≫ x = c j at hx
  refine ⟨x, ?_, ?_⟩
  · apply sections_ext C w mem F
    intro j
    calc
      F.obj.map (w j).op (q.app (op T) x) =
          q.app (op (C j)) (w j ≫ x) :=
        (q.naturality_apply (w j).op x).symm
      _ = _ := by rw [hx, hcq]
  · exact sections_ext C w mem ((Scheme.fppfTopology.over S).yoneda.obj U)
      (fun j ↦ by change w j ≫ x ≫ f = w j ≫ a; rw [← Category.assoc, hx, hcf])


/-- Existence of chart sections with prescribed quotient and base coordinates,
once their uniqueness is known.
Source: Stacks Project, Spaces, Tag 0262, proof (3), and Tags 02WV/02WW;
Descent, Tag 023Q (blueprint: lem-trf-scheme-descent-chart-section-lifting).

Proof: Lift the quotient section on a surjective etale scheme P over the test T,
using representable_etale_fppf_local_lifting. Pull back the open coproduct cover
of V to obtain P_j and maps x_j to X_j. Pair f_j x_j with the prescribed map
P_j to U_i; the pullback property of R_ji gives r_j to R_ji. Transport r_j by
theta_ji and project to X_i. The switched first base-coordinate identity gives
the prescribed U_i coordinate; the quotient compatibility gives the prescribed
quotient section. The maps P_j to T form a jointly surjective etale family,
hence an fppf covering. On every overlap the transported maps agree by the
assumed injectivity for X_i. The subcanonical fppf topology on Over S glues them
to a unique S-morphism T to X_i. Descent uniqueness proves its U_i
coordinate, and separatedness of the fppf sheaf proves its quotient coordinate.
Empty tests and empty summands are covered by the same sheaf condition. -/
theorem scheme_descent_chart_section_lifting
    {S : Scheme.{u}} {I : Type v} (U X : I → Over S) (f : ∀ i, X i ⟶ U i)
    (R : I → I → Over S) (p : ∀ i j, R i j ⟶ X i)
    (b : ∀ i j, R i j ⟶ U i ⨯ U j)
    (hR : ∀ i j, IsPullback (p i j) (b i j) (f i) Limits.prod.fst)
    (theta : ∀ i j, R i j ≅ R j i)
    (hleft : ∀ i j, (theta i j).hom ≫ b j i ≫ Limits.prod.fst =
      b i j ≫ Limits.prod.snd)
    (V : Over S) (ι : ∀ i, X i ⟶ V) (hV : IsColimit (Cofan.mk V ι))
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (q : yoneda.obj V ⟶ F.obj)
    (hqet : IsEtale q) (hqsurj : IsSurjective q)
    (hrel : ∀ i j, yoneda.map (p i j ≫ ι i) ≫ q =
      yoneda.map ((theta i j).hom ≫ p j i ≫ ι j) ≫ q)
    (hinj : ∀ (i : I) (T : Over S) (x y : T ⟶ X i),
      (yoneda.map (ι i) ≫ q).app (op T) x =
        (yoneda.map (ι i) ≫ q).app (op T) y →
      x ≫ f i = y ≫ f i → x = y) :
    ∀ (i : I) (T : Over S) (z : F.obj.obj (op T)) (a : T ⟶ U i),
      ∃ x : T ⟶ X i, (yoneda.map (ι i) ≫ q).app (op T) x = z ∧ x ≫ f i = a := by
  classical
  intro i T z a
  have hVl : IsColimit (Cofan.mk V.left (fun j ↦ (ι j).left)) :=
    isColimitCofanMkObjOfIsColimit (Over.forget S) X ι hV
  have (j : I) : IsOpenImmersion (ι j).left := cofan_open _ _ _ hVl j
  obtain ⟨P, v, d, _, hd, hv, hvs, _⟩ :=
    (representable_etale_fppf_local_lifting F V ⟨q⟩ hqet hqsurj).1 T z
  change q.app (op P) d = F.obj.map v.op z at hd
  let C (j : I) := Limits.pullback (ι j) d
  let l (j : I) : C j ⟶ P := Limits.pullback.snd _ _
  let e (j : I) : C j ⟶ X j := Limits.pullback.fst _ _
  let w (j : I) : C j ⟶ T := l j ≫ v
  have he (j : I) : e j ≫ ι j = l j ≫ d := Limits.pullback.condition
  have hC (j : I) : IsPullback (e j).left (l j).left (ι j).left d.left :=
    (IsPullback.of_hasPullback (ι j) d).map (Over.forget S)
  have hl (j : I) : IsOpenImmersion (l j).left :=
    MorphismProperty.of_isPullback (hC j) inferInstance
  have hw (j : I) : Etale (w j).left := by
    have := hl j
    have := hv
    change Etale ((l j).left ≫ v.left)
    infer_instance
  have hcov : ∀ t : T.left, ∃ j y, (w j).left y = t := by
    intro t
    obtain ⟨p, hp⟩ := hvs.surj t
    obtain ⟨j, x, hx⟩ := cofan_covers _ _ _ hVl (d.left p)
    obtain ⟨c, _, hc⟩ := Scheme.exists_preimage_of_isPullback (hC j) x p hx
    exact ⟨j, c, (congrArg v.left hc).trans hp⟩
  have mem : Sieve.ofArrows C w ∈ (Scheme.fppfTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    change Presieve.ofArrows (fun j ↦ (C j).left) (fun j ↦ (w j).left) ∈
      Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) T.left
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨hcov, fun j ↦ ?_⟩
    have := hw j
    exact ⟨inferInstance, inferInstance⟩
  let r (j : I) : C j ⟶ R j i := (hR j i).lift (e j)
    (Limits.prod.lift (e j ≫ f j) (w j ≫ a)) (by simp)
  have hrp (j : I) : r j ≫ p j i = e j := (hR j i).lift_fst _ _ _
  have hrb (j : I) : r j ≫ b j i = Limits.prod.lift (e j ≫ f j) (w j ≫ a) :=
    (hR j i).lift_snd _ _ _
  let c (j : I) : C j ⟶ X i := r j ≫ (theta j i).hom ≫ p i j
  have hcf (j : I) : c j ≫ f i = w j ≫ a := by
    change (r j ≫ (theta j i).hom ≫ p i j) ≫ f i = _
    rw [Category.assoc, Category.assoc, (hR i j).w, hleft,
      ← Category.assoc, hrb, Limits.prod.lift_snd]
  have hcq (j : I) : (yoneda.map (ι i) ≫ q).app (op (C j)) (c j) =
      F.obj.map (w j).op z := by
    have h := congrArg (fun n ↦ n.app (op (C j)) (r j)) (hrel j i)
    change q.app (op (C j)) (r j ≫ p j i ≫ ι j) =
      q.app (op (C j)) (r j ≫ (theta j i).hom ≫ p i j ≫ ι i) at h
    change q.app (op (C j)) (c j ≫ ι i) = _
    rw [show c j ≫ ι i = r j ≫ (theta j i).hom ≫ p i j ≫ ι i by
      simp only [c, Category.assoc], ← h, ← Category.assoc, hrp, he]
    calc
      q.app (op (C j)) (l j ≫ d) = F.obj.map (l j).op (q.app (op P) d) :=
        q.naturality_apply (l j).op d
      _ = F.obj.map (l j).op (F.obj.map v.op z) := by rw [hd]
      _ = F.obj.map (w j).op z := by simp [w]
  exact glue_chart_sections (f i) F (yoneda.map (ι i) ≫ q)
    (hinj i) C w mem z a c hcq hcf

end AlgebraicGeometry.AlgebraicSpace
