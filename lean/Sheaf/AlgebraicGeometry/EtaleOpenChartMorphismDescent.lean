/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FppfLocalOpenSubfunctorDescent
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Descent of an invariant open chart and its morphism

Source: Stacks Project, Spaces, Tag 02WU; Properties of Spaces, Tag 03BZ;
Divisors on Spaces, Tag 0D2Z
(blueprint: lem-trf-etale-open-chart-morphism-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The actual open subscheme, with its inherited map to the base.
Source: Stacks, Tag 03BZ (blueprint: lem-trf-etale-open-chart-morphism-descent). -/
def openChartObject {S : Scheme.{u}} (V : Over S) (O : V.left.Opens) : Over S :=
  Over.mk (O.ι ≫ V.hom)

/-- The inclusion of the actual open subscheme over the base.
Source: Stacks, Tag 03BZ (blueprint: lem-trf-etale-open-chart-morphism-descent). -/
def openChartInclusion {S : Scheme.{u}} (V : Over S) (O : V.left.Opens) :
    openChartObject V O ⟶ V :=
  Over.homMk O.ι

private theorem preimage_sheafify {C : Type*} [Category C]
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type u}
    (A : Subfunctor F) (f : G ⟶ F) :
    (A.sheafify J).preimage f = (A.preimage f).sheafify J := by
  ext B x
  change A.sieveOfSection (f.app B x) ∈ J B.unop ↔
    (A.preimage f).sieveOfSection x ∈ J B.unop
  have h : A.sieveOfSection (f.app B x) = (A.preimage f).sieveOfSection x := by
    ext D g
    change F.map g.op (f.app B x) ∈ A.obj (op D) ↔
      f.app (op D) (G.map g.op x) ∈ A.obj (op D)
    rw [f.naturality_apply]
  rw [h]

private theorem range_isSheaf {C : Type*} [Category C]
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [Mono f] (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (Subfunctor.range f).toFunctor := by
  exact Presieve.isSheaf_iso J (asIso (Subfunctor.toRange f)) hF

private theorem range_factor {C : Type*} [Category C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ G) (q : F ⟶ H)
    (hq : ∀ (B : Cᵒᵖ) (a b : F.obj B), f.app B a = f.app B b →
      q.app B a = q.app B b) :
    ∃ r : (Subfunctor.range f).toFunctor ⟶ H, Subfunctor.toRange f ≫ r = q := by
  classical
  let r : (Subfunctor.range f).toFunctor ⟶ H :=
    { app := fun B ↦ ↾fun x ↦ q.app B x.property.choose
      naturality := by
        intro B D g
        ext x
        change q.app D _ = H.map g (q.app B _)
        rw [← q.naturality_apply]
        apply hq
        rw [((Subfunctor.range f).toFunctor.map g x).property.choose_spec,
          f.naturality_apply, x.property.choose_spec]
        rfl }
  refine ⟨r, ?_⟩
  ext B x
  apply hq
  exact ((Subfunctor.toRange f).app B x).property.choose_spec

private theorem factor_open_iff {S : Scheme.{u}} {B V : Over S}
    (O : V.left.Opens) (f : B ⟶ V) :
    (∃ w : B ⟶ openChartObject V O, w ≫ openChartInclusion V O = f) ↔
      Set.range f.left ⊆ (O : Set V.left) := by
  constructor
  · rintro ⟨w, rfl⟩
    rintro _ ⟨x, rfl⟩
    exact (w.left x).property
  · intro h
    have h' : Set.range f.left ⊆ Set.range O.ι := by
      simpa only [Scheme.Opens.range_ι] using h
    let w := IsOpenImmersion.lift O.ι f.left h'
    have hw : w ≫ O.ι = f.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk w ?_, ?_⟩
    · change w ≫ O.ι ≫ V.hom = B.hom
      rw [← Category.assoc, hw, f.w]
    · apply Over.OverMorphism.ext
      exact hw

private theorem openChart_mono {S : Scheme.{u}} (V : Over S) (O : V.left.Opens) :
    Mono (openChartInclusion V O) := by
  apply (Over.forget S).mono_of_mono_map
  change Mono O.ι
  infer_instance

private theorem subfunctor_square {C : Type*} [Category C]
    {F G K : Cᵒᵖ ⥤ Type u} (A : Subfunctor K)
    (j : F ⟶ G) (k : F ⟶ A.toFunctor) (p : G ⟶ K) [Mono j]
    (w : j ≫ p = k ≫ A.ι) (hpre : A.preimage p = Subfunctor.range j) :
    IsPullback j k p A.ι := by
  classical
  refine IsPullback.mk' w (fun _ _ _ h _ ↦ (cancel_mono j).mp h) ?_
  intro T a b hab
  have ha : Subfunctor.range a ≤ Subfunctor.range j := by
    intro B x hx
    obtain ⟨y, rfl⟩ := hx
    rw [← hpre]
    change p.app B (a.app B y) ∈ A.obj B
    have he := ConcreteCategory.congr_hom (congr_app hab B) y
    exact he.symm ▸ (b.app B y).property
  let l := Subfunctor.lift a ha ≫ inv (Subfunctor.toRange j)
  have hl : l ≫ j = a := by
    have hj : inv (Subfunctor.toRange j) ≫ j = (Subfunctor.range j).ι := by
      apply (cancel_epi (Subfunctor.toRange j)).mp
      rw [IsIso.hom_inv_id_assoc, Subfunctor.toRange_ι]
    exact (Category.assoc _ _ _).trans ((congr_arg (fun f ↦ Subfunctor.lift a ha ≫ f) hj).trans
      (Subfunctor.lift_ι a ha))
  refine ⟨l, hl, ?_⟩
  apply (cancel_mono A.ι).mp
  rw [Category.assoc, ← w, ← Category.assoc, hl, hab]

private theorem preimage_of_square {C : Type*} [Category C]
    {F G H : Cᵒᵖ ⥤ Type u} (A : Subfunctor H)
    (j : F ⟶ G) (k : F ⟶ A.toFunctor) (a : G ⟶ H)
    (h : IsPullback j k a A.ι) : A.preimage a = Subfunctor.range j := by
  ext B x
  change a.app B x ∈ A.obj B ↔ x ∈ Set.range (j.app B)
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := Types.exists_of_isPullback
      (h.map ((evaluation _ _).obj B)) x ⟨a.app B x, hx⟩ rfl
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hw := ConcreteCategory.congr_hom (congr_app h.w B) y
    exact hw.symm ▸ (k.app B y).property

private theorem compare_atlas {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {V B E E' : Over S} {p : yoneda.obj V ⟶ F} {a : yoneda.obj B ⟶ F}
    {v : E ⟶ V} {e : E ⟶ B} {v' : yoneda.obj E' ⟶ yoneda.obj V}
    {e' : E' ⟶ B} (h : IsPullback (yoneda.map v) (yoneda.map e) p a)
    (h' : IsPullback v' (yoneda.map e') p a) :
    ∃ i : E ≅ E', i.hom ≫ e' = e := by
  let j := h.isoPullback ≪≫ h'.isoPullback.symm
  let i := yoneda.preimageIso j
  refine ⟨i, ?_⟩
  apply yoneda.map_injective
  change yoneda.map i.hom ≫ yoneda.map e' = yoneda.map e
  have hi : yoneda.map i.hom = j.hom := by
    exact yoneda.map_preimage _
  rw [hi]
  dsimp [j]
  simp only [Category.assoc,
    IsPullback.isoPullback_inv_snd, IsPullback.isoPullback_hom_snd]

private theorem atlas_properties {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {V B E : Over S} {p : yoneda.obj V ⟶ F} (hp : IsEtale p)
    (hsur : IsSurjective p) {a : yoneda.obj B ⟶ F} {v : E ⟶ V} {e : E ⟶ B}
    (h : IsPullback (yoneda.map v) (yoneda.map e) p a) :
    Etale e.left ∧ Surjective e.left := by
  obtain ⟨E', e', v', h', he'⟩ := hp B a
  obtain ⟨i, hi⟩ := compare_atlas h h'
  have : Etale e'.left := he'
  have he : Etale e.left := by
    have hleft := congr_arg (fun f ↦ f.left) hi
    change i.hom.left ≫ e'.left = e.left at hleft
    rw [← hleft]
    infer_instance
  obtain ⟨E'', e'', v'', h'', he''⟩ := hsur B a
  obtain ⟨i', hi'⟩ := compare_atlas h h''
  have : Surjective e''.left := he''
  refine ⟨he, ?_⟩
  have hleft := congr_arg (fun f ↦ f.left) hi'
  change i'.hom.left ≫ e''.left = e.left at hleft
  rw [← hleft]
  infer_instance

private theorem fppf_singleton {S : Scheme.{u}} {E B : Over S} (e : E ⟶ B)
    [Etale e.left] [Surjective e.left] :
    Sieve.generate (Presieve.singleton e) ∈ (Scheme.fppfTopology.over S) B := by
  rw [GrothendieckTopology.mem_over_iff]
  change (Sieve.generate (Presieve.singleton e)).functorPushforward (Over.forget S) ∈
    Scheme.fppfTopology B.left
  rw [← Sieve.generate_map_eq_functorPushforward]
  have hmap : (Presieve.singleton e).map (Over.forget S) =
      Presieve.singleton e.left := by
    simp
  rw [hmap]
  exact Precoverage.generate_mem_toGrothendieck e.left.singleton_mem_fppfPrecoverage

private theorem atlas_locallySurjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {V : Over S} {p : yoneda.obj V ⟶ F}
    (hp : IsEtale p) (hsur : IsSurjective p) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p := by
  constructor
  intro B x
  let a : yoneda.obj B ⟶ F := yonedaEquiv.symm x
  obtain ⟨E, e, v, h, he⟩ := hp B a
  let v' : E ⟶ V := yoneda.preimage v
  have hv : yoneda.map v' = v := yoneda.map_preimage _
  have h' : IsPullback (yoneda.map v') (yoneda.map e) p a := by rwa [hv]
  obtain ⟨he, hs⟩ := atlas_properties hp hsur h'
  have : Etale e.left := he
  have : Surjective e.left := hs
  apply (Scheme.fppfTopology.over S).superset_covering _ (fppf_singleton e)
  apply (Sieve.generate_le_iff _ _).mpr
  intro D f hf
  cases hf
  refine ⟨v', ?_⟩
  have hw := ConcreteCategory.congr_hom (congr_app h'.w (op E)) (𝟙 E)
  simpa [a, yonedaEquiv] using hw

private theorem invariant_range {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    {V R : Over S} {p : yoneda.obj V ⟶ X} {s t : R ⟶ V}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (O : V.left.Opens) (hinv : s.left ⁻¹ᵁ O = t.left ⁻¹ᵁ O) :
    (Subfunctor.range (yoneda.map (openChartInclusion V O) ≫ p)).preimage p =
      Subfunctor.range (yoneda.map (openChartInclusion V O)) := by
  ext B v
  change (∃ w, p.app B (w ≫ openChartInclusion V O) = p.app B v) ↔
    ∃ w, w ≫ openChartInclusion V O = v
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨c, hc, hc'⟩ := Types.exists_of_isPullback
      (hR.map ((evaluation _ _).obj B)) v (w ≫ openChartInclusion V O) hw.symm
    apply (factor_open_iff O v).mpr
    rintro _ ⟨x, rfl⟩
    have hx : c.left x ∈ t.left ⁻¹ᵁ O := by
      change t.left (c.left x) ∈ O
      have he := congr_arg (fun f : B.unop ⟶ V ↦ f.left x) hc'
      change t.left (c.left x) = _ at he
      rw [he]
      exact (w.left x).property
    rw [← hinv] at hx
    have he := congr_arg (fun f : B.unop ⟶ V ↦ f.left x) hc
    change s.left (c.left x) = _ at he
    change s.left (c.left x) ∈ O at hx
    rwa [he] at hx
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩

private theorem open_range_preimage {S : Scheme.{u}} {B C : Over S}
    (f : C ⟶ B) (W : B.left.Opens) :
    (Subfunctor.range (yoneda.map (openChartInclusion B W))).preimage (yoneda.map f) =
      Subfunctor.range (yoneda.map (openChartInclusion C (f.left ⁻¹ᵁ W))) := by
  ext D g
  change (∃ w, w ≫ openChartInclusion B W = g ≫ f) ↔
    ∃ w, w ≫ openChartInclusion C (f.left ⁻¹ᵁ W) = g
  rw [factor_open_iff, factor_open_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    exact h ⟨x, rfl⟩
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    exact h ⟨x, rfl⟩

private theorem open_range_injective {S : Scheme.{u}} (B : Over S)
    (W W' : B.left.Opens)
    (h : Subfunctor.range (yoneda.map (openChartInclusion B W)) =
      Subfunctor.range (yoneda.map (openChartInclusion B W'))) : W = W' := by
  apply le_antisymm
  · have hx : openChartInclusion B W ∈
        (Subfunctor.range (yoneda.map (openChartInclusion B W'))).obj
          (op (openChartObject B W)) := by
      rw [← h]
      exact ⟨𝟙 _, by simp⟩
    obtain ⟨w, hw⟩ := hx
    have hfactor := (factor_open_iff W' (openChartInclusion B W)).mp ⟨w, hw⟩
    change Set.range W.ι ⊆ _ at hfactor
    change (W : Set B.left) ⊆ (W' : Set B.left)
    simpa only [Scheme.Opens.range_ι] using hfactor
  · have hx : openChartInclusion B W' ∈
        (Subfunctor.range (yoneda.map (openChartInclusion B W))).obj
          (op (openChartObject B W')) := by
      rw [h]
      exact ⟨𝟙 _, by simp⟩
    obtain ⟨w, hw⟩ := hx
    have hfactor := (factor_open_iff W (openChartInclusion B W')).mp ⟨w, hw⟩
    change Set.range W'.ι ⊆ _ at hfactor
    change (W' : Set B.left) ⊆ (W : Set B.left)
    simpa only [Scheme.Opens.range_ι] using hfactor

private theorem open_preimage_injective {S : Scheme.{u}} {E B : Over S}
    (e : E ⟶ B) [Surjective e.left] (W W' : B.left.Opens)
    (h : e.left ⁻¹ᵁ W = e.left ⁻¹ᵁ W') : W = W' := by
  apply TopologicalSpace.Opens.ext
  apply Set.preimage_injective.mpr (Scheme.Hom.surjective e.left)
  exact congr_arg (fun U : E.left.Opens ↦ (U : Set E.left)) h

private theorem representable_subfunctor_isSheaf {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (A : Subfunctor F)
    (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (hA : IsRepresentable A.ι) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) A.toFunctor := by
  let J := Scheme.fppfTopology.over S
  apply (A.isSheaf_iff hF).mpr
  intro B x hx
  let a : yoneda.obj B.unop ⟶ F := yonedaEquiv.symm x
  obtain ⟨E, e, k, h, _⟩ := hA B.unop a
  have : Mono (yoneda.map e) := h.flip.mono_fst_of_mono
  have : Mono e := yoneda.mono_of_mono_map inferInstance
  have hlift : ∀ (D : Over S) (g : D ⟶ B.unop),
      A.sieveOfSection x g → ∃ w : D ⟶ E, w ≫ e = g := by
    intro D g hg
    obtain ⟨w, _, hw⟩ := Types.exists_of_isPullback
      (h.map ((evaluation _ _).obj (op D)))
      ⟨F.map g.op x, hg⟩ g (by simp [a, yonedaEquiv])
    exact ⟨w, hw⟩
  classical
  let family : (A.sieveOfSection x).arrows.FamilyOfElements (yoneda.obj E) :=
    fun D g hg ↦ (hlift D g hg).choose
  have hf : family.Compatible := by
    intro D₁ D₂ D₃ g₁ g₂ f₁ f₂ h₁ h₂ heq
    apply (cancel_mono e).mp
    change (g₁ ≫ (hlift D₁ f₁ h₁).choose) ≫ e =
      (g₂ ≫ (hlift D₂ f₂ h₂).choose) ≫ e
    rw [Category.assoc, Category.assoc, (hlift D₁ f₁ h₁).choose_spec,
      (hlift D₂ f₂ h₂).choose_spec, heq]
  have hE := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := J) (yoneda.obj E)
  obtain ⟨w, hw, _⟩ := hE _ hx family hf
  have he : w ≫ e = 𝟙 B.unop := by
    have hB := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := J) (yoneda.obj B.unop)
    apply (hB _ hx).isSeparatedFor.ext
    intro D g hg
    change g ≫ w ≫ e = g ≫ 𝟙 _
    have hwg : g ≫ w = (hlift D g hg).choose := hw g hg
    rw [← Category.assoc, hwg]
    exact (hlift D g hg).choose_spec.trans (Category.comp_id g).symm
  have hw' := ConcreteCategory.congr_hom (congr_app h.w B) w
  have hx' : a.app B (w ≫ e) = x := by simp [he, a, yonedaEquiv]
  change x ∈ A.obj B
  change (k.app B w).val = a.app B (w ≫ e) at hw'
  rw [← hx', ← hw']
  exact (k.app B w).property

private theorem subfunctor_preimage_injective {C : Type*} [Category C]
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type u} (p : G ⟶ F)
    [Presheaf.IsLocallySurjective J p] (hF : Presieve.IsSheaf J F)
    (A A' : Subfunctor F) (hA : Presieve.IsSheaf J A.toFunctor)
    (hA' : Presieve.IsSheaf J A'.toFunctor)
    (h : A.preimage p = A'.preimage p) : A = A' := by
  suffices hle : ∀ (A A' : Subfunctor F), Presieve.IsSheaf J A'.toFunctor →
      A.preimage p = A'.preimage p → A ≤ A' by
    exact le_antisymm (hle A A' hA' h) (hle A' A hA h.symm)
  intro A A' hs he B x hx
  apply (A'.isSheaf_iff hF).mp hs
  apply J.superset_covering _ (Presheaf.imageSieve_mem J p x)
  intro D g hg
  obtain ⟨v, hv⟩ := hg
  change F.map g.op x ∈ A'.obj (op D)
  rw [← hv]
  change v ∈ (A'.preimage p).obj (op D)
  rw [← he]
  change p.app (op D) v ∈ A.obj (op D)
  rw [hv]
  exact A.map g.op hx

/-- An invariant open chart and a compatible morphism descend uniquely. Equality on
`R_O` is expressed on all scheme tests mapping to the restricted relation. The pullback
of an open subspace is equality of subfunctors with the range of its open inclusion.
Source: Stacks, Tags 02WU, 03BZ and 0D2Z
(blueprint: lem-trf-etale-open-chart-morphism-descent).

Proof:
1. Every representing scheme pullback of the atlas is surjective and etale, by
   uniqueness of representing pullbacks. Its singleton is an fppf cover, so p is
   locally surjective.
2. Let A be the range of the open-chart map into X and G its subsheafification.
   The relation pullback and invariance give A.preimage p = h_O. Subsheafification
   commutes with preimage; the monic representable h_O is already a sheaf. Thus
   G.preimage p = h_O, giving the required cartesian open square.
3. Apply fppf_local_open_subfunctor_descent to that square. Its representing
   isomorphisms give the open-subspace structure and all test representations.
4. A representable subfunctor of a sheaf is a sheaf: on its membership sieve,
   glue the local sections of its representing monomorphism by subcanonicity.
   Locally surjective p detects equality of subsheaves, proving uniqueness of U.
5. Compatibility on R makes q constant on the fibres of the open-chart map.
   It therefore defines a natural map from A to Z. Mathlib's sheafifyLift
   extends this to r on G. Its restriction and uniqueness lemmas give pO ≫ r = q
   and detection of equality of maps from G into any sheaf.
6. Pulling back the test representation along its atlas cover identifies the
   inverse image open with v inverse O. Surjectivity gives uniqueness of the
   open. The elementary preimage formula for open-inclusion ranges proves
   arbitrary base change. A test factoring through U lifts to O on its atlas
   cover, and cancelling G's monic inclusion proves the stated formula for r.
7. Apply detection to any algebraic-space target, and then to the representable
   sheaf h_T to obtain the relative-base condition. No quasi-compactness,
   separation or nonemptiness hypothesis is used. -/
theorem etale_open_chart_morphism_descent {S : Scheme.{u}}
    (X Z : AlgebraicSpace S) (V : Over S) (p : yoneda.obj V ⟶ X.obj.obj)
    (hp : IsEtale p) (hsur : IsSurjective p)
    (R : Over S) (s t : R ⟶ V)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (O : V.left.Opens) (hinv : s.left ⁻¹ᵁ O = t.left ⁻¹ᵁ O)
    (q : yoneda.obj (openChartObject V O) ⟶ Z.obj.obj)
    (hq : ∀ (B : Over S) (a b : B ⟶ openChartObject V O) (c : B ⟶ R),
      c ≫ s = a ≫ openChartInclusion V O →
      c ≫ t = b ≫ openChartInclusion V O → yoneda.map a ≫ q = yoneda.map b ≫ q) :
    ∃ U : OpenSubspace X,
      U.val.preimage p = Subfunctor.range (yoneda.map (openChartInclusion V O)) ∧
      (∀ U' : OpenSubspace X,
        U'.val.preimage p = Subfunctor.range (yoneda.map (openChartInclusion V O)) →
          U' = U) ∧
      ∃ pO : yoneda.obj (openChartObject V O) ⟶ U.val.toFunctor,
        pO ≫ U.val.ι = yoneda.map (openChartInclusion V O) ≫ p ∧
        ∃ r : U.val.toFunctor ⟶ Z.obj.obj,
          pO ≫ r = q ∧
          (∀ r' : U.val.toFunctor ⟶ Z.obj.obj, pO ≫ r' = q → r' = r) ∧
          (∀ (B : Over S) (a : yoneda.obj B ⟶ X.obj.obj)
            (E : Over S) (e : E ⟶ B) (v : E ⟶ V),
            IsPullback (yoneda.map v) (yoneda.map e) p a →
            ∃ W : B.left.Opens, e.left ⁻¹ᵁ W = v.left ⁻¹ᵁ O ∧
              (∀ W' : B.left.Opens, e.left ⁻¹ᵁ W' = v.left ⁻¹ᵁ O → W' = W) ∧
              U.val.preimage a = Subfunctor.range (yoneda.map (openChartInclusion B W))) ∧
          (∀ (B C : Over S) (a : yoneda.obj B ⟶ X.obj.obj) (f : C ⟶ B)
            (W : B.left.Opens),
            U.val.preimage a = Subfunctor.range (yoneda.map (openChartInclusion B W)) →
            U.val.preimage (yoneda.map f ≫ a) =
              Subfunctor.range (yoneda.map (openChartInclusion C (f.left ⁻¹ᵁ W)))) ∧
          (∀ (B : Over S) (b : yoneda.obj B ⟶ U.val.toFunctor)
            (E : Over S) (e : E ⟶ B) (v : E ⟶ V),
            IsPullback (yoneda.map v) (yoneda.map e) p (b ≫ U.val.ι) →
            ∃ w : E ⟶ openChartObject V O,
              w ≫ openChartInclusion V O = v ∧
              yoneda.map e ≫ b ≫ r = yoneda.map w ≫ q) ∧
          (∀ (Z' : AlgebraicSpace S) (r₁ r₂ : U.val.toFunctor ⟶ Z'.obj.obj),
            pO ≫ r₁ = pO ≫ r₂ → r₁ = r₂) ∧
          (∀ (T : Over S) (x : X.obj.obj ⟶ yoneda.obj T)
            (z : Z.obj.obj ⟶ yoneda.obj T),
            q ≫ z = yoneda.map (openChartInclusion V O) ≫ p ≫ x →
              r ≫ z = U.val.ι ≫ x) := by
  classical
  let J := Scheme.fppfTopology.over S
  let i := yoneda.map (openChartInclusion V O)
  let f := i ≫ p
  let A := Subfunctor.range f
  let G := A.sheafify J
  have hX : Presieve.IsSheaf J X.obj.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp X.obj.property
  have hZ : Presieve.IsSheaf J Z.obj.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp Z.obj.property
  have hG : Presieve.IsSheaf J G.toFunctor := A.sheafify_isSheaf hX
  have hi : Mono (openChartInclusion V O) := openChart_mono V O
  have : Mono i := by dsimp [i]; infer_instance
  have hpre : G.preimage p = Subfunctor.range i := by
    dsimp [G]
    rw [preimage_sheafify, invariant_range hR O hinv]
    exact (Subfunctor.eq_sheafify _
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _) (range_isSheaf J i
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))).symm
  let pO : yoneda.obj (openChartObject V O) ⟶ G.toFunctor :=
    Subfunctor.toRangeSheafify J f
  have hpO : pO ≫ G.ι = i ≫ p := by
    rfl
  have hsquare : IsPullback i pO p G.ι := subfunctor_square G i pO p hpO.symm hpre
  have hpLocal := atlas_locallySurjective hp hsur
  let GS : Sheaf J (Type u) :=
    ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr hG⟩
  have hmono : ∀ T : Over S, Function.Injective (G.ι.app (op T)) := by
    intro T a b h
    exact Subtype.ext h
  obtain ⟨W, eW, heW, _, _, _, _⟩ :=
    fppf_local_open_subfunctor_descent.{u, 0} V X.obj GS G.ι hmono p hpLocal O
      hsquare.isoPullback hsquare.isoPullback_hom_fst
  have htest (B : Over S) (a : yoneda.obj B ⟶ X.obj.obj) :
      G.preimage a = Subfunctor.range (yoneda.map (openChartInclusion B (W B a))) := by
    have hpb : IsPullback (yoneda.map (openChartInclusion B (W B a)))
        ((eW B a).hom ≫ pullback.snd a G.ι) a G.ι := by
      apply IsPullback.of_iso_pullback _ (eW B a) (heW B a) rfl
      constructor
      simp only [Category.assoc, ← pullback.condition]
      exact (congr_arg (fun k ↦ k ≫ a) (heW B a)).symm
    exact preimage_of_square G _ _ _ hpb
  have hrepr : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) G.ι := by
    intro B a
    refine ⟨openChartObject B (W B a), openChartInclusion B (W B a),
      (eW B a).hom ≫ pullback.snd a G.ι, ?_, ?_⟩
    · exact (IsPullback.of_iso_pullback
        ⟨by
          calc
            yoneda.map (Over.homMk (W B a).ι) ≫ a =
                ((eW B a).hom ≫ pullback.fst a G.ι) ≫ a :=
              congr_arg (fun k ↦ k ≫ a) (heW B a).symm
            _ = ((eW B a).hom ≫ pullback.snd a G.ι) ≫ G.ι := by
              rw [Category.assoc, pullback.condition, ← Category.assoc]⟩
        (eW B a) (heW B a) rfl).flip
    · change IsOpenImmersion (W B a).ι
      infer_instance
  let U : OpenSubspace X := ⟨G, hrepr⟩
  refine ⟨U, hpre, ?_, pO, hpO, ?_⟩
  · intro U' hU'
    apply Subtype.ext
    apply subfunctor_preimage_injective J p hX U'.val G
      (representable_subfunctor_isSheaf U'.val hX ?_) hG (hU'.trans hpre.symm)
    intro B a
    obtain ⟨E, e, k, h, _⟩ := U'.property B a
    exact ⟨E, e, k, h, trivial⟩
  have hfib : ∀ (B : (Over S)ᵒᵖ) (a b : (yoneda.obj (openChartObject V O)).obj B),
      f.app B a = f.app B b → q.app B a = q.app B b := by
    intro B a b hab
    obtain ⟨c, hc, hc'⟩ := Types.exists_of_isPullback
      (hR.map ((evaluation _ _).obj B))
      (a ≫ openChartInclusion V O) (b ≫ openChartInclusion V O) hab
    exact ConcreteCategory.congr_hom (congr_app (hq B.unop a b c hc hc') B) (𝟙 B.unop)
  obtain ⟨d, hd⟩ := range_factor f q hfib
  let r := A.sheafifyLift d hZ
  have hr : pO ≫ r = q := by
    change (Subfunctor.toRange f ≫ Subfunctor.homOfLe (A.le_sheafify J)) ≫
      A.sheafifyLift d hZ = q
    rw [Category.assoc, Subfunctor.to_sheafifyLift, hd]
  have hdetect (H : (Over S)ᵒᵖ ⥤ Type u) (hH : Presieve.IsSheaf J H)
      (r₁ r₂ : G.toFunctor ⟶ H) (heq : pO ≫ r₁ = pO ≫ r₂) : r₁ = r₂ := by
    apply A.to_sheafify_lift_unique hH
    apply (cancel_epi (Subfunctor.toRange f)).mp
    change (Subfunctor.toRange f ≫ Subfunctor.homOfLe (A.le_sheafify J)) ≫ r₁ =
      (Subfunctor.toRange f ≫ Subfunctor.homOfLe (A.le_sheafify J)) ≫ r₂ at heq
    simpa only [Category.assoc] using heq
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r' hr'
    exact hdetect _ hZ r' r (hr'.trans hr.symm)
  · intro B a E e v h
    obtain ⟨he, hs⟩ := atlas_properties hp hsur h
    have : Surjective e.left := hs
    have heq : e.left ⁻¹ᵁ W B a = v.left ⁻¹ᵁ O := by
      apply open_range_injective E
      rw [← open_range_preimage, ← htest, ← Subfunctor.preimage_comp,
        ← h.w, Subfunctor.preimage_comp, hpre, open_range_preimage]
    exact ⟨W B a, heq, fun W' hW' ↦ open_preimage_injective e W' (W B a)
      (hW'.trans heq.symm), htest B a⟩
  · intro B C a g W' hW'
    rw [Subfunctor.preimage_comp, hW', open_range_preimage]
  · intro B b E e v h
    have hv : v ∈ (Subfunctor.range i).obj (op E) := by
      rw [← hpre]
      change p.app (op E) v ∈ G.obj (op E)
      have hw := ConcreteCategory.congr_hom (congr_app h.w (op E)) (𝟙 E)
      change p.app (op E) v = _ at hw
      rw [hw]
      exact (b.app (op E) e).property
    obtain ⟨w, hw⟩ := hv
    have hw' : w ≫ openChartInclusion V O = v := hw
    refine ⟨w, hw', ?_⟩
    have hfactor : yoneda.map e ≫ b = yoneda.map w ≫ pO := by
      apply (cancel_mono G.ι).mp
      calc
        (yoneda.map e ≫ b) ≫ G.ι = yoneda.map v ≫ p := h.w.symm
        _ = (yoneda.map w ≫ i) ≫ p := by
          dsimp [i]
          rw [← yoneda.map_comp, hw']
        _ = (yoneda.map w ≫ pO) ≫ G.ι :=
          (Category.assoc _ _ _).trans
            ((congr_arg (fun k ↦ yoneda.map w ≫ k) hpO.symm).trans
              (Category.assoc _ _ _).symm)
    rw [← Category.assoc, hfactor, Category.assoc, hr]
  · intro Z' r₁ r₂ heq
    exact hdetect _ ((isSheaf_iff_isSheaf_of_type _ _).mp Z'.obj.property)
      r₁ r₂ heq
  · intro T x z heq
    apply hdetect _ (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
    change pO ≫ r ≫ z = pO ≫ G.ι ≫ x
    calc
      pO ≫ r ≫ z = q ≫ z := by rw [← Category.assoc, hr]
      _ = i ≫ p ≫ x := heq
      _ = pO ≫ G.ι ≫ x :=
        ((Category.assoc _ _ _).symm.trans
          (congr_arg (fun k ↦ k ≫ x) hpO.symm)).trans (Category.assoc _ _ _)

end AlgebraicGeometry.AlgebraicSpace
