/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.OpensCone
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Closed immersions into the limit descend to a finite stage

A morphism to a cofiltered limit of schemes with affine transition maps which is a closed
immersion after composing with a projection descends to a closed immersion at a finite stage
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_comp_π`,
`AlgebraicGeometry.Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section ClosedImmersionDescent

/-!
## Closed immersions spread out from a limit

We prove Stacks Project Tag 081B (1): a closed immersion into the limit of a cofiltered
system with affine transition morphisms, from a scheme locally of finite type over the base,
is already a closed immersion into the stages from some index on
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_comp_π`). Combined with the descent of
quasi-compact opens (Stacks Project Tag 01Z4), a quasi-compact open of the limit is closed in a
quasi-compact open of some stage
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit`).
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

set_option backward.isDefEq.respectTransparency false in
/-- **Closed immersions spread out from a limit, affine case.** Let `{Dᵢ}` be a cofiltered
system of affine schemes and `g : Y ⟶ lim Dᵢ` a closed immersion such that `Y` is locally of
finite type over an affine scheme `W` receiving a morphism from some `D_{i₀}`. Then
`Y ⟶ D_j` is a closed immersion for some `j ⟶ i₀`: finitely many generators of `Γ(Y)` over
`Γ(W)` lift to a common stage, whose ring of sections then surjects onto `Γ(Y)`. -/
lemma Scheme.exists_isClosedImmersion_comp_π_of_isAffine [IsCofiltered I]
    [∀ i, IsAffine (D.obj i)] (hc : IsLimit c) {Y W : Scheme.{u}} [IsAffine W]
    (g : Y ⟶ c.pt) [IsClosedImmersion g] {i₀ : I} (q : D.obj i₀ ⟶ W)
    [LocallyOfFiniteType (g ≫ c.π.app i₀ ≫ q)] :
    ∃ (j : I) (_ : j ⟶ i₀), IsClosedImmersion (g ≫ c.π.app j) := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffine Y := isAffine_of_isAffineHom g
  have hft : (g ≫ c.π.app i₀ ≫ q).appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := (g ≫ c.π.app i₀ ≫ q).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  have hlift (y : Γ(Y, ⊤)) :
      ∃ (i : I) (t : Γ(D.obj i, ⊤)), (g ≫ c.π.app i).appTop t = y := by
    obtain ⟨x, rfl⟩ := g.app_surjective ⊤ (isAffineOpen_top _) y
    obtain ⟨i, t, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit D c hc x
    exact ⟨i, t, by simp⟩
  choose i t ht using hlift
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (insert i₀ (s.image i))
  have e₀ : j ⟶ i₀ := (hj (Finset.mem_insert_self _ _)).some
  have e (y : Γ(Y, ⊤)) (hy : y ∈ s) : j ⟶ i y :=
    (hj (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))).some
  refine ⟨j, e₀, IsClosedImmersion.of_surjective_of_isAffine _ fun y ↦ ?_⟩
  -- the image of `Γ(D_j)` is a `Γ(W)`-subalgebra containing the chosen generators
  let R : Subalgebra Γ(W, ⊤) Γ(Y, ⊤) :=
    { (g ≫ c.π.app j).appTop.hom.range with
      algebraMap_mem' := fun r ↦ ⟨(D.map e₀ ≫ q).appTop r, (by
        have h : (g ≫ c.π.app j) ≫ D.map e₀ ≫ q = g ≫ c.π.app i₀ ≫ q := by
          rw [Category.assoc, c.w_assoc]
        change _ = (g ≫ c.π.app i₀ ≫ q).appTop r
        rw [← h, Scheme.Hom.comp_appTop]
        rfl)⟩ }
  have hsR : Algebra.adjoin Γ(W, ⊤) (s : Set Γ(Y, ⊤)) ≤ R := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    refine ⟨(D.map (e y hy)).appTop (t y), ?_⟩
    have h : (g ≫ c.π.app j) ≫ D.map (e y hy) = g ≫ c.π.app (i y) := by
      rw [Category.assoc, c.w]
    calc _ = ((g ≫ c.π.app j) ≫ D.map (e y hy)).appTop (t y) := by
          rw [Scheme.Hom.comp_appTop]; rfl
      _ = y := by rw [h, ht y]
  rw [hs] at hsR
  exact hsR (Algebra.mem_top (x := y))

private lemma isClosedImmersion_morphismRestrict_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (e : a = b)
    {U U' : Y.Opens} (e' : U = U') :
    IsClosedImmersion (a ∣_ U) ↔ IsClosedImmersion (b ∣_ U') := by
  subst e e'; rfl

variable {D c}

/-- If `Y ⟶ lim Dᵢ ⟶ D_j` is a closed immersion, then so is `Y ⟶ lim Dᵢ ⟶ D_k` for every
`k ⟶ j`, the transition morphisms being affine, hence separated. -/
lemma Scheme.isClosedImmersion_comp_π_of_comp {Y : Scheme.{u}} (g : Y ⟶ c.pt)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : I} (h : k ⟶ j)
    [IsClosedImmersion (g ≫ c.π.app j)] : IsClosedImmersion (g ≫ c.π.app k) := by
  have : IsClosedImmersion ((g ≫ c.π.app k) ≫ D.map h) := by
    rwa [Category.assoc, c.w]
  exact .of_comp _ (D.map h)

/-- The local version of `AlgebraicGeometry.Scheme.isClosedImmersion_comp_π_of_comp`: being a
closed immersion over the preimage of an open `U ⊆ D_{i₀}` persists to later stages. -/
lemma Scheme.isClosedImmersion_morphismRestrict_comp_π_of_comp {Y : Scheme.{u}}
    (g : Y ⟶ c.pt) [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i₀ j k : I} (f : j ⟶ i₀)
    (h : k ⟶ j) (f' : k ⟶ i₀) (hf : h ≫ f = f') (U : (D.obj i₀).Opens)
    [IsClosedImmersion ((g ≫ c.π.app j) ∣_ (D.map f ⁻¹ᵁ U))] :
    IsClosedImmersion ((g ≫ c.π.app k) ∣_ (D.map f' ⁻¹ᵁ U)) := by
  subst hf
  have : IsClosedImmersion ((g ≫ c.π.app k) ∣_ (D.map h ⁻¹ᵁ (D.map f ⁻¹ᵁ U)) ≫
      D.map h ∣_ (D.map f ⁻¹ᵁ U)) := by
    rw [← morphismRestrict_comp]
    exact (isClosedImmersion_morphismRestrict_congr (by rw [Category.assoc, c.w]) rfl).mpr
      inferInstance
  have : IsClosedImmersion ((g ≫ c.π.app k) ∣_ (D.map h ⁻¹ᵁ (D.map f ⁻¹ᵁ U))) :=
    .of_comp _ (D.map h ∣_ (D.map f ⁻¹ᵁ U))
  exact (isClosedImmersion_morphismRestrict_congr rfl
    (by rw [D.map_comp, Scheme.Hom.comp_preimage])).mpr this

private lemma Scheme.Hom.isClosedImmersion_resLE_congr {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    {V V' : X.Opens} (e : V = V') (h : V ≤ f ⁻¹ᵁ W) (h' : V' ≤ f ⁻¹ᵁ W) :
    IsClosedImmersion (f.resLE W V h) ↔ IsClosedImmersion (f.resLE W V' h') := by
  subst e; rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Closed immersions spread out from a limit, over an affine open.** If `U ⊆ D_{i₀}` is an
affine open mapping into an affine open `W` of `S`, then `Y ⟶ D_j` is a closed immersion over
the preimage of `U` for some `j ⟶ i₀`. This is the affine case applied to the system of the
preimages of `U`, whose limit is the preimage of `U` in `lim Dᵢ`. -/
lemma Scheme.exists_isClosedImmersion_morphismRestrict_comp_π [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) {S Y : Scheme.{u}}
    (g : Y ⟶ c.pt) [IsClosedImmersion g] {i₀ : I} (t : D.obj i₀ ⟶ S)
    [LocallyOfFiniteType (g ≫ c.π.app i₀ ≫ t)] {U : (D.obj i₀).Opens}
    (hU : IsAffineOpen U) {W : S.Opens} (hW : IsAffineOpen W) (hUW : U ≤ t ⁻¹ᵁ W) :
    ∃ (j : I) (f : j ⟶ i₀), IsClosedImmersion ((g ≫ c.π.app j) ∣_ (D.map f ⁻¹ᵁ U)) := by
  have (j : Over i₀) : IsAffine ((opensDiagram D i₀ U).obj j) := hU.preimage _
  have : IsAffine W := hW
  let V := c.π.app i₀ ⁻¹ᵁ U
  let q : (opensDiagram D i₀ U).obj (Over.mk (𝟙 i₀)) ⟶ W :=
    t.resLE W (D.map (𝟙 i₀) ⁻¹ᵁ U) (by simpa using hUW)
  have : LocallyOfFiniteType (g ∣_ V ≫ (opensCone D c i₀ U).π.app (Over.mk (𝟙 i₀)) ≫ q) := by
    have e : (g ∣_ V ≫ (opensCone D c i₀ U).π.app (Over.mk (𝟙 i₀)) ≫ q) ≫ W.ι =
        (g ⁻¹ᵁ V).ι ≫ g ≫ c.π.app i₀ ≫ t := by
      simp [q, V]
    have : LocallyOfFiniteType
        ((g ∣_ V ≫ (opensCone D c i₀ U).π.app (Over.mk (𝟙 i₀)) ≫ q) ≫ W.ι) := by
      rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp _ W.ι
  obtain ⟨j, -, hj⟩ := Scheme.exists_isClosedImmersion_comp_π_of_isAffine _ _
    (isLimitOpensCone D c hc i₀ U) (g ∣_ V) q
  refine ⟨j.left, j.hom, ?_⟩
  rw [← Scheme.Hom.resLE_eq_morphismRestrict] at hj ⊢
  rw [opensCone_π_app, Scheme.Hom.resLE_comp_resLE] at hj
  refine (Scheme.Hom.isClosedImmersion_resLE_congr _ _ ?_ _ _).mp hj
  rw [Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage (c.π.app j.left), c.w]

set_option backward.isDefEq.respectTransparency false in
/-- **Closed immersions spread out from a limit** (Stacks Project Tag 081B, part (1);
blueprint `pqf-lem-limit-immersion-descends`). Let `{Dᵢ}` be a cofiltered system of schemes
with affine transition morphisms and `D_{i₀}` quasi-compact, let `q : D_{i₀} ⟶ S` and let
`g : Y ⟶ lim Dᵢ` be a closed immersion with `Y` locally of finite type over `S`. Then
`Y ⟶ D_k` is a closed immersion for every `k` beyond some `j ⟶ i₀`.

Cover `D_{i₀}` by finitely many affine opens mapping into affine opens of `S`, apply the
affine case over each of them and pass to a common later stage. -/
@[stacks 081B "(1)"]
theorem Scheme.exists_isClosedImmersion_comp_π [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) {S Y : Scheme.{u}}
    (g : Y ⟶ c.pt) [IsClosedImmersion g] {i₀ : I} (t : D.obj i₀ ⟶ S)
    [CompactSpace (D.obj i₀)] [LocallyOfFiniteType (g ≫ c.π.app i₀ ≫ t)] :
    ∃ (j : I) (_ : j ⟶ i₀), ∀ {k : I} (_ : k ⟶ j), IsClosedImmersion (g ≫ c.π.app k) := by
  classical
  have H (x : D.obj i₀) : ∃ (U : (D.obj i₀).Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (j : I) (f : j ⟶ i₀), IsClosedImmersion ((g ≫ c.π.app j) ∣_ (D.map f ⁻¹ᵁ U)) := by
    obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t x)) isOpen_univ
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, hUW⟩ :=
      (D.obj i₀).isBasis_affineOpens.exists_subset_of_mem_open (a := x) hxW
        (t ⁻¹ᵁ W).isOpen
    obtain ⟨j, f, hj⟩ := Scheme.exists_isClosedImmersion_morphismRestrict_comp_π hc g t hU hW hUW
    exact ⟨U, hU, hxU, j, f, hj⟩
  choose U hU hxU j f hj using H
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (U ·) (fun x ↦ (U x).2.mem_nhds (hxU x))
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists (insert i₀ (s.image j)) (by
    exact s.attach.image fun x ↦ ⟨j x.1, i₀, Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ x.2), by simp, f x.1⟩)
  refine ⟨k, fk (by simp), fun {k'} e ↦ ?_⟩
  suffices IsClosedImmersion (g ≫ c.π.app k) from
    Scheme.isClosedImmersion_comp_π_of_comp g e
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (fun x : s ↦ D.map (fk (Finset.mem_insert_self _ _)) ⁻¹ᵁ U x)]
  · intro x
    have h₁ : fk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2)) ≫ f x =
        fk (Finset.mem_insert_self _ _) :=
      hk _ (by simp) (Finset.mem_image.mpr ⟨⟨x, x.2⟩, by simp, by simp⟩)
    have := hj x
    exact Scheme.isClosedImmersion_morphismRestrict_comp_π_of_comp g (f x) _ _ h₁ (U x)
  · refine top_le_iff.mp fun y _ ↦ ?_
    obtain ⟨l, hl, hlU⟩ := Set.mem_iUnion₂.mp
      (hs.ge (Set.mem_univ ((D.map (fk (Finset.mem_insert_self _ _))) y)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨l, hl⟩, hlU⟩

set_option backward.isDefEq.respectTransparency false in
/-- **A quasi-compact open of a limit is closed in an open of some stage.** Let `{Dᵢ}` be a
cofiltered system of quasi-compact schemes with affine transition morphisms and morphisms
`q i : Dᵢ ⟶ S`, and let `ι : X ⟶ lim Dᵢ` be an open immersion from a quasi-compact `X` that is
locally of finite type over `S`. Then there are a stage `i`, a quasi-compact open `U ⊆ Dᵢ` and
a closed immersion `X ⟶ U` lifting `X ⟶ lim Dᵢ ⟶ Dᵢ`.

The image of `X` descends to a quasi-compact open `V₁` of some stage (Stacks Project
Tag 01Z4); `X` is then the limit of the preimages of `V₁`, and the closed immersion spreads
out by Tag 081B. These are Steps 1 and 2 of the proof of blueprint
`thm-pqf-immersion-descent`. -/
theorem Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)] (hc : IsLimit c)
    {X S : Scheme.{u}} (q : ∀ i, D.obj i ⟶ S) (ι : X ⟶ c.pt) [IsOpenImmersion ι]
    [CompactSpace X] [∀ i, LocallyOfFiniteType (ι ≫ c.π.app i ≫ q i)] :
    ∃ (i : I) (U : (D.obj i).Opens) (g : X ⟶ U), IsCompact (U : Set (D.obj i)) ∧
      IsClosedImmersion g ∧ g ≫ U.ι = ι ≫ c.π.app i := by
  obtain ⟨i₁, V₁, hV₁, hV⟩ := exists_preimage_eq D c hc ι.opensRange
    (isCompact_range ι.continuous)
  let g₀ : X ⟶ (opensCone D c i₁ V₁).pt := ι.isoOpensRange.hom ≫ (c.pt.isoOfEq hV.symm).hom
  have hg₀ : g₀ ≫ (c.π.app i₁ ⁻¹ᵁ V₁).ι = ι := by simp [g₀]
  have : CompactSpace ((opensDiagram D i₁ V₁).obj (Over.mk (𝟙 i₁))) :=
    isCompact_iff_compactSpace.mp (by simpa using hV₁)
  let q' : (opensDiagram D i₁ V₁).obj (Over.mk (𝟙 i₁)) ⟶ S :=
    (D.map (𝟙 i₁) ⁻¹ᵁ V₁).ι ≫ q i₁
  have h₁ : (opensCone D c i₁ V₁).π.app (Over.mk (𝟙 i₁)) ≫ (D.map (𝟙 i₁) ⁻¹ᵁ V₁).ι =
      (c.π.app i₁ ⁻¹ᵁ V₁).ι ≫ c.π.app i₁ :=
    opensCone_π_ι D c i₁ V₁ (Over.mk (𝟙 i₁))
  have : LocallyOfFiniteType (g₀ ≫ (opensCone D c i₁ V₁).π.app (Over.mk (𝟙 i₁)) ≫ q') := by
    have e : g₀ ≫ (opensCone D c i₁ V₁).π.app (Over.mk (𝟙 i₁)) ≫ q' = ι ≫ c.π.app i₁ ≫ q i₁ := by
      simp only [q']
      rw [reassoc_of% h₁, reassoc_of% hg₀]
    rw [e]; infer_instance
  obtain ⟨j, -, hj⟩ := Scheme.exists_isClosedImmersion_comp_π (isLimitOpensCone D c hc i₁ V₁)
    g₀ q'
  have := hj (𝟙 j)
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ V₁, g₀ ≫ (opensCone D c i₁ V₁).π.app j,
    (D.map j.hom).isCompact_preimage hV₁, this, ?_⟩
  have h₂ : (opensCone D c i₁ V₁).π.app j ≫ (D.map j.hom ⁻¹ᵁ V₁).ι =
      (c.π.app i₁ ⁻¹ᵁ V₁).ι ≫ c.π.app j.left :=
    opensCone_π_ι D c i₁ V₁ j
  rw [Category.assoc, h₂, reassoc_of% hg₀]

end ClosedImmersionDescent

end AlgebraicGeometry
