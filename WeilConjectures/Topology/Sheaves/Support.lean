/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque

/-!
# Sections of abelian sheaves, supports and the sheaves `ℤ_U`

Let `X` be a topological space. This file collects section-level facts about sheaves of abelian
groups on `X`:

* a monomorphism of sheaves is injective on sections, and an epimorphism is locally surjective on
  sections; a section which is locally zero is zero;
* a sheaf `F` is *supported on* a set `Z` if its sections over opens disjoint from `Z` vanish;
  this property passes to subsheaves and quotients;
* every section of the sheaf `ℤ_U = TopCat.Sheaf.freeYoneda.obj U` is locally an integer
  multiple of the canonical generator of `ℤ_U` or zero. Consequently a quotient of `ℤ_U` whose
  generator vanishes on `U ⊓ A` is supported on the complement of `A`.

## Main definitions

- `TopCat.Sheaf.IsSupportedOn`: the sections of `F` over opens disjoint from `Z` vanish.
- `TopCat.Sheaf.freeYonedaGen`: the canonical generator of `ℤ_U` over `U`.

## Main statements

- `TopCat.Sheaf.exists_map_eq_of_epi`: epimorphisms are locally surjective on sections.
- `TopCat.Sheaf.IsSupportedOn.of_epi`, `TopCat.Sheaf.IsSupportedOn.of_mono`: supports of
  quotients and subsheaves.
- `TopCat.Sheaf.isSupportedOn_compl_of_epi`: a quotient of `ℤ_U` whose generator vanishes on
  `U ⊓ A` is supported on `Aᶜ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section Sections

variable {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

@[simp]
lemma comp_hom_app_apply {H : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (f : F ⟶ G) (g : G ⟶ H) (U : (Opens X)ᵒᵖ) (x : F.obj.obj U) :
    (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) :=
  rfl

/-- A monomorphism of abelian sheaves is injective on sections. -/
lemma injective_app_of_mono (f : F ⟶ G) [Mono f] (U : (Opens X)ᵒᵖ) :
    Function.Injective (f.hom.app U) := by
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have : Mono (f.hom.app U) := (NatTrans.mono_iff_mono_app f.hom).1 inferInstance U
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- A morphism of abelian sheaves which is injective on sections is a monomorphism. -/
lemma mono_of_injective_app (f : F ⟶ G) (hf : ∀ U, Function.Injective (f.hom.app U)) :
    Mono f := by
  have (U : (Opens X)ᵒᵖ) : Mono (f.hom.app U) := (AddCommGrpCat.mono_iff_injective _).2 (hf U)
  have : Mono f.hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

/-- A morphism of abelian sheaves which is surjective on sections is an epimorphism. -/
lemma epi_of_surjective_app (f : F ⟶ G) (hf : ∀ U, Function.Surjective (f.hom.app U)) :
    Epi f := by
  have (U : (Opens X)ᵒᵖ) : Epi (f.hom.app U) := (AddCommGrpCat.epi_iff_surjective _).2 (hf U)
  have : Epi f.hom := NatTrans.epi_of_epi_app _
  exact (sheafToPresheaf _ _).epi_of_epi_map this

/-- **Epimorphisms of abelian sheaves are locally surjective.** -/
lemma exists_map_eq_of_epi (f : F ⟶ G) [Epi f] {V : Opens X} (t : G.obj.obj (op V)) {x : X}
    (hx : x ∈ V) : ∃ (W : Opens X) (hWV : W ≤ V) (_ : x ∈ W) (s : F.obj.obj (op W)),
      f.hom.app (op W) s = G.obj.map (homOfLE hWV).op t := by
  have : CategoryTheory.Sheaf.IsLocallySurjective f :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (φ := f)).2 inferInstance
  obtain ⟨W, i, ⟨s, hs⟩, hxW⟩ := (Opens.mem_grothendieckTopology X).1
    (CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X) f.hom t) x hx
  refine ⟨W, i.le, hxW, s, ?_⟩
  rw [hs]
  rfl

/-- A section of an abelian sheaf which is locally zero is zero. -/
lemma eq_zero_of_locally (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {V : Opens X} (s : F.obj.obj (op V))
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V) (_ : x ∈ W), F.obj.map (homOfLE hWV).op s = 0) :
    s = 0 := by
  choose W hWV hxW hW using h
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : V ↦ W x.1 x.2) V
    (fun x ↦ homOfLE (hWV x.1 x.2)) (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxW y hy⟩) s 0
    fun x ↦ ?_
  rw [map_zero]
  exact hW x.1 x.2

/-- An abelian sheaf all of whose sections vanish is a zero object. -/
lemma isZero_of_forall_eq_zero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (h : ∀ (V : Opens X) (s : F.obj.obj (op V)), s = 0) : IsZero F := by
  refine (IsZero.iff_id_eq_zero F).2 (CategoryTheory.Sheaf.hom_ext ?_)
  ext V s
  simpa using h V.unop s

end Sections

section Support

/-- An abelian sheaf `F` is *supported on* the set `Z` if its sections over opens disjoint from
`Z` vanish. -/
def IsSupportedOn (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (Z : Set X) : Prop :=
  ∀ (V : Opens X), Disjoint (V : Set X) Z → ∀ s : F.obj.obj (op V), s = 0

variable {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {Z Z' : Set X}

lemma IsSupportedOn.mono (hF : IsSupportedOn F Z) (h : Z ⊆ Z') : IsSupportedOn F Z' :=
  fun V hV ↦ hF V (hV.mono_right h)

/-- A subsheaf of a sheaf supported on `Z` is supported on `Z`. -/
lemma IsSupportedOn.of_mono (f : F ⟶ G) [Mono f] (hG : IsSupportedOn G Z) :
    IsSupportedOn F Z :=
  fun V hV _ ↦ injective_app_of_mono f (op V) ((hG V hV _).trans (map_zero _).symm)

/-- A quotient of a sheaf supported on `Z` is supported on `Z`. -/
lemma IsSupportedOn.of_epi (f : F ⟶ G) [Epi f] (hF : IsSupportedOn F Z) :
    IsSupportedOn G Z := by
  intro V hV t
  refine eq_zero_of_locally G t fun x hx ↦ ?_
  obtain ⟨W, hWV, hxW, s, hs⟩ := exists_map_eq_of_epi f t hx
  refine ⟨W, hWV, hxW, ?_⟩
  rw [← hs, hF W (hV.mono_left hWV) s, map_zero]

lemma IsSupportedOn.of_iso (e : F ≅ G) (hF : IsSupportedOn F Z) : IsSupportedOn G Z :=
  hF.of_epi e.hom

/-- A sheaf supported on the empty set is zero. -/
lemma IsSupportedOn.isZero (hF : IsSupportedOn F ∅) : IsZero F :=
  isZero_of_forall_eq_zero F fun V ↦ hF V (Set.disjoint_empty _)

end Support

section FreeYoneda

/-- The canonical generator of `ℤ_U = TopCat.Sheaf.freeYoneda.obj U` over `U`. -/
noncomputable def freeYonedaGen (U : Opens X) : (freeYoneda.obj U).obj.obj (op U) :=
  freeYonedaHomEquiv (freeYoneda.obj U) U (𝟙 _)

variable {E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

lemma freeYonedaHomEquiv_comp {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} {W : Opens X} (b : freeYoneda.obj W ⟶ F) (g : F ⟶ E) :
    freeYonedaHomEquiv E W (b ≫ g) = g.hom.app (op W) (freeYonedaHomEquiv F W b) := by
  change yonedaEquiv (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _
        (b ≫ g))) = g.hom.app (op W) (yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _
        b)))
  erw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    yonedaEquiv_comp]

/-- The section corresponding to a morphism `ℤ_U ⟶ E` is the image of the generator. -/
lemma freeYonedaHomEquiv_apply {U : Opens X} (f : freeYoneda.obj U ⟶ E) :
    freeYonedaHomEquiv E U f = f.hom.app (op U) (freeYonedaGen U) := by
  rw [freeYonedaGen, ← freeYonedaHomEquiv_comp, Category.id_comp]

lemma freeYonedaGen_eq (U : Opens X) :
    freeYonedaGen U = (toSheafify (Opens.grothendieckTopology X)
      (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U)) :=
  rfl

/-- Every element of the free abelian group on a subsingleton type is a multiple of a generator. -/
lemma _root_.FreeAbelianGroup.exists_eq_zsmul_of {α : Type*} [Subsingleton α] (a : α)
    (τ : FreeAbelianGroup α) : ∃ n : ℤ, τ = n • FreeAbelianGroup.of a := by
  induction τ using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of x => exact ⟨1, by rw [Subsingleton.elim x a, one_smul]⟩
  | neg x ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨-n, by rw [hn, neg_smul]⟩
  | add x y hx hy =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := hy
    exact ⟨n + m, by rw [add_smul]⟩

lemma _root_.FreeAbelianGroup.eq_zero_of_isEmpty {α : Type*} [IsEmpty α]
    (τ : FreeAbelianGroup α) : τ = 0 := by
  induction τ using FreeAbelianGroup.induction_on with
  | zero => rfl
  | of x => exact isEmptyElim x
  | neg x ih => rw [ih, neg_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

lemma map_map_apply (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : F.obj.obj (op U)) :
    F.obj.map (homOfLE h₂).op (F.obj.map (homOfLE h₁).op s) =
      F.obj.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Local structure of `ℤ_U`.** Every section of `ℤ_U` is, locally, an integer multiple of the
restriction of the generator, or zero. -/
lemma exists_freeYoneda_eq (U : Opens X) {V : Opens X} (σ : (freeYoneda.obj U).obj.obj (op V))
    {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (hWV : W ≤ V) (_ : x ∈ W),
      (∃ (hWU : W ≤ U) (n : ℤ), (freeYoneda.obj U).obj.map (homOfLE hWV).op σ =
        n • (freeYoneda.obj U).obj.map (homOfLE hWU).op (freeYonedaGen U)) ∨
      (freeYoneda.obj U).obj.map (homOfLE hWV).op σ = 0 := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := yoneda.obj U ⋙ AddCommGrpCat.free
  obtain ⟨W, i, ⟨τ, hτ⟩, hxW⟩ := (Opens.mem_grothendieckTopology X).1
    (CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) P) σ) x hx
  have hτ' : (freeYoneda.obj U).obj.map (homOfLE i.le).op σ =
      (toSheafify (Opens.grothendieckTopology X) P).app (op W) τ := hτ.symm
  refine ⟨W, i.le, hxW, ?_⟩
  rw [hτ']
  by_cases hWU : W ≤ U
  · left
    have : Subsingleton (W ⟶ U) := inferInstance
    obtain ⟨n, hn⟩ := FreeAbelianGroup.exists_eq_zsmul_of (homOfLE hWU) τ
    refine ⟨hWU, n, ?_⟩
    rw [hn]
    refine (map_zsmul ((toSheafify (Opens.grothendieckTopology X) P).app (op W)).hom n
      (FreeAbelianGroup.of (homOfLE hWU))).trans ?_
    rw [freeYonedaGen_eq]
    congr 1
    have h := NatTrans.naturality_apply (toSheafify (Opens.grothendieckTopology X) P)
      (homOfLE hWU).op (FreeAbelianGroup.of (𝟙 U))
    refine Eq.trans ?_ h
    rfl
  · right
    have : IsEmpty (W ⟶ U) := ⟨fun f ↦ hWU f.le⟩
    rw [FreeAbelianGroup.eq_zero_of_isEmpty τ]
    exact map_zero ((toSheafify (Opens.grothendieckTopology X) P).app (op W)).hom

/-- **Supports of quotients of `ℤ_U`.** Let `π : ℤ_U ⟶ E` be an epimorphism whose generator
vanishes on `U ⊓ A`. Then `E` is supported on the complement of `A`. -/
lemma isSupportedOn_compl_of_epi {U : Opens X} (π : freeYoneda.obj U ⟶ E) [Epi π]
    (A : Opens X)
    (h : E.obj.map (homOfLE (inf_le_left : U ⊓ A ≤ U)).op (freeYonedaHomEquiv E U π) = 0) :
    IsSupportedOn E (A : Set X)ᶜ := by
  intro V hV t
  have hVA : V ≤ A := fun y hy ↦ by
    by_contra hyA
    exact Set.disjoint_left.1 hV hy hyA
  refine eq_zero_of_locally E t fun x hx ↦ ?_
  obtain ⟨W, hWV, hxW, σ, hσ⟩ := exists_map_eq_of_epi π t hx
  obtain ⟨W', hW'W, hxW', hW'⟩ := exists_freeYoneda_eq U σ hxW
  refine ⟨W', hW'W.trans hWV, hxW', ?_⟩
  rw [← map_map_apply E hWV hW'W, ← hσ, ← NatTrans.naturality_apply]
  rcases hW' with ⟨hW'U, n, hn⟩ | hn
  · change π.hom.app _ ((freeYoneda.obj U).obj.map (homOfLE hW'W).op σ) = 0
    rw [hn, map_zsmul, NatTrans.naturality_apply, ← freeYonedaHomEquiv_apply]
    have hle : W' ≤ U ⊓ A := le_inf hW'U ((hW'W.trans hWV).trans hVA)
    rw [show (homOfLE hW'U) = homOfLE hle ≫ homOfLE inf_le_left from rfl, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply, h, map_zero, smul_zero]
  · change π.hom.app _ ((freeYoneda.obj U).obj.map (homOfLE hW'W).op σ) = 0
    rw [hn, map_zero]

end FreeYoneda

end TopCat.Sheaf
