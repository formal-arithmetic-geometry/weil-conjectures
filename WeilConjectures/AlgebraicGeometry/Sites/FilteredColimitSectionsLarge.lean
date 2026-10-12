/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections

/-!
# Sections over quasi-compact objects commute with large filtered colimits

The results of `WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections`, for filtered
diagrams indexed by categories in `Type (u + 1)` instead of `Type u`: this is the size of the
coproducts of étale sheaves of `ModuleCat.{u + 1} Λ`-modules which Brown representability
quantifies over. The proofs are the same.

## Main statements

- `AlgebraicGeometry.Scheme.isColimitSheafSectionsMapCoconeLarge`: sections over a quasi-compact
  quasi-separated étale `X`-scheme commute with filtered colimits indexed by `Type (u + 1)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] {K : Type (u + 1)} [SmallCategory K]
  [IsFiltered K] {F : K ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}

omit [IsFiltered K] in
/-- The presheaf colimit of a diagram of sheaves, with its comparison map to the sheaf colimit:
the comparison is locally surjective and locally injective, being the sheafification map. -/
private lemma exists_presheafColimitLarge (hc : IsColimit c) :
    ∃ (E : Cocone (F ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      Presheaf.IsLocallySurjective X.smallEtaleTopology φ ∧
      Presheaf.IsLocallyInjective X.smallEtaleTopology φ ∧
      ∀ k, E.ι.app k ≫ φ = (c.ι.app k).hom := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let hE : IsColimit E := colimit.isColimit _
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  let e' : sheafify X.smallEtaleTopology E.pt ≅ c.pt.obj := (sheafToPresheaf _ _).mapIso e
  refine ⟨E, hE, toSheafify X.smallEtaleTopology E.pt ≫ e'.hom, ?_, ?_, fun k ↦ ?_⟩
  · infer_instance
  · infer_instance
  · have h := congrArg (fun f ↦ f.hom) (IsColimit.comp_coconePointUniqueUpToIso_hom
      (Sheaf.isColimitSheafifyCocone E hE) hc k)
    rw [← h]
    erw [ObjectProperty.FullSubcategory.comp_hom, Sheaf.sheafifyCocone_ι_app_val]
    exact (Category.assoc _ _ _).symm

/-- **Sections of a filtered colimit are locally lifted.** Every section of `c.pt` over `W` is,
on the members of a covering sieve of `W`, the image of a section of some `F k`. -/
private lemma exists_mem_forall_exists_app_eqLarge (hc : IsColimit c) {W : X.Etale}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k : K) (t : (F.obj k).obj.obj (op V)),
        (c.ι.app k).hom.app (op V) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, -, hφ⟩ := exists_presheafColimitLarge hc
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  obtain ⟨k, t, rfl⟩ := Concrete.isColimit_exists_rep _ hEV p
  refine ⟨k, t, Eq.trans ?_ hp⟩
  rw [← hφ k]
  rfl

/-- **Sections of a filtered colimit are locally separated.** Two sections of `F k` over `W`
with the same image in `c.pt` agree, on the members of a covering sieve of `W`, in some later
`F k'`. -/
private lemma exists_mem_forall_exists_map_eqLarge (hc : IsColimit c) {W : X.Etale} {k : K}
    (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k' : K) (a : k ⟶ k'),
        (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t) =
          (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t') := by
  obtain ⟨E, hE, φ, -, hi, hφ⟩ := exists_presheafColimitLarge hc
  have h' : φ.app (op W) ((E.ι.app k).app (op W) t) =
      φ.app (op W) ((E.ι.app k).app (op W) t') := by
    change (E.ι.app k ≫ φ).app _ t = (E.ι.app k ≫ φ).app _ t'
    rw [hφ]
    exact h
  refine ⟨_, Presheaf.equalizerSieve_mem _ φ _ _ h', fun V f hf ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  have hf' : (E.ι.app k).app (op V) ((F.obj k).obj.map f.op t) =
      (E.ι.app k).app (op V) ((F.obj k).obj.map f.op t') := by
    have hn := (E.ι.app k).naturality f.op
    have e1 := ConcreteCategory.congr_hom hn t
    have e2 := ConcreteCategory.congr_hom hn t'
    simp only [ConcreteCategory.comp_apply] at e1 e2
    erw [e1, e2]
    exact hf
  obtain ⟨k', a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hEV _ _ hf'
  refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
  let q := IsFiltered.coeqHom a b
  calc (F.map (a ≫ q)).hom.app (op V) ((F.obj k).obj.map f.op t)
      = (F.map q).hom.app (op V) ((F.map a).hom.app (op V) ((F.obj k).obj.map f.op t)) := by
        rw [F.map_comp]; rfl
    _ = (F.map q).hom.app (op V) ((F.map b).hom.app (op V) ((F.obj k).obj.map f.op t')) :=
        congrArg _ hab
    _ = (F.map (b ≫ q)).hom.app (op V) ((F.obj k).obj.map f.op t') := by
        rw [F.map_comp]; rfl
    _ = _ := by rw [← IsFiltered.coeq_condition a b]

omit [IsFiltered K] in
/-- A finite family of morphisms `aᵢ : k ⟶ kᵢ` out of an object of a filtered category extends to
a cocone: there are `A : k ⟶ k'` and `bᵢ : kᵢ ⟶ k'` with `aᵢ ≫ bᵢ = A`. -/
private lemma exists_comp_eq_of_finiteLarge [IsFilteredOrEmpty K] {k : K}
    {ι : Type*} [Finite ι] {k₁ : ι → K} (a : ∀ i, k ⟶ k₁ i) :
    ∃ (k' : K) (A : k ⟶ k') (b : ∀ i, k₁ i ⟶ k'), ∀ i, a i ≫ b i = A := by
  classical
  have := Fintype.ofFinite ι
  have : Nonempty K := ⟨k⟩
  have : IsFiltered K := { }
  let O : Finset K := insert k (Finset.univ.image k₁)
  have hk : k ∈ O := Finset.mem_insert_self _ _
  have hk₁ (i : ι) : k₁ i ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun i ↦ ⟨k, k₁ i, hk, hk₁ i, a i⟩
  exact ⟨IsFiltered.sup O H, IsFiltered.toSup O H hk, fun i ↦ IsFiltered.toSup O H (hk₁ i),
    fun i ↦ IsFiltered.toSup_commutes O H hk (hk₁ i)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

/-- **Sections over a quasi-compact `W` of a filtered colimit are separated at a finite stage.**
Two sections of `F k` over `W` with the same image in `c.pt` agree in some later `F k'`. -/
theorem exists_map_eq_of_isColimitLarge (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    {k : K} (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = (F.map a).hom.app (op W) t' := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_map_eqLarge hc t t' h
  obtain ⟨n, U, g, hRg, -, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
  choose k₁ a₁ ha₁ using fun i ↦ hloc (g i) (hRg i)
  obtain ⟨k', A, b, hb⟩ := exists_comp_eq_of_finiteLarge a₁
  refine ⟨k', A, (isSheafFor_ofArrows_moduleCat (F.obj k') g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change (F.obj k').obj.map (g i).op _ = (F.obj k').obj.map (g i).op _
  have hnat (z : (F.obj k).obj.obj (op W)) : (F.obj k').obj.map (g i).op ((F.map A).hom.app _ z) =
      (F.map (b i)).hom.app _ ((F.map (a₁ i)).hom.app _ ((F.obj k).obj.map (g i).op z)) := by
    rw [← hb i, F.map_comp]
    exact (NatTrans.naturality_apply (F.map (a₁ i) ≫ F.map (b i)).hom (g i).op z).symm
  rw [hnat, hnat, ha₁ i]

/-- A finite family of objects of a filtered category has a cocone. -/
private lemma exists_cocone_of_finiteLarge {ι : Type*} [Finite ι]
    (k₁ : ι → K) : ∃ k : K, Nonempty (∀ i, k₁ i ⟶ k) := by
  classical
  have := Fintype.ofFinite ι
  let O : Finset K := Finset.univ.image k₁
  exact ⟨IsFiltered.sup O ∅, ⟨fun i ↦ IsFiltered.toSup O ∅
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩⟩

/-- **Sections over a quasi-compact quasi-separated `W` of a filtered colimit come from a finite
stage.** Every section of `c.pt` over `W` is the image of a section of some `F k` (Stacks 0738).
-/
theorem exists_app_eq_of_isColimitLarge (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (k : K) (t : (F.obj k).obj.obj (op W)), (c.ι.app k).hom.app (op W) t = s := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_app_eqLarge hc s
  obtain ⟨n, U, g, hRg, hU, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
  choose k₁ t₁ ht₁ using fun i ↦ hloc (g i) (hRg i)
  obtain ⟨k, ⟨b⟩⟩ := exists_cocone_of_finiteLarge k₁
  let t₂ (i : Fin n) : (F.obj k).obj.obj (op (U i)) := (F.map (b i)).hom.app _ (t₁ i)
  have ht₂ (i : Fin n) : (c.ι.app k).hom.app _ (t₂ i) = c.pt.obj.map (g i).op s := by
    rw [← ht₁ i, ← c.w (b i)]
    rfl
  -- on the overlaps the local lifts agree at a later stage
  have hpair (ij : Fin n × Fin n) : ∃ (k' : K) (a : k ⟶ k'),
      (F.map a).hom.app _ ((F.obj k).obj.map (pullback.fst (g ij.1) (g ij.2)).op (t₂ ij.1)) =
        (F.map a).hom.app _ ((F.obj k).obj.map (pullback.snd (g ij.1) (g ij.2)).op
          (t₂ ij.2)) := by
    have := hU ij.1
    have := hU ij.2
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback (g ij.1) (g ij.2)
    refine exists_map_eq_of_isColimitLarge hc _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht₂, ht₂]
    change c.pt.obj.map _ (c.pt.obj.map _ s) = c.pt.obj.map _ (c.pt.obj.map _ s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition]
  choose k₂ a₂ ha₂ using hpair
  obtain ⟨k', A, b', hb'⟩ := exists_comp_eq_of_finiteLarge a₂
  let z (i : Fin n) : (F.obj k').obj.obj (op (U i)) := (F.map A).hom.app _ (t₂ i)
  have hz (i : Fin n) : (c.ι.app k').hom.app _ (z i) = c.pt.obj.map (g i).op s := by
    rw [← ht₂ i, ← c.w A]
    rfl
  have hA (ij : Fin n × Fin n) :
      (F.obj k').obj.map (pullback.fst (g ij.1) (g ij.2)).op (z ij.1) =
        (F.obj k').obj.map (pullback.snd (g ij.1) (g ij.2)).op (z ij.2) := by
    have e (j : Fin n) (r : pullback (g ij.1) (g ij.2) ⟶ U j) :
        (F.obj k').obj.map r.op (z j) =
          (F.map (b' ij)).hom.app _
            ((F.map (a₂ ij)).hom.app _ ((F.obj k).obj.map r.op (t₂ j))) := by
      change (F.obj k').obj.map r.op ((F.map A).hom.app _ (t₂ j)) = _
      rw [← hb' ij, F.map_comp]
      exact (NatTrans.naturality_apply (F.map (a₂ ij) ≫ F.map (b' ij)).hom r.op (t₂ j)).symm
    rw [e, e, ha₂ ij]
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows_moduleCat (F.obj k') g hcov)) z fun i j ↦ hA (i, j)
  refine ⟨k', y, (isSheafFor_ofArrows_moduleCat c.pt g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← hz i]
  erw [← hy i]
  exact (NatTrans.naturality_apply (c.ι.app k').hom (g i).op y).symm

/-- **Sections over a quasi-compact quasi-separated `W` commute with filtered colimits** (Stacks
0738): the image of a colimit cocone of a filtered diagram of étale sheaves of
`Λ`-modules under the sections functor over `W` is a colimit cocone. -/
noncomputable def isColimitSheafSectionsMapCoconeLarge (hc : IsColimit c) (W : X.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op W)).mapCocone
      c) := by
  have : ReflectsColimit (F ⋙ (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op W))
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) := reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun s ↦ ?_) (fun k t t' h ↦ ?_)
  · obtain ⟨k, t, ht⟩ := exists_app_eq_of_isColimitLarge hc s
    exact ⟨k, t, ht.symm⟩
  · exact exists_map_eq_of_isColimitLarge hc t t' h

/-- The sections functor over a quasi-compact quasi-separated étale `X`-scheme preserves
colimits of filtered diagrams. -/
instance preservesFilteredColimitsOfSize_sheafSectionsLarge (W : X.Etale) [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op W)) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {_} ↦ ⟨fun {_} hc ↦ ⟨isColimitSheafSectionsMapCoconeLarge hc W⟩⟩⟩

end AlgebraicGeometry.Scheme
