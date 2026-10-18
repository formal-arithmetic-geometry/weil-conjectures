/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.SplitEtaleHypercoverLocalCone
public import WeilConjectures.AlgebraicTopology.FreeComplexCone
public import WeilConjectures.CategoryTheory.Sites.SheafifyExactOfLocal

/-!
# The augmented free complex of a split étale hypercover

Let `U` be a split étale hypercover of `X` and `Free : Type ⥤ A` a "free object" functor to a
concrete abelian category (free abelian groups, free modules). We show that the sheafification
of the augmented complex of presheaves `Free[Hom(-, U_•)] ⟶ Free[Hom(-, X)]` is exact, using
the local cones of `AlgebraicGeometry.SplitEtaleHypercover.exists_cone`. For an injective sheaf
`I` we deduce that the complex of sections `I(U_•)` is a resolution of `I(X)`.

## Main results

- `AlgebraicGeometry.SplitEtaleHypercover.quasiIso_augmentation`
- `AlgebraicGeometry.SplitEtaleHypercover.injective_section_cohomology`
-/

@[expose] public section

universe w u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.SplitEtaleHypercover

variable {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X] (U : SplitEtaleHypercover X)

section Points

/-- The simplicial set of `V`-valued points `k ↦ Hom(V, U_k)` (lifted to `Type (w + 1)`). -/
noncomputable abbrev points (V : X.Etale) : SimplicialObject (Type (w + 1)) :=
  U.simplicial ⋙ uliftYoneda.{w + 1} ⋙ (evaluation X.Etaleᵒᵖ (Type (w + 1))).obj (op V)

/-- Restriction of points along `π : T ⟶ V`. -/
noncomputable abbrev pointsRestrict {V T : X.Etale} (π : T ⟶ V) : U.points V ⟶ U.points T :=
  Functor.whiskerLeft (U.simplicial ⋙ uliftYoneda.{w + 1})
    ((evaluation X.Etaleᵒᵖ (Type (w + 1))).map π.op)

/-- The face closure of a set of `m`-simplices with values in `V`: all their iterated faces
and degeneracies in degree `k`. -/
def faceClosure {V : X.Etale} {m : ℕ} (F : Set (V ⟶ U.simplicial _⦋m⦌)) (k : ℕ) :
    Set (V ⟶ U.simplicial _⦋k⦌) :=
  {σ | ∃ τ ∈ F, ∃ θ : ⦋k⦌ ⟶ ⦋m⦌, σ = τ ≫ U.simplicial.map θ.op}

lemma faceClosure_finite {V : X.Etale} {m : ℕ} {F : Set (V ⟶ U.simplicial _⦋m⦌)}
    (hF : F.Finite) (k : ℕ) : (U.faceClosure F k).Finite := by
  have : (U.faceClosure F k) =
      (fun p : (V ⟶ U.simplicial _⦋m⦌) × (⦋k⦌ ⟶ ⦋m⦌) ↦ p.1 ≫ U.simplicial.map p.2.op) ''
        (F ×ˢ Set.univ) := by
    ext σ
    simp only [faceClosure, Set.mem_image, Set.mem_prod, Set.mem_univ,
      and_true, Prod.exists]
    constructor
    · rintro ⟨τ, hτ, θ, rfl⟩
      exact ⟨τ, θ, hτ, rfl⟩
    · rintro ⟨τ, θ, hτ, rfl⟩
      exact ⟨τ, hτ, θ, rfl⟩
  rw [this]
  exact (hF.prod Set.finite_univ).image _

lemma mem_faceClosure_self {V : X.Etale} {m : ℕ} {F : Set (V ⟶ U.simplicial _⦋m⦌)}
    {τ : V ⟶ U.simplicial _⦋m⦌} (hτ : τ ∈ F) : τ ∈ U.faceClosure F m :=
  ⟨τ, hτ, 𝟙 _, by simp⟩

lemma faceClosure_δ {V : X.Etale} {m : ℕ} (F : Set (V ⟶ U.simplicial _⦋m⦌)) (k : ℕ)
    (σ : V ⟶ U.simplicial _⦋k + 1⦌) (hσ : σ ∈ U.faceClosure F (k + 1)) (i : Fin (k + 2)) :
    σ ≫ U.simplicial.δ i ∈ U.faceClosure F k := by
  obtain ⟨τ, hτ, θ, rfl⟩ := hσ
  refine ⟨τ, hτ, SimplexCategory.δ i ≫ θ, ?_⟩
  simp [SimplicialObject.δ]

end Points

section Free

variable {A : Type u'} [Category.{w + 1} A] [Abelian A] {FA : A → A → Type*}
  {CA : A → Type (w + 1)} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w + 1} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]
  (Free : Type (w + 1) ⥤ A)

/-- The presheaf functor `V ↦ Free[Hom(-, V)]`. -/
noncomputable abbrev freePresheaf : X.Etale ⥤ X.Etaleᵒᵖ ⥤ A :=
  uliftYoneda.{w + 1} ⋙ (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) A).obj Free

/-- The (non-augmented) free complex of presheaves of the hypercover. -/
noncomputable abbrev freeComplex : ChainComplex (X.Etaleᵒᵖ ⥤ A) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (U.simplicial ⋙ freePresheaf Free)

lemma freeComplex_d_app (n : ℕ) (V : X.Etale) :
    ((U.freeComplex Free).d (n + 1) n).app (op V) =
      ((AlgebraicTopology.alternatingFaceMapComplex A).obj (U.points V ⋙ Free)).d (n + 1) n := by
  simp only [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, NatTrans.app_sum, NatTrans.app_zsmul]
  rfl

variable (hsub : ∀ {X Y : A} (f g : X ⟶ Y) (x : ToType X), (f - g) x = f x - g x)
  (hfin : ∀ (S : Type (w + 1)) (x : ToType (Free.obj S)), ∃ F : Set S, F.Finite ∧
    x ∈ Set.range (Free.map (↾(Subtype.val : F → S))))

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- A single surjective étale map generates a covering sieve. -/
lemma ofArrows_unit_mem {V T : X.Etale} (π : T ⟶ V) (hπ : Surjective π.left) :
    Sieve.ofArrows (fun _ : Unit ↦ T) (fun _ ↦ π) ∈ X.smallEtaleTopology V := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.iUnion_const]
  exact Set.range_eq_univ.2 hπ.surj

include hsub hfin in
/-- In positive degrees, cycles of the free complex are locally boundaries. -/
lemma imageSieve_freeComplex_d_mem (n : ℕ) (V : X.Etale)
    (x : ToType (((U.freeComplex Free).X (n + 1)).obj (op V)))
    (hx : ((U.freeComplex Free).d (n + 1) n).app (op V) x = 0) :
    Presheaf.imageSieve ((U.freeComplex Free).d (n + 2) (n + 1)) x ∈
      X.smallEtaleTopology V := by
  obtain ⟨F₀, hF₀, hxF⟩ := hfin _ x
  let F : ∀ k, Set (V ⟶ U.simplicial _⦋k⦌) :=
    fun k ↦ U.faceClosure (ULift.up ⁻¹' F₀ : Set (V ⟶ U.simplicial _⦋n + 1⦌)) k
  have hF : ∀ k, (F k).Finite := fun k ↦
    U.faceClosure_finite (hF₀.preimage ULift.up_injective.injOn) k
  obtain ⟨T', π, v, h, hπ, hc₁, -, hc₃⟩ :=
    exists_cone F hF (fun k τ hτ i ↦ U.faceClosure_δ _ k τ hτ i) (n + 2)
  have hmem : ∀ τ ∈ F₀, τ.down ∈ F (n + 1) := fun τ hτ ↦ U.mem_faceClosure_self hτ
  rw [freeComplex_d_app] at hx
  have key := AlgebraicTopology.FreeComplexCone.d_map_succ Free (U.pointsRestrict π) hsub F₀
    (fun τ ↦ ULift.up (h (n + 1) τ.down)) (fun τ ↦ ULift.up (h n τ.down))
    (fun τ hτ ↦ congrArg ULift.up (hc₁ (n + 1) (by omega) τ.down (hmem τ hτ)))
    (fun τ hτ i ↦ congrArg ULift.up (hc₃ n (by omega) τ.down (hmem τ hτ) i)) x hxF hx
  refine X.smallEtaleTopology.superset_covering ?_ (ofArrows_unit_mem π hπ)
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  refine ⟨Free.map (↾fun τ ↦ ULift.up (h (n + 1) τ.down)) x, ?_⟩
  rw [freeComplex_d_app]
  exact key

include hsub hfin in
/-- In degree `0`, chains with vanishing augmentation are locally boundaries. -/
lemma imageSieve_freeComplex_d_zero_mem (V : X.Etale)
    (x : ToType (((U.freeComplex Free).X 0).obj (op V)))
    (hx : ((freePresheaf Free).map (terminal.from (U.simplicial _⦋0⦌))).app (op V) x = 0) :
    Presheaf.imageSieve ((U.freeComplex Free).d 1 0) x ∈ X.smallEtaleTopology V := by
  obtain ⟨F₀, hF₀, hxF⟩ := hfin _ x
  let F : ∀ k, Set (V ⟶ U.simplicial _⦋k⦌) :=
    fun k ↦ U.faceClosure (ULift.up ⁻¹' F₀ : Set (V ⟶ U.simplicial _⦋0⦌)) k
  have hF : ∀ k, (F k).Finite := fun k ↦
    U.faceClosure_finite (hF₀.preimage ULift.up_injective.injOn) k
  obtain ⟨T', π, v, h, hπ, hc₁, hc₂, -⟩ :=
    exists_cone F hF (fun k τ hτ i ↦ U.faceClosure_δ _ k τ hτ i) 1
  have hmem : ∀ τ ∈ F₀, τ.down ∈ F 0 := fun τ hτ ↦ U.mem_faceClosure_self hτ
  have key := AlgebraicTopology.FreeComplexCone.d_map_zero Free (U.pointsRestrict π) hsub F₀
    (fun τ ↦ ULift.up (h 0 τ.down))
    ((uliftYoneda.{w + 1}.map (terminal.from (U.simplicial _⦋0⦌))).app (op V))
    (fun _ ↦ ULift.up v)
    (fun τ hτ ↦ congrArg ULift.up (hc₁ 0 (by omega) τ.down (hmem τ hτ)))
    (fun τ hτ ↦ congrArg ULift.up (hc₂ (by omega) τ.down (hmem τ hτ))) x hxF hx
  refine X.smallEtaleTopology.superset_covering ?_ (ofArrows_unit_mem π hπ)
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  refine ⟨Free.map (↾fun τ ↦ ULift.up (h 0 τ.down)) x, ?_⟩
  rw [freeComplex_d_app]
  exact key

omit [Abelian A] [∀ (X Y : A), AddMonoidHomClass (FA X Y) (CA X) (CA Y)] in
omit [(X : A) → AddCommGroup (CA X)] in
/-- The augmentation of the free complex is locally surjective. -/
lemma isLocallySurjective_augmentation :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      ((freePresheaf Free).map (terminal.from (U.simplicial _⦋0⦌))) where
  imageSieve_mem {V} y := by
    obtain ⟨T', π, s, hπ, -⟩ := U.exists_cover_lift 0 (T := V)
      (fun Δ h _ ↦ absurd h (Nat.not_lt_zero _)) (fun _ _ h ↦ absurd h (Nat.not_lt_zero _))
    refine X.smallEtaleTopology.superset_covering ?_ (ofArrows_unit_mem π hπ)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨Free.map (↾fun _ ↦ ULift.up s) y, ?_⟩
    have e : Free.map (↾fun _ ↦ ULift.up s) ≫
        ((freePresheaf Free).map (terminal.from (U.simplicial _⦋0⦌))).app (op T') =
          ((freePresheaf Free).obj (⊤_ X.Etale)).map π.op := by
      change Free.map _ ≫ Free.map _ = Free.map _
      rw [← Free.map_comp]
      congr 1
      ext a
      exact Subsingleton.elim (α := ULift (T' ⟶ ⊤_ X.Etale)) _ _
    rw [← e, ConcreteCategory.comp_apply]
    rfl

section Sheaf

variable [HasSheafify X.smallEtaleTopology A] [X.smallEtaleTopology.WEqualsLocallyBijective A]
  [X.smallEtaleTopology.HasSheafCompose (forget A)]
  [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology]
  [(forget A).PreservesMonomorphisms]

/-- The functor `V ↦ Free[V]^#` to sheaves. -/
noncomputable abbrev freeSheaf : X.Etale ⥤ Sheaf X.smallEtaleTopology A :=
  uliftYoneda.{w + 1} ⋙ (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) A).obj Free ⋙
    presheafToSheaf X.smallEtaleTopology A

/-- The free complex of sheaves of the hypercover. -/
noncomputable abbrev freeSheafComplex : ChainComplex (Sheaf X.smallEtaleTopology A) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (U.simplicial ⋙ freeSheaf Free)

omit [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] in
lemma freeSheafComplex_d (n : ℕ) :
    (U.freeSheafComplex Free).d (n + 1) n =
      (presheafToSheaf X.smallEtaleTopology A).map ((U.freeComplex Free).d (n + 1) n) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum]
  simp only [Functor.map_zsmul]
  rfl

omit [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] in
lemma freeSheafComplex_d_one_zero :
    (U.freeSheafComplex Free).d 1 0 =
      (presheafToSheaf X.smallEtaleTopology A).map ((U.freeComplex Free).d 1 0) :=
  U.freeSheafComplex_d Free 0

include hsub hfin in
lemma freeSheafComplex_exactAt (n : ℕ) : (U.freeSheafComplex Free).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  let S : ShortComplex (X.Etaleᵒᵖ ⥤ A) := ShortComplex.mk ((U.freeComplex Free).d (n + 2) (n + 1))
    ((U.freeComplex Free).d (n + 1) n) (HomologicalComplex.d_comp_d _ _ _ _)
  have hS := Presheaf.exact_map_presheafToSheaf_of_imageSieve_mem X.smallEtaleTopology S hsub
    (fun V x hx ↦ U.imageSieve_freeComplex_d_mem Free hsub hfin n V x hx)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hS
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact U.freeSheafComplex_d Free (n + 1)
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact U.freeSheafComplex_d Free n

omit [HasSheafify X.smallEtaleTopology A] [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] in
lemma freeComplex_d_comp_augmentation :
    (U.freeComplex Free).d 1 0 ≫ (freePresheaf Free).map (terminal.from (U.simplicial _⦋0⦌)) =
      0 := by
  have h₀ :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d (U.simplicial ⋙ freePresheaf Free) 0
  rw [h₀, AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Preadditive.add_comp, Preadditive.neg_comp, SimplicialObject.δ, Functor.comp_map,
    ← Functor.map_comp]
  rw [Subsingleton.elim (U.simplicial.map (SimplexCategory.δ 0).op ≫ terminal.from _)
    (U.simplicial.map (SimplexCategory.δ 1).op ≫ terminal.from _), add_neg_cancel]

omit [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] in
lemma freeSheafComplex_d_comp_augmentation :
    (U.freeSheafComplex Free).d 1 0 ≫ (freeSheaf Free).map (terminal.from (U.simplicial _⦋0⦌)) =
      0 := by
  have h := congrArg (presheafToSheaf X.smallEtaleTopology A).map
    (U.freeComplex_d_comp_augmentation Free)
  rw [Functor.map_comp, Functor.map_zero] at h
  rw [freeSheafComplex_d_one_zero]
  exact h

include hsub hfin in
lemma freeSheafComplex_exact_zero :
    (ShortComplex.mk _ _ (U.freeSheafComplex_d_comp_augmentation Free)).Exact := by
  let S : ShortComplex (X.Etaleᵒᵖ ⥤ A) := ShortComplex.mk ((U.freeComplex Free).d 1 0)
    ((freePresheaf Free).map (terminal.from (U.simplicial _⦋0⦌)))
    (U.freeComplex_d_comp_augmentation Free)
  have hS := Presheaf.exact_map_presheafToSheaf_of_imageSieve_mem X.smallEtaleTopology S hsub
    (fun V x hx ↦ U.imageSieve_freeComplex_d_zero_mem Free hsub hfin V x hx)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hS
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact U.freeSheafComplex_d_one_zero Free
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

include FA CA in
omit [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] in
omit [(forget A).PreservesMonomorphisms] in
omit [Abelian A] [∀ (X Y : A), AddMonoidHomClass (FA X Y) (CA X) (CA Y)] in
lemma epi_freeSheaf_map_augmentation :
    Epi ((freeSheaf Free).map (terminal.from (U.simplicial _⦋0⦌))) := by
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (((Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) A).obj Free).map
        (uliftYoneda.{w + 1}.map (terminal.from (U.simplicial _⦋0⦌)))) :=
    U.isLocallySurjective_augmentation Free
  exact Presheaf.epi_presheafToSheaf_map_of_isLocallySurjective X.smallEtaleTopology _

end Sheaf


section Sections

variable [HasSheafify X.smallEtaleTopology A] [X.smallEtaleTopology.WEqualsLocallyBijective A]
  [X.smallEtaleTopology.HasSheafCompose (forget A)]
  [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology]
  [(forget A).PreservesMonomorphisms]
  (adj : Free ⊣ forget A)

include hsub in
omit [∀ (X Y : A), AddMonoidHomClass (FA X Y) (CA X) (CA Y)] [(forget A).PreservesMonomorphisms] in
lemma zero_apply_of_sub {X Y : A} (x : ToType X) : (0 : X ⟶ Y) x = 0 := by
  have := hsub (0 : X ⟶ Y) 0 x
  rw [sub_zero, sub_self] at this
  exact this

include hsub in
omit [∀ (X Y : A), AddMonoidHomClass (FA X Y) (CA X) (CA Y)] [(forget A).PreservesMonomorphisms]
  in
lemma add_apply_of_sub {X Y : A} (f g : X ⟶ Y) (x : ToType X) : (f + g) x = f x + g x := by
  have h : f + g = f - (0 - g) := by abel
  rw [h, hsub, hsub, zero_apply_of_sub hsub]
  abel

/-- Evaluation at an element, as an additive map. -/
noncomputable def evalAddHom {X Y : A} (x : ToType X) : (X ⟶ Y) →+ ToType Y where
  toFun f := f x
  map_zero' := zero_apply_of_sub hsub x
  map_add' f g := add_apply_of_sub hsub f g x

/-- Morphisms `Free[V]^# ⟶ I` are the sections of `I` over `V`. -/
noncomputable def sectionsEquiv (I : Sheaf X.smallEtaleTopology A) (V : X.Etale) :
    ((freeSheaf Free).obj V ⟶ I) ≃ ToType (I.obj.obj (op V)) :=
  ((sheafificationAdjunction X.smallEtaleTopology A).homEquiv _ _).trans
    (((adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv.{w + 1})

omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] [Abelian A] [∀ (X Y : A), AddMonoidHomClass (FA X Y) (CA X) (CA Y)] [X.smallEtaleTopology.WEqualsLocallyBijective A] [X.smallEtaleTopology.HasSheafCompose (forget A)] [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] [(forget A).PreservesMonomorphisms] in
omit [(X : A) → AddCommGroup (CA X)] in
lemma sectionsEquiv_apply (I : Sheaf X.smallEtaleTopology A) (V : X.Etale)
    (φ : (freeSheaf Free).obj V ⟶ I) :
    sectionsEquiv Free adj I V φ =
      (toSheafify X.smallEtaleTopology _ ≫ φ.hom).app (op V)
        (adj.unit.app _ (ULift.up (𝟙 V))) := by
  simp only [sectionsEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rfl

omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] [Abelian A] [∀ (X Y : A), AddMonoidHomClass (FA X Y) (CA X) (CA Y)] [X.smallEtaleTopology.WEqualsLocallyBijective A] [X.smallEtaleTopology.HasSheafCompose (forget A)] [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] [(forget A).PreservesMonomorphisms] in
omit [(X : A) → AddCommGroup (CA X)] in
lemma sectionsEquiv_naturality (I : Sheaf X.smallEtaleTopology A) {V V' : X.Etale}
    (f : V' ⟶ V) (φ : (freeSheaf Free).obj V ⟶ I) :
    sectionsEquiv Free adj I V' ((freeSheaf Free).map f ≫ φ) =
      I.obj.map f.op (sectionsEquiv Free adj I V φ) := by
  simp only [sectionsEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ f.op).symm

include hsub in
omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X]
  [X.smallEtaleTopology.WEqualsLocallyBijective A]
  [X.smallEtaleTopology.HasSheafCompose (forget A)]
  [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology] in
lemma sectionsEquiv_add (I : Sheaf X.smallEtaleTopology A) (V : X.Etale)
    (φ ψ : (freeSheaf Free).obj V ⟶ I) :
    sectionsEquiv Free adj I V (φ + ψ) =
      sectionsEquiv Free adj I V φ + sectionsEquiv Free adj I V ψ := by
  have h : toSheafify X.smallEtaleTopology _ ≫ (φ + ψ).hom =
      toSheafify X.smallEtaleTopology _ ≫ φ.hom + toSheafify X.smallEtaleTopology _ ≫ ψ.hom := by
    rw [← Preadditive.comp_add]
    rfl
  rw [sectionsEquiv_apply, sectionsEquiv_apply, sectionsEquiv_apply, h, NatTrans.app_add,
    add_apply_of_sub hsub]

/-- `sectionsEquiv` as an additive equivalence. -/
noncomputable def sectionsAddEquiv (I : Sheaf X.smallEtaleTopology A) (V : X.Etale) :
    ((freeSheaf Free).obj V ⟶ I) ≃+ ToType (I.obj.obj (op V)) :=
  { sectionsEquiv Free adj I V with map_add' := sectionsEquiv_add Free hsub adj I V }

include hsub in
lemma sum_zsmul_apply_of_sub {X Y : A} {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (f : ι → (X ⟶ Y)) (x : ToType X) :
    (∑ i ∈ s, c i • f i) x = ∑ i ∈ s, c i • f i x := by
  let ev : (X ⟶ Y) →+ ToType Y :=
    { toFun := fun g ↦ g x
      map_zero' := zero_apply_of_sub hsub x
      map_add' := fun g g' ↦ add_apply_of_sub hsub g g' x }
  change ev (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • ev (f i)
  simp only [map_sum, map_zsmul]

lemma sectionsEquiv_d (I : Sheaf X.smallEtaleTopology A) (p : ℕ)
    (φ : (freeSheaf Free).obj (U.simplicial _⦋p⦌) ⟶ I) :
    sectionsAddEquiv Free hsub adj I (U.simplicial _⦋p + 1⦌)
        ((U.freeSheafComplex Free).d (p + 1) p ≫ φ) =
      ((AlgebraicTopology.alternatingCofaceMapComplex A).obj
        (U.simplicial.rightOp ⋙ I.obj)).d p (p + 1)
          (sectionsAddEquiv Free hsub adj I (U.simplicial _⦋p⦌) φ) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, map_sum, map_zsmul]
  have hC : ((AlgebraicTopology.alternatingCofaceMapComplex A).obj
      (U.simplicial.rightOp ⋙ I.obj)).d p (p + 1) =
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          (U.simplicial.rightOp ⋙ I.obj) p := by
    simp [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [hC, AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_zsmul_apply_of_sub hsub]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact sectionsEquiv_naturality Free adj I (U.simplicial.δ i) φ

include hsub hfin adj in
/-- For an injective sheaf `I`, the complex of sections `I(U_•)` is a resolution of `I(X)`. -/
theorem injective_section_cohomology
    (hexact : ∀ S : ShortComplex A, (∀ x₂ : ToType S.X₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂) →
      S.Exact)
    (I : Sheaf X.smallEtaleTopology A) [Injective I] :
    Function.Injective (I.obj.map (terminal.from (U.simplicial.obj (op ⦋0⦌))).op) ∧
      (∀ s : ToType (I.obj.obj (op (U.simplicial.obj (op ⦋0⦌)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex A).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from (U.simplicial.obj (op ⦋0⦌))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex A).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  have := U.epi_freeSheaf_map_augmentation Free
  let e := fun V ↦ sectionsAddEquiv Free hsub adj I V
  have key : ∀ φ : (freeSheaf Free).obj (⊤_ X.Etale) ⟶ I,
      I.obj.map (terminal.from (U.simplicial.obj (op ⦋0⦌))).op (e _ φ) =
        e _ ((freeSheaf Free).map (terminal.from (U.simplicial.obj (op ⦋0⦌))) ≫ φ) :=
    fun φ ↦ (sectionsEquiv_naturality Free adj I _ φ).symm
  refine ⟨?_, ?_, ?_⟩
  · intro s t h
    obtain ⟨φ, rfl⟩ := (e _).surjective s
    obtain ⟨ψ, rfl⟩ := (e _).surjective t
    rw [key, key] at h
    rw [(cancel_epi _).1 ((e _).injective h)]
  · intro s
    obtain ⟨φ, rfl⟩ := (e _).surjective s
    have hex := U.freeSheafComplex_exact_zero Free hsub hfin
    constructor
    · intro hs
      have h1 : (U.freeSheafComplex Free).d 1 0 ≫ φ = 0 := by
        apply (e _).injective
        rw [map_zero]
        exact (sectionsEquiv_d U Free hsub adj I 0 φ).trans hs
      refine ⟨e _ (hex.descToInjective φ h1), ?_⟩
      rw [key]
      congr 1
      exact hex.comp_descToInjective φ h1
    · rintro ⟨t, ht⟩
      obtain ⟨ψ, rfl⟩ := (e _).surjective t
      rw [key] at ht
      obtain rfl := (e _).injective ht
      rw [← sectionsEquiv_d U Free hsub adj I 0, ← Category.assoc,
        U.freeSheafComplex_d_comp_augmentation Free, zero_comp, map_zero]
  · intro p hp
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    refine HomologicalComplex.ExactAt.isZero_homology ?_
    rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp)]
    apply hexact
    intro s hs
    obtain ⟨φ, rfl⟩ := (e _).surjective s
    have h1 : (U.freeSheafComplex Free).d (m + 2) (m + 1) ≫ φ = 0 := by
      apply (e _).injective
      rw [map_zero]
      exact (sectionsEquiv_d U Free hsub adj I (m + 1) φ).trans hs
    have hL := U.freeSheafComplex_exactAt Free hsub hfin m
    rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)] at hL
    refine ⟨e _ (hL.descToInjective φ h1), ?_⟩
    refine (sectionsEquiv_d U Free hsub adj I m _).symm.trans ?_
    congr 1
    exact hL.comp_descToInjective φ h1

include hsub hfin in
/-- The augmented free complex of a split étale hypercover is exact after sheafification. -/
theorem quasiIso_augmentation :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _ (freeSheaf Free)).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · have h : (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
          ((SimplicialObject.Augmented.whiskeringObj X.Etale _ (freeSheaf Free)).obj
            (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))).f 0 =
            (freeSheaf Free).map (terminal.from (U.simplicial _⦋0⦌)) := by
        rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
        simp only [SimplicialObject.Augmented.whiskeringObj, NatTrans.comp_app,
          Functor.whiskerRight_app, SimplicialObject.augmentOfIsTerminal_hom_app,
          Functor.constComp_hom_app, Category.comp_id]
        rfl
      refine ⟨?_, ?_⟩
      · refine (ShortComplex.exact_iff_of_iso ?_).1 (U.freeSheafComplex_exact_zero Free hsub hfin)
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
          rfl
        · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
          exact h
      · change Epi ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app
          ((SimplicialObject.Augmented.whiskeringObj X.Etale _ (freeSheaf Free)).obj
            (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))).f 0)
        rw [h]
        exact U.epi_freeSheaf_map_augmentation Free
    all_goals simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact U.freeSheafComplex_exactAt Free hsub hfin n

end Sections

end Free

end AlgebraicGeometry.SplitEtaleHypercover
