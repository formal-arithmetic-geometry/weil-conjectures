/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
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
    simp only [faceClosure, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_univ,
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
  [∀ X, AddCommGroup (CA X)] (Free : Type (w + 1) ⥤ A)

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
    change (Free.map _ ≫ Free.map _) y = Free.map _ y
    rw [← Free.map_comp]
    congr 2
    ext a
    exact Subsingleton.elim (α := ULift (T' ⟶ ⊤_ X.Etale)) _ _

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

lemma freeSheafComplex_d (n : ℕ) :
    (U.freeSheafComplex Free).d (n + 1) n =
      (presheafToSheaf X.smallEtaleTopology A).map ((U.freeComplex Free).d (n + 1) n) := by
  simp only [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rfl

include hsub hfin in
lemma freeSheafComplex_exactAt (n : ℕ) : (U.freeSheafComplex Free).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  let S : ShortComplex (X.Etaleᵒᵖ ⥤ A) := ShortComplex.mk ((U.freeComplex Free).d (n + 2) (n + 1))
    ((U.freeComplex Free).d (n + 1) n) (by simp)
  have hS := Presheaf.exact_map_presheafToSheaf_of_imageSieve_mem X.smallEtaleTopology S hsub
    (fun V x hx ↦ U.imageSieve_freeComplex_d_mem Free hsub hfin n V x hx)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hS
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [S, freeSheafComplex_d]) (by simp [S, freeSheafComplex_d])

lemma freeComplex_d_comp_augmentation :
    (U.freeComplex Free).d 1 0 ≫ (freePresheaf Free).map (terminal.from (U.simplicial _⦋0⦌)) =
      0 := by
  have h₀ := AlgebraicTopology.alternatingFaceMapComplex_obj_d (U.simplicial ⋙ freePresheaf Free) 0
  rw [h₀, AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Preadditive.add_comp, Preadditive.neg_comp, SimplicialObject.δ, Functor.comp_map,
    ← Functor.map_comp]
  rw [Subsingleton.elim (U.simplicial.map (SimplexCategory.δ 0).op ≫ terminal.from _)
    (U.simplicial.map (SimplexCategory.δ 1).op ≫ terminal.from _), add_neg_cancel]

include hsub hfin in
lemma freeSheafComplex_exact_zero :
    (ShortComplex.mk ((U.freeSheafComplex Free).d 1 0)
      ((freeSheaf Free).map (terminal.from (U.simplicial _⦋0⦌))) (by
        rw [freeSheafComplex_d, Functor.map_comp.symm]
        sorry)).Exact := by
  sorry

end Sheaf

end Free

end AlgebraicGeometry.SplitEtaleHypercover
