/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.FieldTheory.Normal.Defs

/-!
# Field points of the small étale site of a field

Let `K` be a field. Every étale `K`-scheme `V` is covered by its *field points*, the morphisms
`Spec E ⟶ V` of étale `K`-schemes with `E` a finite separable field extension of `K`. Hence a
section of an étale sheaf on `Spec K` is determined by its restrictions to the field points.

## Main statements

- `AlgebraicGeometry.Scheme.exists_etaleSpecMap_eq`: a morphism `Spec B ⟶ Spec A` of étale
  `K`-schemes comes from a `K`-algebra map `A →ₐ[K] B`.
- `AlgebraicGeometry.Scheme.exists_etaleSpec_field_mem_of_mem`: a covering sieve contains a field
  point through every point.
- `AlgebraicGeometry.Scheme.ext_of_forall_etaleSpec_field`: sections are determined by their
  restrictions to field points.
- `AlgebraicGeometry.Scheme.injective_map_of_surjective`: restriction along a surjective
  morphism of étale `K`-schemes is injective.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

lemma nsmul_hom_app_apply {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (m : ℕ) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (m • f).hom.app U x = m • f.hom.app U x := by
  have e : (m • f).hom = m • f.hom := (sheafToPresheaf _ _).map_nsmul (f := f) (n := m)
  rw [e, NatTrans.app_nsmul]
  rfl

lemma zsmul_hom_app_apply {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (m : ℤ) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (m • f).hom.app U x = m • f.hom.app U x := by
  have e : (m • f).hom = m • f.hom := (sheafToPresheaf _ _).map_zsmul (f := f) (r := m)
  rw [e, NatTrans.app_zsmul]
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [Algebra.Etale K A] [Algebra.Etale K B]

/-- A morphism `Spec B ⟶ Spec A` of étale `K`-schemes is induced by a `K`-algebra map
`A →ₐ[K] B`. -/
lemma exists_etaleSpecMap_eq (ψ : etaleSpec K B ⟶ etaleSpec K A) :
    ∃ γ : A →ₐ[K] B, etaleSpecMap γ = ψ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ψ.left
  have hw : ψ.left ≫ (etaleSpec K A).hom = (etaleSpec K B).hom := MorphismProperty.Over.w ψ
  rw [← hφ] at hw
  change Spec.map φ ≫ Spec.map _ = Spec.map _ at hw
  rw [← Spec.map_comp] at hw
  have hc := Spec.map_injective hw
  refine ⟨{ φ.hom with commutes' := fun r ↦ congr($(hc).hom r) }, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact hφ

/-- **Field points.** Every point of an étale `K`-scheme `V` is in the image of a morphism
`Spec E ⟶ V` of étale `K`-schemes, for a finite separable field extension `E` of `K`. -/
lemma exists_etaleSpec_field_mem (V : (Spec (.of K)).Etale) (x : V.left) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra.Etale K E)
      (ψ : etaleSpec K E ⟶ V), x ∈ Set.range ψ.left := by
  let 𝒱 := V.left.affineOpenCover
  obtain ⟨z, hz⟩ := 𝒱.covers x
  generalize 𝒱.idx x = k at z hz
  have hc : Etale (𝒱.f k ≫ V.hom) := by
    have := V.prop
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒱.f k ≫ V.hom)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Etale)] at hc
  algebraize [φ.hom]
  have : Module.Finite K (𝒱.X k) := Algebra.FormallyUnramified.finite_of_free K _
  set p := (z : PrimeSpectrum (𝒱.X k)).asIdeal
  have : p.IsMaximal := by
    have : Algebra.IsIntegral K (𝒱.X k) := inferInstance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
      ((Ideal.comap (algebraMap K (𝒱.X k)) p).eq_bot_of_prime ▸ Ideal.bot_isMaximal)
  let := Ideal.Quotient.field p
  have : Algebra.FormallyEtale K (𝒱.X k ⧸ p) := Algebra.FormallyEtale.of_isSeparable K _
  have : Algebra.Etale K (𝒱.X k ⧸ p) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let g : etaleSpec K (𝒱.X k ⧸ p) ⟶ V :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p)) ≫ 𝒱.f k)
      (by
        change _ ≫ V.hom = Spec.map _
        rw [Category.assoc, ← hφ, ← Spec.map_comp]
        rfl)
  refine ⟨_, _, _, _, g, ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩⟩
  change (𝒱.f k) ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))) _) = x
  rw [← hz]
  congr 1
  apply PrimeSpectrum.ext
  exact (RingHom.ker_eq_comap_bot (Ideal.Quotient.mk p)).symm.trans Ideal.mk_ker

/-- A covering sieve of an étale `K`-scheme `V` contains a field point through every point
of `V`. -/
lemma exists_etaleSpec_field_mem_of_mem {V : (Spec (.of K)).Etale} {R : Sieve V}
    (hR : R ∈ (Spec (.of K)).smallEtaleTopology V) (x : V.left) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra.Etale K E)
      (ψ : etaleSpec K E ⟶ V), R ψ ∧ x ∈ Set.range ψ.left := by
  obtain ⟨W, g, hg, w, rfl⟩ := (mem_smallEtaleTopology_iff R).1 hR x
  obtain ⟨E, _, _, _, ψ, y, rfl⟩ := exists_etaleSpec_field_mem W w
  exact ⟨E, _, _, _, ψ ≫ g, R.downward_closed hg ψ, y, rfl⟩

/-- The sieve generated by the field points of an étale `K`-scheme is a covering sieve. -/
lemma mem_smallEtaleTopology_of_forall_etaleSpec_field {V : (Spec (.of K)).Etale}
    (R : Sieve V)
    (hR : ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.Etale K E]
      (ψ : etaleSpec K E ⟶ V), R ψ) :
    R ∈ (Spec (.of K)).smallEtaleTopology V := by
  refine (mem_smallEtaleTopology_iff R).2 fun x ↦ ?_
  obtain ⟨E, _, _, _, ψ, hx⟩ := exists_etaleSpec_field_mem V x
  exact ⟨_, ψ, hR E ψ, hx⟩

/-- **Sections are determined by field points.** Two sections of a sheaf on the small étale
site of `Spec K` agree if their restrictions to all field points agree. -/
lemma ext_of_forall_etaleSpec_field (M : Sheaf (Spec (.of K)).smallEtaleTopology
    AddCommGrpCat.{u + 1}) {V : (Spec (.of K)).Etale} {s t : M.obj.obj (op V)}
    (h : ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.Etale K E]
      (ψ : etaleSpec K E ⟶ V), M.obj.map ψ.op s = M.obj.map ψ.op t) : s = t := by
  let R : Sieve V :=
    { arrows W g := M.obj.map g.op s = M.obj.map g.op t
      downward_closed := by
        intro W W' g hg f
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg] }
  have hR : R ∈ (Spec (.of K)).smallEtaleTopology V :=
    mem_smallEtaleTopology_of_forall_etaleSpec_field R fun E _ _ _ ψ ↦ h E ψ
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ M.obj
    (CategoryTheory.forget AddCommGrpCat) M.property)) R hR
  exact hsep.isSeparatedFor.ext fun W g hg ↦ hg

/-- Restriction along a surjective morphism of étale `K`-schemes is injective. -/
lemma injective_map_of_surjective (M : Sheaf (Spec (.of K)).smallEtaleTopology
    AddCommGrpCat.{u + 1}) {V W : (Spec (.of K)).Etale} (g : W ⟶ V)
    (hg : Function.Surjective g.left) : Function.Injective (M.obj.map g.op) := by
  intro s t hst
  have hR : Sieve.generate (Presieve.singleton g) ∈ (Spec (.of K)).smallEtaleTopology V := by
    refine (mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
    obtain ⟨w, rfl⟩ := hg x
    exact ⟨W, g, ⟨W, 𝟙 W, g, Presieve.singleton.mk, Category.id_comp g⟩, w, rfl⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ M.obj
    (CategoryTheory.forget AddCommGrpCat) M.property)) _ hR
  refine hsep.isSeparatedFor.ext fun Z f ⟨Y, a, b, hb, hab⟩ ↦ ?_
  cases hb
  rw [← hab]
  change M.obj.map (a ≫ g).op s = M.obj.map (a ≫ g).op t
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hst]

/-- A morphism of étale `K`-schemes between spectra of fields is surjective. -/
lemma surjective_left_of_field {E F : Type u} [Field E] [Field F] [Algebra K E] [Algebra K F]
    [Algebra.Etale K E] [Algebra.Etale K F] (g : etaleSpec K E ⟶ etaleSpec K F) :
    Function.Surjective g.left := fun y ↦
  ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
    (Ideal.eq_bot_of_prime (y : PrimeSpectrum F).asIdeal).symm)⟩

/-! ### Base change to an étale algebra -/

section BaseChange

variable (A) in
/-- The base change `V ×_K A` of an étale `K`-scheme `V` to an étale `K`-algebra `A`, as an
étale `K`-scheme. -/
noncomputable abbrev etaleBaseChange (V : (Spec (.of K)).Etale) : (Spec (.of K)).Etale :=
  (MorphismProperty.Over.map ⊤ (etaleSpec K A).prop).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ (etaleSpec K A).hom).obj V)

variable (A) in
/-- The projection `V ×_K A ⟶ V`. -/
noncomputable def etaleBaseChangeFst (V : (Spec (.of K)).Etale) : etaleBaseChange A V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom (etaleSpec K A).hom) pullback.condition

variable (A) in
/-- The projection `V ×_K A ⟶ Spec A`. -/
noncomputable def etaleBaseChangeSnd (V : (Spec (.of K)).Etale) :
    etaleBaseChange A V ⟶ etaleSpec K A :=
  MorphismProperty.Over.homMk (pullback.snd V.hom (etaleSpec K A).hom) rfl

/-- The morphism `V ×_K B ⟶ V ×_K A` induced by a `K`-algebra map `A →ₐ[K] B`. -/
noncomputable def etaleBaseChangeMap (φ : A →ₐ[K] B) (V : (Spec (.of K)).Etale) :
    etaleBaseChange B V ⟶ etaleBaseChange A V :=
  MorphismProperty.Over.homMk
    (pullback.map _ _ _ _ (𝟙 _) (etaleSpecMap φ).left (𝟙 _) (by simp)
      (by simp [MorphismProperty.Over.w (etaleSpecMap φ)]))
    (by simp [MorphismProperty.Over.w (etaleSpecMap φ)])

/-- The morphism `Z ⟶ V ×_K A` with components `g₁ : Z ⟶ V` and `g₂ : Z ⟶ Spec A`. -/
noncomputable def etaleBaseChangeLift {Z V : (Spec (.of K)).Etale} (g₁ : Z ⟶ V)
    (g₂ : Z ⟶ etaleSpec K A) : Z ⟶ etaleBaseChange A V :=
  MorphismProperty.Over.homMk
    (pullback.lift g₁.left g₂.left
      (by rw [MorphismProperty.Over.w g₁, MorphismProperty.Over.w g₂]))
    (by simp [MorphismProperty.Over.w g₂])

@[reassoc (attr := simp)]
lemma etaleBaseChangeLift_fst {Z V : (Spec (.of K)).Etale} (g₁ : Z ⟶ V)
    (g₂ : Z ⟶ etaleSpec K A) : etaleBaseChangeLift g₁ g₂ ≫ etaleBaseChangeFst A V = g₁ := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma etaleBaseChangeLift_snd {Z V : (Spec (.of K)).Etale} (g₁ : Z ⟶ V)
    (g₂ : Z ⟶ etaleSpec K A) : etaleBaseChangeLift g₁ g₂ ≫ etaleBaseChangeSnd A V = g₂ := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

lemma etaleBaseChange_hom_ext {Z V : (Spec (.of K)).Etale} {f g : Z ⟶ etaleBaseChange A V}
    (h₁ : f ≫ etaleBaseChangeFst A V = g ≫ etaleBaseChangeFst A V)
    (h₂ : f ≫ etaleBaseChangeSnd A V = g ≫ etaleBaseChangeSnd A V) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.hom_ext congr($(h₁).left) congr($(h₂).left)

@[reassoc (attr := simp)]
lemma etaleBaseChangeMap_fst (φ : A →ₐ[K] B) (V : (Spec (.of K)).Etale) :
    etaleBaseChangeMap φ V ≫ etaleBaseChangeFst A V = etaleBaseChangeFst B V := by
  apply MorphismProperty.Over.Hom.ext
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma etaleBaseChangeMap_snd (φ : A →ₐ[K] B) (V : (Spec (.of K)).Etale) :
    etaleBaseChangeMap φ V ≫ etaleBaseChangeSnd A V =
      etaleBaseChangeSnd B V ≫ etaleSpecMap φ := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _


variable (A) in
/-- The morphism `V₁ ×_K A ⟶ V₂ ×_K A` induced by a morphism `V₁ ⟶ V₂`. These are the
restriction maps of the pushforward along `Spec A ⟶ Spec K`. -/
noncomputable abbrev etaleBaseChangeHom {V₁ V₂ : (Spec (.of K)).Etale} (f : V₁ ⟶ V₂) :
    etaleBaseChange A V₁ ⟶ etaleBaseChange A V₂ :=
  (MorphismProperty.Over.map ⊤ (etaleSpec K A).prop).map
    ((MorphismProperty.Over.pullback @Etale ⊤ (etaleSpec K A).hom).map f)

@[reassoc (attr := simp)]
lemma etaleBaseChangeHom_fst {V₁ V₂ : (Spec (.of K)).Etale} (f : V₁ ⟶ V₂) :
    etaleBaseChangeHom A f ≫ etaleBaseChangeFst A V₂ = etaleBaseChangeFst A V₁ ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma etaleBaseChangeHom_snd {V₁ V₂ : (Spec (.of K)).Etale} (f : V₁ ⟶ V₂) :
    etaleBaseChangeHom A f ≫ etaleBaseChangeSnd A V₂ = etaleBaseChangeSnd A V₁ := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

lemma etaleBaseChangeMap_comp {C : Type u} [CommRing C] [Algebra K C] [Algebra.Etale K C]
    (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) (V : (Spec (.of K)).Etale) :
    etaleBaseChangeMap ψ V ≫ etaleBaseChangeMap φ V = etaleBaseChangeMap (ψ.comp φ) V := by
  refine etaleBaseChange_hom_ext ?_ ?_
  · simp
  · simp [etaleSpecMap_comp]

@[reassoc]
lemma etaleBaseChangeMap_hom (φ : A →ₐ[K] B) {V₁ V₂ : (Spec (.of K)).Etale} (f : V₁ ⟶ V₂) :
    etaleBaseChangeMap φ V₁ ≫ etaleBaseChangeHom A f =
      etaleBaseChangeHom B f ≫ etaleBaseChangeMap φ V₂ := by
  refine etaleBaseChange_hom_ext ?_ ?_ <;> simp

/-- For a nonempty `A`, the projection `V ×_K A ⟶ V` is surjective. -/
lemma surjective_etaleBaseChangeFst [Nontrivial A] (V : (Spec (.of K)).Etale) :
    Function.Surjective (etaleBaseChangeFst A V).left := by
  have : Surjective (etaleSpec K A).hom := ⟨fun x ↦ by
    obtain ⟨y⟩ : Nonempty (Spec (.of A)) := inferInstance
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have h : Surjective (pullback.fst V.hom (etaleSpec K A).hom) := inferInstance
  exact h.surj

end BaseChange

/-! ### Galois descent -/

section Descent

variable {N : Type u} [Field N] [Algebra K N] [Algebra.Etale K N]

/-- **Galois descent of sections.** Let `N/K` be a finite Galois extension and `M` an étale
sheaf on `Spec K`. A section of `M` over `V ×_K N` which is invariant under the automorphisms
of `N/K` descends to `V`. -/
theorem exists_map_etaleBaseChangeFst_eq [IsGalois K N]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : (Spec (.of K)).Etale) (t : M.obj.obj (op (etaleBaseChange N V)))
    (ht : ∀ σ : N ≃ₐ[K] N, M.obj.map (etaleBaseChangeMap σ.toAlgHom V).op t = t) :
    ∃ s, M.obj.map (etaleBaseChangeFst N V).op s = t := by
  let p := etaleBaseChangeFst N V
  have hcov : Sieve.generate (Presieve.singleton p) ∈ (Spec (.of K)).smallEtaleTopology V := by
    refine (mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
    obtain ⟨w, rfl⟩ := surjective_etaleBaseChangeFst (A := N) V x
    exact ⟨_, p, ⟨_, 𝟙 _, p, Presieve.singleton.mk, Category.id_comp p⟩, w, rfl⟩
  have hsheaf : Presieve.IsSheafFor (M.obj ⋙ CategoryTheory.forget _)
      (Presieve.singleton p) := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ M.obj (CategoryTheory.forget AddCommGrpCat) M.property)
    rw [Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨s, hs, -⟩ := Presieve.isSheafFor_singleton.mp hsheaf t fun {Z} g₁ g₂ hg ↦ by
    change M.obj.map g₁.op t = M.obj.map g₂.op t
    refine ext_of_forall_etaleSpec_field M fun E _ _ _ ψ ↦ ?_
    obtain ⟨β₁, hβ₁⟩ := exists_etaleSpecMap_eq (ψ ≫ g₁ ≫ etaleBaseChangeSnd N V)
    obtain ⟨β₂, hβ₂⟩ := exists_etaleSpecMap_eq (ψ ≫ g₂ ≫ etaleBaseChangeSnd N V)
    obtain ⟨σ, rfl⟩ := Normal.exists_algEquiv_comp_eq β₁ β₂
    have hg' : ψ ≫ g₂ = ψ ≫ g₁ ≫ etaleBaseChangeMap σ.toAlgHom V := by
      refine etaleBaseChange_hom_ext ?_ ?_
      · simp only [Category.assoc, etaleBaseChangeMap_fst]
        exact congrArg (ψ ≫ ·) hg.symm
      · simp only [Category.assoc, etaleBaseChangeMap_snd]
        rw [← hβ₂, ← etaleSpecMap_comp, hβ₁]
        simp only [Category.assoc]
    have key : M.obj.map (ψ ≫ g₂).op t = M.obj.map (ψ ≫ g₁).op t := by
      rw [hg', ← Category.assoc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ht]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using key.symm
  exact ⟨s, hs⟩

end Descent

end AlgebraicGeometry.Scheme
