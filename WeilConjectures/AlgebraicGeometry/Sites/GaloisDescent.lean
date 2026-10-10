/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.Mathlib.FieldTheory.Normal.Basic

/-!
# Galois descent for sections of étale sheaves on the spectrum of a field

Let `K` be a field. Every étale `K`-scheme is covered by the spectra of finite separable field
extensions of `K` (`AlgebraicGeometry.Scheme.exists_etaleSpec_hom_mem_range`), and the morphisms
between such spectra are induced by `K`-algebra maps
(`AlgebraicGeometry.Scheme.exists_etaleSpecMap_eq`). For a finite Galois extension `L/K`, two
morphisms from the spectrum of a field to `Spec L` differ by an automorphism of `L/K`. Hence a
section of an étale sheaf over a covering `V ⟶ U` on which the Galois group acts, and which is
invariant, descends to `U` (`AlgebraicGeometry.Scheme.existsUnique_map_eq_of_forall_map_eq`).

## Main statements

- `AlgebraicGeometry.Scheme.existsUnique_map_eq_of_forall_map_eq`: Galois descent of sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

section Morphisms

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [Algebra.Etale K A] [Algebra.Etale K B]

/-- Every morphism `Spec B ⟶ Spec A` of the small étale site of `Spec K` is induced by a
`K`-algebra map `A →ₐ[K] B`. -/
lemma exists_etaleSpecMap_eq (g : etaleSpec K B ⟶ etaleSpec K A) :
    ∃ φ : A →ₐ[K] B, etaleSpecMap φ = g := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective g.left
  have hw : Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [hψ]
    exact MorphismProperty.Over.w g
  rw [← Spec.map_comp] at hw
  have hw' := Spec.map_injective hw
  refine ⟨{ ψ.hom with commutes' := fun r ↦ ?_ }, ?_⟩
  · exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of B ↦ f r) hw'
  · apply MorphismProperty.Over.Hom.ext
    exact hψ

end Morphisms

/-- **Field points of an étale `K`-scheme.** Every point of an étale `K`-scheme `W` lies in the
image of a morphism `Spec E ⟶ W` from the spectrum of a finite separable field extension `E` of
`K`. -/
lemma exists_etaleSpec_hom_mem_range (W : (Spec (.of K)).Etale) (x : W.left) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra.Etale K E)
      (g : etaleSpec K E ⟶ W), x ∈ Set.range g.left := by
  let 𝒱 := W.left.affineOpenCover
  let k := 𝒱.idx x
  obtain ⟨z, hz⟩ : x ∈ Set.range (𝒱.f k) := 𝒱.covers x
  have := z.isPrime
  let p : Spec (𝒱.X k) ⟶ Spec (.of K) := 𝒱.f k ≫ W.hom
  have hc : Etale p := by
    have : Etale W.hom := W.prop
    exact inferInstanceAs (Etale (𝒱.f k ≫ W.hom))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective p
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Etale)] at hc
  algebraize [φ.hom]
  have : Module.Finite K (𝒱.X k) := Algebra.FormallyUnramified.finite_of_free K _
  let m := (z : PrimeSpectrum (𝒱.X k)).asIdeal
  have : Algebra.IsIntegral K (𝒱.X k) := Algebra.IsIntegral.of_finite K _
  have : m.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := K) m ?_
    rw [Ideal.eq_bot_of_prime (m.comap (algebraMap K (𝒱.X k)))]
    exact Ideal.bot_isMaximal
  let := Ideal.Quotient.field m
  have : Algebra.FormallyEtale K (𝒱.X k ⧸ m) := Algebra.FormallyEtale.of_isSeparable K _
  have : Algebra.Etale K (𝒱.X k ⧸ m) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let g : etaleSpec K (𝒱.X k ⧸ m) ⟶ W :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ 𝒱.f k)
      (by
        change Spec.map _ ≫ p = Spec.map _
        rw [← hφ, ← Spec.map_comp]
        rfl)
  refine ⟨_, _, _, _, g, ?_⟩
  refine ⟨IsLocalRing.closedPoint _, ?_⟩
  change (𝒱.f k) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) _) = x
  rw [← hz]
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk m) (IsLocalRing.maximalIdeal _) = m
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- The morphisms from the spectra of fields to an étale `K`-scheme `W` form a covering family:
for every point of `W` one such morphism hits it. -/
lemma isSeparatedFor_etaleSpec (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (W : (Spec (.of K)).Etale) {a b : F.obj.obj (op W)}
    (h : ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.Etale K E] (g : etaleSpec K E ⟶ W),
      F.obj.map g.op a = F.obj.map g.op b) : a = b := by
  choose E _ _ _ g hg using exists_etaleSpec_hom_mem_range W
  have hcov : ⋃ x, Set.range (g x).left = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, hg x⟩
  refine (isSheafFor_ofArrows F g hcov).isSeparatedFor.ext ?_
  rintro _ _ ⟨x⟩
  exact h _ (g x)

/-- **Galois descent of sections.** Let `p : V ⟶ U` be a surjective morphism of étale `K`-schemes
and let a type `G` act on `V`, transitively on the field points of the fibres of `p`:
two morphisms `Spec E ⟶ V` from the spectrum of a field which agree after composition with `p`
differ by the action of some `σ : G`. Then a section of an abelian étale sheaf over `V` which is
invariant under the action is the pullback of a unique section over `U`. -/
theorem existsUnique_map_eq_of_forall_map_eq
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {U V : (Spec (.of K)).Etale} (p : V ⟶ U) (hp : Function.Surjective p.left)
    {G : Type*} (act : G → (V ⟶ V))
    (htrans : ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.Etale K E]
      (g₁ g₂ : etaleSpec K E ⟶ V), g₁ ≫ p = g₂ ≫ p → ∃ σ, g₂ = g₁ ≫ act σ)
    (x : F.obj.obj (op V)) (hx : ∀ σ, F.obj.map (act σ).op x = x) :
    ∃! y, F.obj.map p.op y = x := by
  have hcov : ⋃ _ : Unit, Set.range p.left = Set.univ := by
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.2 hp
  have hsh := isSheafFor_ofArrows F (fun _ : Unit ↦ p) hcov
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hcomp : Presieve.Arrows.Compatible (F.obj ⋙ CategoryTheory.forget _) (fun _ : Unit ↦ p)
      (fun _ ↦ x) := by
    intro _ _ Z g₁ g₂ hg
    refine isSeparatedFor_etaleSpec F Z fun E _ _ _ g ↦ ?_
    obtain ⟨σ, hσ⟩ := htrans E (g ≫ g₁) (g ≫ g₂) (by simp only [Category.assoc, hg])
    change F.obj.map g.op (F.obj.map g₁.op x) = F.obj.map g.op (F.obj.map g₂.op x)
    calc F.obj.map g.op (F.obj.map g₁.op x) = F.obj.map (g ≫ g₁).op x := by
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      _ = F.obj.map ((g ≫ g₁) ≫ act σ).op x := by
          rw [op_comp (f := g ≫ g₁), Functor.map_comp, ConcreteCategory.comp_apply, hx]
      _ = F.obj.map g.op (F.obj.map g₂.op x) := by
          rw [← hσ, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  obtain ⟨y, hy, huniq⟩ := hsh (fun _ ↦ x) hcomp
  exact ⟨y, hy (), fun y' hy' ↦ huniq y' fun _ ↦ hy'⟩

section Product

/-- The structure morphism of an étale `K`-scheme, as a morphism to the terminal object. -/
noncomputable abbrev toEtalePoint (U : (Spec (.of K)).Etale) : U ⟶ etalePoint K :=
  isTerminalEtalePoint.from U

variable (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L]

/-- The product `U ×_K Spec L` of an étale `K`-scheme `U` with the spectrum of a finite separable
field extension `L`, as an object of the small étale site of `Spec K`. -/
noncomputable abbrev prodEtaleSpec (U : (Spec (.of K)).Etale) : (Spec (.of K)).Etale :=
  pullback (toEtalePoint U) (toEtalePoint (etaleSpec K L))

/-- The projection `U ×_K Spec L ⟶ U` is surjective. -/
lemma surjective_fst_prodEtaleSpec (U : (Spec (.of K)).Etale) :
    Function.Surjective
      (pullback.fst (toEtalePoint U) (toEtalePoint (etaleSpec K L))).left := by
  let F := Etale.forget (Spec (.of K)) ⋙ Over.forget (Spec (.of K))
  have e := PreservesPullback.iso_hom_fst F (toEtalePoint U)
    (toEtalePoint (etaleSpec K L))
  have : Nonempty (Spec (.of L)) := inferInstance
  have hs : Surjective (F.map (toEtalePoint (etaleSpec K L))) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨z⟩ := ‹Nonempty (Spec (.of L))›
    have : Subsingleton (F.obj (etalePoint K)) := inferInstanceAs (Subsingleton (Spec (.of K)))
    exact ⟨z, Subsingleton.elim _ _⟩
  have : Surjective (Limits.pullback.fst (F.map (toEtalePoint U))
      (F.map (toEtalePoint (etaleSpec K L)))) := inferInstance
  have : Surjective (F.map (pullback.fst (toEtalePoint U) (toEtalePoint (etaleSpec K L)))) := by
    rw [← e]
    infer_instance
  exact this.surj

variable {L}

/-- The action of a `K`-automorphism `σ` of `L` on `U ×_K Spec L`. -/
noncomputable def prodEtaleSpecMap (U : (Spec (.of K)).Etale) (σ : L ≃ₐ[K] L) :
    prodEtaleSpec L U ⟶ prodEtaleSpec L U :=
  pullback.map _ _ _ _ (𝟙 U) (etaleSpecMap σ.toAlgHom) (𝟙 _)
    (isTerminalEtalePoint.hom_ext _ _) (isTerminalEtalePoint.hom_ext _ _)

@[reassoc (attr := simp)]
lemma prodEtaleSpecMap_fst (U : (Spec (.of K)).Etale) (σ : L ≃ₐ[K] L) :
    prodEtaleSpecMap U σ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [prodEtaleSpecMap, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma prodEtaleSpecMap_snd (U : (Spec (.of K)).Etale) (σ : L ≃ₐ[K] L) :
    prodEtaleSpecMap U σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ etaleSpecMap σ.toAlgHom := by
  rw [prodEtaleSpecMap, pullback.lift_snd]

/-- **Galois descent along `U ×_K Spec L ⟶ U`.** For a finite Galois extension `L/K`, a section
of an abelian étale sheaf over `U ×_K Spec L` which is invariant under the automorphisms of
`L/K` is the pullback of a unique section over `U`. -/
theorem existsUnique_map_fst_eq [Normal K L]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : (Spec (.of K)).Etale) (x : F.obj.obj (op (prodEtaleSpec L U)))
    (hx : ∀ σ, F.obj.map (prodEtaleSpecMap U σ).op x = x) :
    ∃! y, F.obj.map (pullback.fst _ _).op y = x := by
  refine existsUnique_map_eq_of_forall_map_eq F _ (surjective_fst_prodEtaleSpec L U)
    (prodEtaleSpecMap U) (fun E _ _ _ g₁ g₂ hg ↦ ?_) x hx
  obtain ⟨φ₁, hφ₁⟩ := exists_etaleSpecMap_eq (g₁ ≫ pullback.snd _ _)
  obtain ⟨φ₂, hφ₂⟩ := exists_etaleSpecMap_eq (g₂ ≫ pullback.snd _ _)
  obtain ⟨σ, hσ⟩ := φ₁.exists_comp_eq_of_normal φ₂
  refine ⟨σ, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, prodEtaleSpecMap_fst, hg]
  · rw [Category.assoc, prodEtaleSpecMap_snd, ← Category.assoc, ← hφ₁, ← hφ₂,
      etaleSpecMap_comp, hσ]

end Product

end AlgebraicGeometry.Scheme
