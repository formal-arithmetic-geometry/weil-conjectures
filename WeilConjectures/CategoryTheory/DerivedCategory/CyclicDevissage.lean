/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dévissage over cyclic modules

Let `Λ` be a commutative ring in which every ideal is the annihilator of a single element (for
instance a finite local principal ideal ring such as `ℤ/ℓⁿ` or `𝒪_E/ϖⁿ`). Let
`Φ, Ψ : ModuleCat Λ ⥤ D(C)` be functors carrying short exact sequences to distinguished
triangles, and `φ : Φ ⟶ Ψ`. If `φ` is an isomorphism at `Λ`, both functors are concentrated in
degree `0` at `Λ`, uniformly bounded below on the cyclic modules `Λ ⧸ J`, and `H⁰ Φ` carries
the quotient maps `Λ ⟶ Λ ⧸ J` to epimorphisms, then `φ` is an isomorphism at every cyclic
module `Λ ⧸ J`.

## Main statements

- `DerivedCategory.isIso_app_quotient_of_devissage`
-/

@[expose] public section

universe w v u' u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u'} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {Λ : Type u} [CommRing Λ]

/-- The short complex `0 ⟶ Λ ⧸ J ⟶ Λ ⟶ Λ ⧸ (a) ⟶ 0` of `Λ`-modules attached to an element `a`
whose annihilator is `J`: the first map is induced by `x ↦ x * a` and the second one is the
quotient map. -/
noncomputable abbrev cyclicShortComplex (J : Ideal Λ) (a : Λ) (ha : ∀ x : Λ, x * a = 0 ↔ x ∈ J) :
    ShortComplex (ModuleCat.{u} Λ) :=
  ShortComplex.mk
    (ModuleCat.ofHom (X := ModuleCat.of Λ (Λ ⧸ J)) (Y := ModuleCat.of Λ Λ)
      (J.liftQ (LinearMap.mulRight Λ a) fun x hx => by simpa using (ha x).2 hx))
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ (Ideal.span {a})).toLinearMap)
    (by
      ext
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton'.2 ⟨1, rfl⟩))

/-- If the annihilator of `a` is `J`, then `0 ⟶ Λ ⧸ J ⟶ Λ ⟶ Λ ⧸ (a) ⟶ 0` is short exact. -/
lemma cyclicShortComplex_shortExact (J : Ideal Λ) (a : Λ)
    (ha : ∀ x : Λ, x * a = 0 ↔ x ∈ J) : (cyclicShortComplex J a ha).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ((Ideal.Quotient.eq_zero_iff_mem).1 hx)
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    replace hxy : x * a = y * a := hxy
    refine (Submodule.Quotient.eq J).2 ?_
    rw [← ha, sub_mul, hxy, sub_self]
  · rw [ModuleCat.epi_iff_surjective]
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, rfl⟩

/-- A functor carrying short exact sequences to distinguished triangles carries the two maps of a
short exact sequence to morphisms with zero composition. -/
lemma map_f_comp_map_g_eq_zero {F : ModuleCat.{u} Λ ⥤ DerivedCategory C}
    (hF : ∀ S : ShortComplex (ModuleCat.{u} Λ), S.ShortExact →
      ∃ δ, Triangle.mk (F.map S.f) (F.map S.g) δ ∈ distTriang _)
    (S : ShortComplex (ModuleCat.{u} Λ)) (hS : S.ShortExact) : F.map S.f ≫ F.map S.g = 0 := by
  obtain ⟨δ, hT⟩ := hF S hS
  exact comp_distTriang_mor_zero₁₂ _ hT

/-- Let `F` carry short exact sequences to distinguished triangles and let `Ann(a) = J`. If
`Hᵠ F(Λ) = 0` and `H^{q₀} F` carries `Λ ⟶ Λ ⧸ (a)` to an epimorphism, where `q₀ + 1 = q`, then
`Hᵠ F(Λ ⧸ J) = 0`. -/
lemma isZero_homology_obj_quotient_of_epi {F : ModuleCat.{u} Λ ⥤ DerivedCategory C}
    (hF : ∀ S : ShortComplex (ModuleCat.{u} Λ), S.ShortExact →
      ∃ δ, Triangle.mk (F.map S.f) (F.map S.g) δ ∈ distTriang _)
    (J : Ideal Λ) (a : Λ) (ha : ∀ x : Λ, x * a = 0 ↔ x ∈ J) (q₀ q : ℤ) (hq : q₀ + 1 = q)
    (hepi : Epi ((homologyFunctor C q₀).map
      (F.map (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ (Ideal.span {a})).toLinearMap))))
    (hΛ : IsZero ((homologyFunctor C q).obj (F.obj (ModuleCat.of Λ Λ)))) :
    IsZero ((homologyFunctor C q).obj (F.obj (ModuleCat.of Λ (Λ ⧸ J)))) := by
  obtain ⟨δ, hT⟩ := hF _ (cyclicShortComplex_shortExact J a ha)
  exact (HomologySequence.exact₁ _ hT q₀ q hq).isZero_X₂
    ((HomologySequence.epi_homologyMap_mor₂_iff _ hT q₀ q hq).1 hepi) (hΛ.eq_of_tgt _ _)

/-- Let `F` carry short exact sequences to distinguished triangles and let `Ann(a) = J`. If
`H⁻¹ F(Λ ⧸ (a)) = 0`, then `H⁰ F` carries `Λ ⧸ J ⟶ Λ` to a monomorphism. -/
lemma mono_homologyMap_cyclicShortComplex_f {F : ModuleCat.{u} Λ ⥤ DerivedCategory C}
    (hF : ∀ S : ShortComplex (ModuleCat.{u} Λ), S.ShortExact →
      ∃ δ, Triangle.mk (F.map S.f) (F.map S.g) δ ∈ distTriang _)
    (J : Ideal Λ) (a : Λ) (ha : ∀ x : Λ, x * a = 0 ↔ x ∈ J)
    (h : IsZero ((homologyFunctor C (-1)).obj (F.obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {a}))))) :
    Mono ((homologyFunctor C 0).map (F.map (cyclicShortComplex J a ha).f)) := by
  obtain ⟨δ, hT⟩ := hF _ (cyclicShortComplex_shortExact J a ha)
  exact (HomologySequence.mono_homologyMap_mor₁_iff _ hT (-1) 0).2 (h.eq_of_src _ _)

/-- Let `F` carry short exact sequences to distinguished triangles and let `Ann(a) = J`. If
`H⁻¹ F(Λ ⧸ (a)) = 0`, then every morphism to `H⁰ F(Λ)` which vanishes in `H⁰ F(Λ ⧸ (a))` factors
through `H⁰ F(Λ ⧸ J)`. -/
lemma exists_comp_homologyMap_cyclicShortComplex_f {F : ModuleCat.{u} Λ ⥤ DerivedCategory C}
    (hF : ∀ S : ShortComplex (ModuleCat.{u} Λ), S.ShortExact →
      ∃ δ, Triangle.mk (F.map S.f) (F.map S.g) δ ∈ distTriang _)
    (J : Ideal Λ) (a : Λ) (ha : ∀ x : Λ, x * a = 0 ↔ x ∈ J)
    (h : IsZero ((homologyFunctor C (-1)).obj (F.obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {a})))))
    {A : C} (k : A ⟶ (homologyFunctor C 0).obj (F.obj (ModuleCat.of Λ Λ)))
    (hk : k ≫ (homologyFunctor C 0).map (F.map (cyclicShortComplex J a ha).g) = 0) :
    ∃ l, l ≫ (homologyFunctor C 0).map (F.map (cyclicShortComplex J a ha).f) = k := by
  obtain ⟨δ, hT⟩ := hF _ (cyclicShortComplex_shortExact J a ha)
  have := (HomologySequence.mono_homologyMap_mor₁_iff _ hT (-1) 0).2 (h.eq_of_src _ _)
  exact ⟨(HomologySequence.exact₂ _ hT 0).lift k hk, (HomologySequence.exact₂ _ hT 0).lift_f k hk⟩

/-- **Dévissage over cyclic modules.** Let `Λ` be a commutative ring in which every ideal is the
annihilator of a single element, and `φ : Φ ⟶ Ψ` a natural transformation between functors
`ModuleCat Λ ⥤ D(C)` carrying short exact sequences to distinguished triangles. Assume that
`φ` is an isomorphism at `Λ`, that `Φ(Λ)` is concentrated in degree `0`, that `Φ` and `Ψ` are
uniformly bounded below on the cyclic modules, and that `H⁰ Φ` carries the quotient maps
`Λ ⟶ Λ ⧸ J` to epimorphisms. Then `φ` is an isomorphism at every cyclic module `Λ ⧸ J`.

The proof uses, for each ideal `J = Ann(a)`, the short exact sequence
`0 ⟶ Λ ⧸ J ⟶ Λ ⟶ Λ ⧸ (a) ⟶ 0`: below degree `0` the homology of `Φ` and `Ψ` at `Λ ⧸ J` is a
homology group of one degree lower at another cyclic module, so it vanishes by the uniform
lower bound; `H⁰` is then left exact on the copresentation `0 ⟶ Λ ⧸ J ⟶ Λ ⟶ Λ`, so `H⁰ φ` is an
isomorphism; this makes `H⁰ Ψ` right exact on `Λ ⟶ Λ ⧸ J`, which kills `H¹`, and the higher
homology is a homology group of one degree lower at another cyclic module. -/
theorem isIso_app_quotient_of_devissage
    (hΛ : ∀ J : Ideal Λ, ∃ a : Λ, ∀ x : Λ, x * a = 0 ↔ x ∈ J)
    {Φ Ψ : ModuleCat.{u} Λ ⥤ DerivedCategory C} (φ : Φ ⟶ Ψ)
    (hΦ : ∀ S : ShortComplex (ModuleCat.{u} Λ), S.ShortExact →
      ∃ δ, Triangle.mk (Φ.map S.f) (Φ.map S.g) δ ∈ distTriang _)
    (hΨ : ∀ S : ShortComplex (ModuleCat.{u} Λ), S.ShortExact →
      ∃ δ, Triangle.mk (Ψ.map S.f) (Ψ.map S.g) δ ∈ distTriang _)
    (h₁ : IsIso (φ.app (ModuleCat.of Λ Λ)))
    (h₀ : ∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor C q).obj (Φ.obj (ModuleCat.of Λ Λ))))
    (m : ℤ) (hm : ∀ (J : Ideal Λ) (q : ℤ), q < m →
      IsZero ((homologyFunctor C q).obj (Φ.obj (ModuleCat.of Λ (Λ ⧸ J)))) ∧
        IsZero ((homologyFunctor C q).obj (Ψ.obj (ModuleCat.of Λ (Λ ⧸ J)))))
    (hepi : ∀ J : Ideal Λ, Epi ((homologyFunctor C 0).map
      (Φ.map (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ J).toLinearMap))))
    (J : Ideal Λ) :
    IsIso (φ.app (ModuleCat.of Λ (Λ ⧸ J))) := by
  choose a ha using hΛ
  have hΨ₀ (q : ℤ) (hq : q ≠ 0) :
      IsZero ((homologyFunctor C q).obj (Ψ.obj (ModuleCat.of Λ Λ))) :=
    (h₀ q hq).of_iso ((homologyFunctor C q).mapIso (asIso (φ.app _))).symm
  -- Step A: vanishing in negative degrees, by descending induction against the bound `m`.
  have hneg (k : ℕ) (J : Ideal Λ) (q : ℤ) (hq : q < 0) (hqk : q < m + k) :
      IsZero ((homologyFunctor C q).obj (Φ.obj (ModuleCat.of Λ (Λ ⧸ J)))) ∧
        IsZero ((homologyFunctor C q).obj (Ψ.obj (ModuleCat.of Λ (Λ ⧸ J)))) := by
    induction k generalizing J q with
    | zero => exact hm J q (by simpa using hqk)
    | succ k ih =>
      have h' := ih (Ideal.span {a J}) (q - 1) (by lia) (by push_cast at hqk; lia)
      exact ⟨isZero_homology_obj_quotient_of_epi hΦ J (a J) (ha J) (q - 1) q (by lia)
          (h'.1.epi _) (h₀ q hq.ne),
        isZero_homology_obj_quotient_of_epi hΨ J (a J) (ha J) (q - 1) q (by lia)
          (h'.2.epi _) (hΨ₀ q hq.ne)⟩
  have hneg' (J : Ideal Λ) (q : ℤ) (hq : q < 0) :=
    hneg (q - m + 1).toNat J q hq (by lia)
  -- Step B: `H⁰ φ` is a monomorphism, then an isomorphism, at every cyclic module.
  have hmono (J : Ideal Λ) : Mono ((homologyFunctor C 0).map (φ.app (ModuleCat.of Λ (Λ ⧸ J)))) := by
    have := mono_homologyMap_cyclicShortComplex_f hΦ J (a J) (ha J)
      (hneg' (Ideal.span {a J}) (-1) (by lia)).1
    have : Mono ((homologyFunctor C 0).map (Φ.map (cyclicShortComplex J (a J) (ha J)).f) ≫
        (homologyFunctor C 0).map (φ.app (ModuleCat.of Λ Λ))) := mono_comp _ _
    rw [← Functor.map_comp, φ.naturality, Functor.map_comp] at this
    exact mono_of_mono _ ((homologyFunctor C 0).map (Ψ.map (cyclicShortComplex J (a J) (ha J)).f))
  have hiso₀ (J : Ideal Λ) :
      IsIso ((homologyFunctor C 0).map (φ.app (ModuleCat.of Λ (Λ ⧸ J)))) := by
    have := mono_homologyMap_cyclicShortComplex_f hΨ J (a J) (ha J)
      (hneg' (Ideal.span {a J}) (-1) (by lia)).2
    have := hmono (Ideal.span {a J})
    obtain ⟨s, hs⟩ := exists_comp_homologyMap_cyclicShortComplex_f hΦ J (a J) (ha J)
      (hneg' (Ideal.span {a J}) (-1) (by lia)).1
      ((homologyFunctor C 0).map (Ψ.map (cyclicShortComplex J (a J) (ha J)).f) ≫
        inv ((homologyFunctor C 0).map (φ.app (ModuleCat.of Λ Λ)))) (by
        rw [← cancel_mono ((homologyFunctor C 0).map
          (φ.app (ModuleCat.of Λ (Λ ⧸ Ideal.span {a J})))), Category.assoc, Category.assoc,
          ← Functor.map_comp, φ.naturality, Functor.map_comp, IsIso.inv_hom_id_assoc,
          ← Functor.map_comp, map_f_comp_map_g_eq_zero hΨ _
            (cyclicShortComplex_shortExact J (a J) (ha J)), Functor.map_zero, zero_comp])
    have hs' : s ≫ (homologyFunctor C 0).map (φ.app (ModuleCat.of Λ (Λ ⧸ J))) = 𝟙 _ := by
      rw [← cancel_mono ((homologyFunctor C 0).map (Ψ.map (cyclicShortComplex J (a J) (ha J)).f)),
        Category.assoc, ← Functor.map_comp, ← φ.naturality, Functor.map_comp, reassoc_of% hs]
      simp
    have : IsSplitEpi ((homologyFunctor C 0).map (φ.app (ModuleCat.of Λ (Λ ⧸ J)))) :=
      IsSplitEpi.mk' ⟨s, hs'⟩
    exact isIso_of_mono_of_epi _
  -- Steps C and D: vanishing in positive degrees, by ascending induction.
  have hpos (k : ℕ) (J : Ideal Λ) :
      IsZero ((homologyFunctor C (k + 1)).obj (Φ.obj (ModuleCat.of Λ (Λ ⧸ J)))) ∧
        IsZero ((homologyFunctor C (k + 1)).obj (Ψ.obj (ModuleCat.of Λ (Λ ⧸ J)))) := by
    induction k generalizing J with
    | zero =>
      have hεΨ := hiso₀ (Ideal.span {a J})
      have : Epi ((homologyFunctor C 0).map
          (Φ.map (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ (Ideal.span {a J})).toLinearMap)) ≫
          (homologyFunctor C 0).map (φ.app (ModuleCat.of Λ (Λ ⧸ Ideal.span {a J})))) := by
        have := hepi (Ideal.span {a J})
        exact epi_comp _ _
      rw [← Functor.map_comp, φ.naturality, Functor.map_comp] at this
      exact ⟨isZero_homology_obj_quotient_of_epi hΦ J (a J) (ha J) 0 _ (by simp)
          (hepi _) (h₀ _ (by simp)),
        isZero_homology_obj_quotient_of_epi hΨ J (a J) (ha J) 0 _ (by simp)
          (epi_of_epi ((homologyFunctor C 0).map (φ.app (ModuleCat.of Λ Λ))) _)
          (hΨ₀ _ (by simp))⟩
    | succ k ih =>
      have h' := ih (Ideal.span {a J})
      exact ⟨isZero_homology_obj_quotient_of_epi hΦ J (a J) (ha J) (k + 1) _ (by push_cast; lia)
          (h'.1.epi _) (h₀ _ (by lia)),
        isZero_homology_obj_quotient_of_epi hΨ J (a J) (ha J) (k + 1) _ (by push_cast; lia)
          (h'.2.epi _) (hΨ₀ _ (by lia))⟩
  rw [isIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact ⟨0, (hneg' J n hn).1.eq_of_src _ _, (hneg' J n hn).2.eq_of_src _ _⟩
  · exact hiso₀ J
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ n - 1)
    obtain rfl : n = k + 1 := by lia
    exact ⟨0, (hpos k J).1.eq_of_src _ _, (hpos k J).2.eq_of_src _ _⟩

end DerivedCategory
