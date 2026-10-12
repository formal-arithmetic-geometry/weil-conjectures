/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyBijective

/-!
# Passing the eight curve assertions to the kernel of an epimorphism

Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence of étale sheaves of `Λ`-modules on a
`k`-scheme `X` such that `C` has no cohomology in positive degrees, also after restriction to
any open subscheme. Then the eight curve assertions `C(X, B)` and `C(X, C)` imply `C(X, A)`
(provided the coefficient hypotheses of the assertions for `A` imply those for `B` and `C`):
in degrees at least two the map `Hᵠ(A) ⟶ Hᵠ(B)` is bijective, and in low degrees the long
exact sequence `0 → H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → 0`, together with its pullback
along a field extension, and the five lemma, transfer finiteness and bijectivity.

This is the half of the dense-open localisation (blueprint
`lemma-weil-pbc-curve-dense-open-reduction`) not covered by the dévissage
`AlgebraicGeometry.IsCurve.Assertions.of_shortExact`.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_δSucc`: the pullback map on étale cohomology commutes
  with the connecting maps of the long exact sequence.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_X₁_of_shortExact`: the five lemma for the
  pullback maps on the long exact cohomology sequences.
- `AlgebraicGeometry.IsCurve.Assertions.of_shortExact_of_subsingleton`: the transfer of the
  eight assertions to the kernel `A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry

namespace Etale

section Forget

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

/-- Taking underlying abelian sheaves of étale sheaves of `Λ`-modules is additive. -/
instance additive_sheafCompose_forget₂_moduleCat :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive where
  map_add := by
    intros
    rfl

/-- Taking underlying abelian sheaves of étale sheaves of `Λ`-modules is left exact: it
commutes with `sheafToPresheaf`, which creates limits, and `forget₂` preserves limits. -/
instance preservesFiniteLimits_sheafCompose_forget₂_moduleCat :
    PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

variable {Λ} in
/-- The underlying abelian sheaves of a short exact sequence of étale sheaves of `Λ`-modules
form a short exact sequence. -/
lemma shortExact_map_sheafCompose_forget₂
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact) :
    (S.map (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hg : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 inferInstance
  have : Sheaf.IsLocallySurjective ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map S.g) :=
    ⟨fun s ↦ hg.imageSieve_mem s⟩
  exact { exact := hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
          mono_f := Functor.map_mono (sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) S.f
          epi_g := Sheaf.epi_of_isLocallySurjective ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map S.g) }

end Forget

section LongExact

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)

include hS in
/-- The pullback of a short exact sequence of abelian étale sheaves is short exact. -/
lemma shortExact_map_upperStar : (S.map (f)^*[AddCommGrpCat.{u + 1}]).ShortExact :=
  hS.map_of_exact _

/-- **The pullback map on cohomology commutes with the connecting maps** of the long exact
cohomology sequence of a short exact sequence `S` of abelian étale sheaves and of its
pullback `f^* S`. -/
lemma cohomologyMap_δSucc (n : ℕ) (x : Sheaf.H S.X₃ n) :
    cohomologyMap f S.X₁ (n + 1) (Sheaf.H.δSucc hS n x) =
      Sheaf.H.δSucc (shortExact_map_upperStar f hS) n (cohomologyMap f S.X₃ n x) := by
  rw [Sheaf.H.δSucc_apply, Sheaf.H.δSucc_apply, cohomologyMap_apply, cohomologyMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

include hS in
/-- **The five lemma for pullback maps on cohomology.** Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a
short exact sequence of abelian étale sheaves on `Y` and `f : X ⟶ Y` a morphism of schemes.
If the pullback maps `Hⁿ(Y, S.Xᵢ) ⟶ Hⁿ(X, f^* S.Xᵢ)` are bijective for `i = 2, 3` and every
`n`, then so are those for `i = 1`. -/
lemma bijective_cohomologyMap_X₁_of_shortExact
    (h₂ : ∀ n, Function.Bijective (cohomologyMap f S.X₂ n))
    (h₃ : ∀ n, Function.Bijective (cohomologyMap f S.X₃ n)) (n : ℕ) :
    Function.Bijective (cohomologyMap f S.X₁ n) := by
  have hS' := shortExact_map_upperStar f hS
  rcases n with _ | n
  · exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      (Sheaf.H.map S.f 0) (Sheaf.H.map S.g 0)
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.f) 0)
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.g) 0)
      (cohomologyMap f S.X₁ 0) (cohomologyMap f S.X₂ 0) (cohomologyMap f S.X₃ 0)
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map f 0 S.f x).symm)
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map f 0 S.g x).symm)
      (Sheaf.H.exact_map_map hS 0) (Sheaf.H.exact_map_map hS' 0) (h₂ 0) (h₃ 0).1
      (have := hS.mono_f; Ext.postcomp_mk₀_injective_of_mono _ S.f)
      (by
        have : Mono ((f)^*[AddCommGrpCat.{u + 1}].map S.f) := hS'.mono_f
        exact Ext.postcomp_mk₀_injective_of_mono _ _)
  · exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (Sheaf.H.map S.g n) (Sheaf.H.δSucc hS n) (Sheaf.H.map S.f (n + 1))
      (Sheaf.H.map S.g (n + 1))
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.g) n) (Sheaf.H.δSucc hS' n)
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.f) (n + 1))
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.g) (n + 1))
      (cohomologyMap f S.X₂ n) (cohomologyMap f S.X₃ n) (cohomologyMap f S.X₁ (n + 1))
      (cohomologyMap f S.X₂ (n + 1)) (cohomologyMap f S.X₃ (n + 1))
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map f n S.g x).symm)
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_δSucc f hS n x).symm)
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map f (n + 1) S.f x).symm)
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map f (n + 1) S.g x).symm)
      (Sheaf.H.exact_map_δSucc hS n) (Sheaf.H.exact_δSucc_map hS n)
      (Sheaf.H.exact_map_map hS (n + 1)) (Sheaf.H.exact_map_δSucc hS' n)
      (Sheaf.H.exact_δSucc_map hS' n) (Sheaf.H.exact_map_map hS' (n + 1))
      (h₂ n).2 (h₃ n) (h₂ (n + 1)) (h₃ (n + 1)).1

include hS in
/-- In a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of abelian étale sheaves, if
`Hⁿ(S.X₃)` and `Hⁿ⁺¹(S.X₂)` are finite, so is `Hⁿ⁺¹(S.X₁)`. -/
lemma finite_H_X₁_of_shortExact (n : ℕ) [Finite (Sheaf.H S.X₃ n)]
    [Finite (Sheaf.H S.X₂ (n + 1))] : Finite (Sheaf.H S.X₁ (n + 1)) := by
  let K := (Sheaf.H.map S.f (n + 1)).ker
  have hK : Finite K := by
    have : (Sheaf.H.δSucc hS n).range = K := by
      ext x
      exact (Sheaf.H.exact_δSucc_map hS n x).symm
    rw [← this]
    exact Set.finite_range _ |>.to_subtype
  have : Finite (Sheaf.H S.X₁ (n + 1) ⧸ K) :=
    Finite.of_injective _ (QuotientAddGroup.kerLift_injective (Sheaf.H.map S.f (n + 1)))
  exact (finite_iff_addSubgroup_quotient K).2 ⟨hK, this⟩

include hS in
/-- In a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of abelian étale sheaves, if
`H⁰(S.X₂)` is finite, so is `H⁰(S.X₁)`. -/
lemma finite_H_zero_X₁_of_shortExact [Finite (Sheaf.H S.X₂ 0)] :
    Finite (Sheaf.H S.X₁ 0) :=
  have := hS.mono_f
  Finite.of_injective _ (Ext.postcomp_mk₀_injective_of_mono _ S.f)

include hS in
/-- In a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of abelian étale sheaves, if
`Hⁿ(S.X₃) = 0` and `Hⁿ⁺¹(S.X₂) = 0`, then `Hⁿ⁺¹(S.X₁) = 0`. -/
lemma subsingleton_H_X₁_of_shortExact (n : ℕ) [Subsingleton (Sheaf.H S.X₃ n)]
    [Subsingleton (Sheaf.H S.X₂ (n + 1))] : Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, ha⟩ := (Sheaf.H.exact_δSucc_map hS n x).1 (Subsingleton.elim _ _)
  obtain ⟨b, hb⟩ := (Sheaf.H.exact_δSucc_map hS n y).1 (Subsingleton.elim _ _)
  rw [← ha, ← hb, Subsingleton.elim a b]

end LongExact

section Retract

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (i : G ⟶ F) (r : F ⟶ G) (hir : i ≫ r = 𝟙 G)

/-- The cohomology of a zero sheaf vanishes. -/
lemma subsingleton_H_of_isZero (hG : IsZero G) (n : ℕ) : Subsingleton (Sheaf.H G n) := by
  have h (z : Sheaf.H G n) : z = 0 := by
    rw [← Ext.comp_mk₀_id z, hG.eq_of_src (𝟙 G) 0, Ext.mk₀_zero, Ext.comp_zero]
  exact ⟨fun x y ↦ by rw [h x, h y]⟩

include hir in
/-- The map induced on cohomology by a section of a retraction is injective. -/
lemma injective_H_map_of_retract (n : ℕ) : Function.Injective (Sheaf.H.map i n) :=
  Function.LeftInverse.injective (g := Sheaf.H.map r n) fun x ↦ by
    rw [← Sheaf.H.map_comp_apply, hir, Sheaf.H.map_id_apply]

include hir in
/-- A retract of a sheaf whose pullback map on `Hⁿ` is surjective has a surjective pullback map
on `Hⁿ`. -/
lemma surjective_cohomologyMap_of_retract (n : ℕ)
    (hF : Function.Surjective (cohomologyMap g F n)) :
    Function.Surjective (cohomologyMap g G n) := by
  intro y
  obtain ⟨z, hz⟩ := hF (Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map i) n y)
  refine ⟨Sheaf.H.map r n z, ?_⟩
  rw [cohomologyMap_map, hz, ← Sheaf.H.map_comp_apply, ← Functor.map_comp, hir,
    CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]

include hir in
/-- A retract of a sheaf whose pullback map on `Hⁿ` is bijective has a bijective pullback map
on `Hⁿ`. -/
lemma bijective_cohomologyMap_of_retract (n : ℕ)
    (hF : Function.Bijective (cohomologyMap g F n)) :
    Function.Bijective (cohomologyMap g G n) := by
  refine ⟨fun x y h ↦ injective_H_map_of_retract i r hir n (hF.1 ?_),
    surjective_cohomologyMap_of_retract g i r hir n hF.2⟩
  rw [cohomologyMap_map, cohomologyMap_map, h]

end Retract

end Etale

namespace IsCurve

open Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)}

/-- **The eight curve assertions for the zero sheaf**: all cohomology groups, also after any
pullback, vanish. -/
theorem Assertions.of_isZero {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hG : IsZero G) : Assertions Λ f G := by
  have h₀ : IsZero ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) :=
    Functor.map_isZero _ hG
  have hX := subsingleton_H_of_isZero h₀
  have hY {Y : Scheme.{u}} (g : Y ⟶ X) := subsingleton_H_of_isZero
    (Functor.map_isZero (g)^*[AddCommGrpCat.{u + 1}] h₀)
  have hbij {Y : Scheme.{u}} (g : Y ⟶ X) (q : ℕ) :
      Function.Bijective (cohomologyMap g
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q) :=
    have := hX q
    have := hY g q
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  exact ⟨fun q _ ↦ hX q, fun q _ ↦ hX q, fun _ _ _ _ q _ ↦ hX q,
    fun q ↦ have := hX q; Finite.of_subsingleton, fun q ↦ have := hX q; Finite.of_subsingleton,
    fun _ _ _ _ _ _ ι' _ q ↦ hbij ι' q, fun _ _ _ _ _ _ ι' _ q ↦ hbij ι' q,
    fun a _ ↦ (hbij a 2).2⟩

/-- **The eight curve assertions pass to retracts.** Let `G` be a retract of an étale sheaf `F`
of `Λ`-modules on `X` (`i : G ⟶ F`, `r : F ⟶ G`, `i ≫ r = 𝟙 G`), and suppose that the
coefficient hypotheses of the assertions `C₃`, `C₄`, `C₆` for `G` imply those for `F`, unless
`G` is zero. Then `C(X, F)` implies `C(X, G)`: the cohomology of `G` and its pullback maps are
retracts of those of `F`. -/
theorem Assertions.of_retract {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (i : G ⟶ F) (r : F ⟶ G) (hir : i ≫ r = 𝟙 G) (hF : Assertions Λ f F)
    (hprim : ∀ (p : ℕ), Scheme.IsPrimaryTorsionSheaf Λ G p →
      Scheme.IsPrimaryTorsionSheaf Λ F p ∨ IsZero G)
    (hcons : Scheme.IsConstructibleSheaf G → Scheme.IsConstructibleSheaf F)
    (hinv : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨ IsZero G) :
    Assertions Λ f G := by
  set Φ := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hir' : Φ.map i ≫ Φ.map r = 𝟙 _ := by rw [← Φ.map_comp, hir, Φ.map_id]
  have hinj (q : ℕ) := injective_H_map_of_retract (Φ.map i) (Φ.map r) hir' q
  by_cases hG : IsZero G
  · exact Assertions.of_isZero hG
  refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_, fun p _ _ hp q hq ↦ ?_, fun q ↦ ?_, fun q ↦ ?_,
    fun k' _ _ X' ι f' ι' h q ↦ ?_, fun k' _ _ X' ι f' ι' h q ↦ ?_, fun {W} a _ ↦ ?_⟩
  · have := hF.subsingleton_of_two_lt q hq
    exact (hinj q).subsingleton
  · have := hF.subsingleton_of_one_lt_of_isAffine q hq
    exact (hinj q).subsingleton
  · rcases hprim p hp with hp' | hp'
    · have := hF.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hp' q hq
      exact (hinj q).subsingleton
    · exact absurd hp' hG
  · rename_i hcG hiG
    have := hcons hcG
    rcases hinv hiG with hiF | hz
    · have := hF.finite_of_isTorsionSheafOfInvertibleOrder q
      exact Finite.of_injective _ (hinj q)
    · exact absurd hz hG
  · rename_i _ hcG
    have := hcons hcG
    have := hF.finite_of_isProper q
    exact Finite.of_injective _ (hinj q)
  · rename_i hiG _ _
    rcases hinv hiG with hiF | hz
    · exact bijective_cohomologyMap_of_retract ι' (Φ.map i) (Φ.map r) hir' q
        (hF.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h q)
    · exact absurd hz hG
  · exact bijective_cohomologyMap_of_retract ι' (Φ.map i) (Φ.map r) hir' q
      (hF.bijective_cohomologyMap_of_isProper k' h q)
  · exact surjective_cohomologyMap_of_retract a (Φ.map i) (Φ.map r) hir' 2
      (hF.surjective_cohomologyMap_of_isOpenImmersion a)

/-- The eight curve assertions are invariant under isomorphism of sheaves. -/
theorem Assertions.of_iso {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : G ≅ F)
    (hF : Assertions Λ f F)
    (hprim : ∀ (p : ℕ), Scheme.IsPrimaryTorsionSheaf Λ G p → Scheme.IsPrimaryTorsionSheaf Λ F p)
    (hinv : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F) :
    Assertions Λ f G :=
  hF.of_retract e.hom e.inv e.hom_inv_id (fun p hp ↦ .inl (hprim p hp))
    (fun _ ↦ Scheme.IsConstructibleSheaf.of_iso e) (fun h ↦ .inl (hinv h))
/-- **The eight curve assertions pass to the kernel of an epimorphism onto an acyclic sheaf.**
Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence of étale sheaves of `Λ`-modules on a
`k`-scheme `X`, such that `C` has no cohomology in positive degrees, and neither have its
restrictions to the open subschemes of `X`. Suppose that the coefficient hypotheses of the
assertions `C₃`, `C₄`, `C₆` for `A` imply the corresponding ones for `B` and `C`, unless the
cohomology of `A` vanishes. Then `C(X, B)` and `C(X, C)` imply `C(X, A)`.

In degrees at least two `Hᵠ(A) ⟶ Hᵠ(B)` is bijective, and in low degrees one uses the long
exact sequence `0 → H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → 0`, its pullback along a field
extension, and the five lemma (blueprint `lemma-weil-pbc-curve-dense-open-reduction`). -/
theorem Assertions.of_shortExact_of_subsingleton
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (hB : Assertions Λ f S.X₂) (hC : Assertions Λ f S.X₃)
    (hvan : ∀ q, Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj S.X₃) (q + 1)))
    (hvan' : ∀ {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a] (q : ℕ),
      Subsingleton (Sheaf.H ((a)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj S.X₃))
          (q + 1)))
    (hprim : ∀ (p : ℕ), Scheme.IsPrimaryTorsionSheaf Λ S.X₁ p →
      Scheme.IsPrimaryTorsionSheaf Λ S.X₂ p ∨ IsZero S.X₁)
    (hcons : Scheme.IsConstructibleSheaf S.X₁ →
      Scheme.IsConstructibleSheaf S.X₂ ∧ Scheme.IsConstructibleSheaf S.X₃)
    (hinv : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) S.X₁ →
      (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) S.X₂ ∧
        Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) S.X₃) ∨
      IsZero S.X₁) :
    Assertions Λ f S.X₁ := by
  set Φ := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hT : (S.map Φ).ShortExact := shortExact_map_sheafCompose_forget₂ hS
  -- vanishing in degrees `q ≥ 2` transfers from `B` to `A`
  have hsub (q : ℕ) (hq : 1 < q) (hBq : Subsingleton (Sheaf.H (Φ.obj S.X₂) q)) :
      Subsingleton (Sheaf.H (Φ.obj S.X₁) q) := by
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 + 1 := ⟨q - 2, by omega⟩
    have : Subsingleton (Sheaf.H (S.map Φ).X₃ (n + 1)) := hvan n
    have : Subsingleton (Sheaf.H (S.map Φ).X₂ (n + 1 + 1)) := hBq
    exact subsingleton_H_X₁_of_shortExact hT (n + 1)
  -- finiteness transfers from `B` and `C` to `A`
  have hfin (hB' : ∀ q, Finite (Sheaf.H (Φ.obj S.X₂) q))
      (hC' : ∀ q, Finite (Sheaf.H (Φ.obj S.X₃) q)) (q : ℕ) :
      Finite (Sheaf.H (Φ.obj S.X₁) q) := by
    rcases q with _ | q
    · have : Finite (Sheaf.H (S.map Φ).X₂ 0) := hB' 0
      exact finite_H_zero_X₁_of_shortExact hT
    · have : Finite (Sheaf.H (S.map Φ).X₂ (q + 1)) := hB' (q + 1)
      have : Finite (Sheaf.H (S.map Φ).X₃ q) := hC' q
      exact finite_H_X₁_of_shortExact hT q
  by_cases hA : IsZero S.X₁
  · exact Assertions.of_isZero hA
  refine ⟨fun q hq ↦ hsub q (by omega) (hB.subsingleton_of_two_lt q hq),
    fun q hq ↦ hsub q hq (hB.subsingleton_of_one_lt_of_isAffine q hq),
    fun p _ _ hp q hq ↦ ?_, fun q ↦ ?_, fun q ↦ ?_, fun k' _ _ X' ι f' ι' h q ↦ ?_,
    fun k' _ _ X' ι f' ι' h q ↦ ?_, fun {W} a _ ↦ ?_⟩
  · rcases hprim p hp with hp' | hp'
    · exact hsub q hq (hB.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hp' q hq)
    · exact absurd hp' hA
  · rename_i hcA hiA
    obtain ⟨hcB, hcC⟩ := hcons hcA
    rcases hinv hiA with ⟨hiB, hiC⟩ | hz
    · exact hfin (hB.finite_of_isTorsionSheafOfInvertibleOrder)
        (hC.finite_of_isTorsionSheafOfInvertibleOrder) q
    · exact absurd hz hA
  · rename_i hp hcA
    obtain ⟨hcB, hcC⟩ := hcons hcA
    exact hfin hB.finite_of_isProper hC.finite_of_isProper q
  · rename_i hiA _ _
    rcases hinv hiA with ⟨hiB, hiC⟩ | hz
    · exact bijective_cohomologyMap_X₁_of_shortExact ι' hT
        (hB.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h)
        (hC.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h) q
    · exact absurd hz hA
  · exact bijective_cohomologyMap_X₁_of_shortExact ι' hT
      (hB.bijective_cohomologyMap_of_isProper k' h)
      (hC.bijective_cohomologyMap_of_isProper k' h) q
  · -- `C₈`: `H²(A) ⟶ H²(B)` is bijective, on `X` and on `W`
    have hT' := shortExact_map_upperStar a hT
    have : Subsingleton (Sheaf.H (S.map Φ).X₃ 1) := hvan 0
    have : Subsingleton (Sheaf.H (S.map Φ).X₃ (1 + 1)) := hvan 1
    have : Subsingleton (Sheaf.H ((S.map Φ).map (a)^*[AddCommGrpCat.{u + 1}]).X₃ 1) :=
      hvan' a 0
    have : Subsingleton (Sheaf.H ((S.map Φ).map (a)^*[AddCommGrpCat.{u + 1}]).X₃ (1 + 1)) :=
      hvan' a 1
    have hX : Function.Bijective (Sheaf.H.map (S.map Φ).f (1 + 1)) :=
      Sheaf.H.bijective_map_f (S := S.map Φ) hT 1
    have hW : Function.Bijective (Sheaf.H.map ((S.map Φ).map
        (a)^*[AddCommGrpCat.{u + 1}]).f (1 + 1)) :=
      Sheaf.H.bijective_map_f (S := (S.map Φ).map (a)^*[AddCommGrpCat.{u + 1}]) hT' 1
    intro y
    obtain ⟨x, hx⟩ := hB.surjective_cohomologyMap_of_isOpenImmersion a
      (Sheaf.H.map ((S.map Φ).map (a)^*[AddCommGrpCat.{u + 1}]).f 2 y)
    obtain ⟨z, rfl⟩ := hX.2 x
    refine ⟨z, hW.1 ?_⟩
    rw [← hx]
    exact (cohomologyMap_map a 2 (S.map Φ).f z).symm

end IsCurve

end AlgebraicGeometry
