/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Equivariant epimorphic generator sites

Source: Stacks Project, Sites, Tags 03A1 and 03CI
(blueprint: lem-pur-invariant-generator-site).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem epi_of_support
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} (F : E ⥤ Sheaf J (Type u))
    {T : E} {R S : PreZeroHypercover.{u} T} (h : R.presieve₀ = S.presieve₀)
    (hS : ⟨T, S⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F) :
    ⟨T, R⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F := by
  intro B f g hfg
  apply hS B f g
  intro i
  have hi : R.presieve₀ (S.f i) := h ▸ S.presieve₀_f i
  rw [hi.eq_eqToHom_comp_hom_idx, F.map_comp, Category.assoc, hfg hi.idx]
  simp only [Category.assoc]

private theorem epi_map
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} (H : D ⥤ Sheaf J (Type u))
    (s : D ≌ D) (σ : Sheaf J (Type u) ≌ Sheaf J (Type u))
    (a : s.functor ⋙ H ≅ H ⋙ σ.functor)
    {T : D} (R : PreZeroHypercover.{u} T)
    (hR : ⟨T, R⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} H) :
    ⟨s.functor.obj T, R.map s.functor⟩ ∈
      sheafSubcategoryEpimorphicFamilies.{u, u, 0} H := by
  intro B f g hfg
  apply (cancel_epi (a.inv.app T)).1
  apply (σ.toAdjunction.homEquiv _ _).injective
  apply hR
  intro i
  rw [← σ.toAdjunction.homEquiv_naturality_left,
    ← σ.toAdjunction.homEquiv_naturality_left]
  congr 1
  have hn := a.inv.naturality (R.f i)
  change σ.functor.map (H.map (R.f i)) ≫ a.inv.app T =
    a.inv.app (R.X i) ≫ H.map (s.functor.map (R.f i)) at hn
  have hh := congrArg (fun k ↦ a.inv.app (R.X i) ≫ k) (hfg i)
  change a.inv.app (R.X i) ≫ (H.map (s.functor.map (R.f i)) ≫ f) =
    a.inv.app (R.X i) ≫ (H.map (s.functor.map (R.f i)) ≫ g) at hh
  simpa only [← Category.assoc, ← hn] using hh

private def inverse_intertwiner
    {D E : Type*} [Category D] [Category E]
    (H : D ⥤ E) (s : D ≌ D) (σ : E ≌ E)
    (a : s.functor ⋙ H ≅ H ⋙ σ.functor) :
    s.inverse ⋙ H ≅ H ⋙ σ.inverse :=
  (s.inverse ⋙ H).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft _ σ.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ a.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight s.counitIso H ≪≫ H.leftUnitor) σ.inverse

private theorem continuous_of_coverings
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D) (hJ : J.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f) :
    f.IsContinuous J.toGrothendieck K.toGrothendieck := by
  let : J.HasPullbacks := ⟨by
    intro X Y R b hR
    obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨P, p, q, hpb, hp⟩ := hJ.2.2 I Y U a hR X b
    exact ⟨by
      rintro Z a ⟨i⟩
      exact (hpb i).flip.hasPullback⟩⟩
  refine ⟨fun G ↦ ?_⟩
  rw [J.isSheaf_toGrothendieck_iff]
  intro X Y b R hR
  obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨P, p, q, hpb, hp⟩ := hJ.2.2 I X U a hR Y b
  rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hpb,
    Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
  let : (Presieve.ofArrows P p).HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hp
  let : f.PreservesPairwisePullbacks (Presieve.ofArrows P p) :=
    ⟨fun A B a b ha hb ↦ hpullback Y A B _ hp a b ha⟩
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks f G.obj _).2
  exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
    (hcover _ _ hp)

/-- The epimorphic presieves of full finite-limit generators form an invariant site.

Source: Stacks Project, Sites, Tags 03A1 and 03CI
(blueprint: lem-pur-invariant-generator-site).

Proof: Apply the full-subcategory comparison with no prescribed families. Its
covering supports are exactly the epimorphic families: joint cancellation depends
only on the support. Map a covering family by the site equivalence. The given
intertwiner identifies its image under H with the ambient equivalence applied to
the original family. The adjunction Hom bijections transfer joint cancellation.
The inverse intertwiner follows from the units and counits and gives the reverse
cover preservation. Both equivalence functors preserve pullbacks, so the sheaf
condition for covering pullback families proves continuity. The comparison theorem
also provides the explicit restricted Yoneda nerve isomorphism.
-/
theorem invariantGeneratorSite
    {C D : Type u} [SmallCategory C] [SmallCategory D] [HasFiniteLimits D]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (H : D ⥤ Sheaf J.toGrothendieck (Type u))
    [H.Full] [H.Faithful] [PreservesFiniteLimits H]
    (s : D ≌ D) (σ : Sheaf J.toGrothendieck (Type u) ≌
      Sheaf J.toGrothendieck (Type u))
    (a : s.functor ⋙ H ≅ H ⋙ σ.functor)
    (hrep : ∀ U : C, ∃ A : D,
      Nonempty (H.obj A ≅
        (presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U))) :
    ∃ (K : Precoverage D) (_ : K.IsSiteForCoverings)
      (e : Sheaf J.toGrothendieck (Type u) ≌ Sheaf K.toGrothendieck (Type u)),
      Nonempty (e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅
        sheafSubcategoryNerve H) ∧
      (∀ U (R : Presieve U), R ∈ K U → R.map s.functor ∈ K (s.functor.obj U)) ∧
      (∀ U (R : Presieve U), R ∈ K U → R.map s.inverse ∈ K (s.inverse.obj U)) ∧
      s.functor.IsContinuous K.toGrothendieck K.toGrothendieck ∧
      s.inverse.IsContinuous K.toGrothendieck K.toGrothendieck := by
  classical
  have hpb : ∀ (A B T : D) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : D) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (H.map p) (H.map q) (H.map f) (H.map g) := by
    intro A B T f g
    exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
      (IsPullback.of_hasPullback f g).map H⟩
  obtain ⟨_, Cov, K, hK, e, _, _, hsub, _, hsite, hsupp, hmem, hnerve, _⟩ :=
    sheafSubcategory_comparison.{u, u, 0} J hJ H hrep hpb
      ∅ (by infer_instance) (by simp)
  have hepi : ∀ T (R : PreZeroHypercover.{u} T), R.presieve₀ ∈ K T ↔
      ⟨T, R⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} H := by
    intro T R
    constructor
    · intro h
      obtain ⟨S, hS, heq⟩ := (hmem T R.presieve₀).1 h
      exact epi_of_support H heq (hsub hS)
    · intro h
      obtain ⟨S, hS, heq⟩ := hsupp T R h
      exact (hmem T _).2 ⟨S, hS, heq⟩
  have hf : ∀ U (R : Presieve U), R ∈ K U →
      R.map s.functor ∈ K (s.functor.obj U) := by
    intro U R hR
    have h := epi_map H s σ a R.preZeroHypercover
      ((hepi U _).1 (by simpa using hR))
    simpa only [PreZeroHypercover.presieve₀_map,
      Presieve.presieve₀_preZeroHypercover] using (hepi _ _).2 h
  have hi : ∀ U (R : Presieve U), R ∈ K U →
      R.map s.inverse ∈ K (s.inverse.obj U) := by
    intro U R hR
    have h := epi_map H s.symm σ.symm (inverse_intertwiner H s σ a)
      R.preZeroHypercover ((hepi U _).1 (by simpa using hR))
    have h' := (hepi _ _).2 h
    change (R.preZeroHypercover.map s.inverse).presieve₀ ∈ K (s.inverse.obj U) at h'
    simpa only [PreZeroHypercover.presieve₀_map,
      Presieve.presieve₀_preZeroHypercover] using h'
  exact ⟨K, hsite, e, hnerve, hf, hi,
    continuous_of_coverings K K hsite s.functor hf (by intros; infer_instance),
    continuous_of_coverings K K hsite s.inverse hi (by intros; infer_instance)⟩

end CategoryTheory
