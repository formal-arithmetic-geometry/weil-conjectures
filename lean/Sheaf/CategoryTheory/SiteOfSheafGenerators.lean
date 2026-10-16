/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module
public import Sheaf.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.LeftExact
/-!
# Epimorphic covering presieves on finite-limit sheaf generators

Source: Stacks Project, Sites, Tags 03A1 and 03CI
(blueprint: lem-weil-pbc-site-of-sheaf-generators).
-/

@[expose] public section
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

private theorem siteAxioms_of_familyComparison
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} (F : E ⥤ Sheaf J (Type u))
    (K : Precoverage E)
    (Cov : Set (Σ T : E, PreZeroHypercover.{u} T))
    (hCov : PreZeroHypercover.IsCoveringClass Cov)
    (hsub : Cov ⊆ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F)
    (hmem : ∀ T (S : Presieve T), S ∈ K T ↔
      ∃ R : PreZeroHypercover.{u} T, ⟨T, R⟩ ∈ Cov ∧ S = R.presieve₀)
    (hepi : ∀ T (R : PreZeroHypercover.{u} T), R.presieve₀ ∈ K T ↔
      ⟨T, R⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F) :
    K.HasIsos ∧ K.IsStableUnderComposition ∧ K.IsStableUnderBaseChange := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · intro S T f hf
    exact (hmem T _).2 ⟨.singleton f, hCov.1 T S f hf,
      (PreZeroHypercover.presieve₀_singleton f).symm⟩
  · intro I S X f hf sizes Y g hg
    let R : PreZeroHypercover.{u} S :=
      ⟨Sigma sizes, fun p ↦ Y p.1 p.2, fun p ↦ g p.1 p.2 ≫ f p.1⟩
    apply (hepi S R).2
    intro B a b hab
    apply (hepi S { I₀ := I, X := X, f := f }).1 hf B a b
    intro i
    apply (hepi (X i) { I₀ := sizes i, X := Y i, f := g i }).1 (hg i) B
      (F.map (f i) ≫ a) (F.map (f i) ≫ b)
    intro j
    simpa only [R, Functor.map_comp, Category.assoc] using hab ⟨i, j⟩
  · intro I S X f hf Y g P p q hp
    obtain ⟨R, hR, hRf⟩ := (hmem S _).1 hf
    obtain ⟨Q, a, b, hQ, ha⟩ := hCov.2.2 S R hR Y g
    apply (hepi Y { I₀ := I, X := P, f := p }).2
    intro B x y hxy
    apply hsub ha B x y
    intro i
    have hi : Presieve.ofArrows X f (R.f i) := hRf ▸ R.presieve₀_f i
    let j := hi.idx
    have hw : a i ≫ g = (b i ≫ eqToHom hi.obj_idx.symm) ≫ f j := by
      rw [Category.assoc, ← hi.eq_eqToHom_comp_hom_idx]
      exact (hQ i).w
    let k : Q i ⟶ P j := (hp j).lift (a i) (b i ≫ eqToHom hi.obj_idx.symm) hw
    have hk : k ≫ p j = a i := (hp j).lift_fst _ _ _
    calc
      F.map (a i) ≫ x = F.map k ≫ (F.map (p j) ≫ x) := by
        rw [← Category.assoc, ← F.map_comp, hk]
      _ = F.map k ≫ (F.map (p j) ≫ y) := by rw [hxy j]
      _ = F.map (a i) ≫ y := by rw [← Category.assoc, ← F.map_comp, hk]

private theorem siteForCoverings_of_axioms
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks] :
    J.IsSiteForCoverings := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    let E := R.preZeroHypercover
    let V (i : E.I₀) := (T (E.f i) i.2).preZeroHypercover
    have hE : E.presieve₀ ∈ J X := by simpa [E] using hR
    have hV (i : E.I₀) : (V i).presieve₀ ∈ J (E.X i) := by
      simpa [V] using hT (E.X i) (E.f i) i.2
    have h := Precoverage.comp_mem_coverings E.f hE (fun i ↦ (V i).f) hV
    convert h using 1
    apply le_antisymm
    · rintro Z f ⟨Y, g, a, ha, hg, rfl⟩
      let i : E.I₀ := ⟨⟨Y, a⟩, ha⟩
      let j : (V i).I₀ := ⟨⟨Z, g⟩, hg⟩
      exact Presieve.ofArrows.mk (ι := Σ i : E.I₀, (V i).I₀) ⟨i, j⟩
    · rintro Z f ⟨⟨i, j⟩⟩
      change R.bind (fun _ f hf ↦ T f hf) (j.1.2 ≫ i.1.2)
      exact ⟨i.1.1, j.1.2, i.1.2, i.2, j.2, rfl⟩
  · intro I X U a ha Y b
    have := J.hasPullbacks_of_mem b ha
    have (i : I) : HasPullback (a i) b := Presieve.hasPullback b (Presieve.ofArrows.mk i)
    refine ⟨fun i ↦ pullback (a i) b, fun i ↦ pullback.snd (a i) b,
      fun i ↦ pullback.fst (a i) b, fun i ↦ (IsPullback.of_hasPullback (a i) b).flip, ?_⟩
    exact Precoverage.mem_coverings_of_isPullback a ha b _ _
      (fun i ↦ (IsPullback.of_hasPullback (a i) b).flip)

/-- The epimorphic families on finite-limit generators give a site presenting the ambient topos.

Source: Stacks Project, Sites, Tags 03A1 and 03CI
(blueprint: lem-weil-pbc-site-of-sheaf-generators).

Proof: Apply the subcategory comparison theorem with no prescribed coverings. Its
representatives have the same arrow supports as all epimorphic families, so a presieve
is covering exactly when its associated family is jointly epimorphic. Singleton
isomorphisms and composites satisfy joint cancellation. For base change, take the
chosen covering pullback family provided by the comparison theorem; each chosen
pullback maps to any other pullback by the universal property, so cancellation on
the latter family follows from cancellation on the chosen family. Existence of all
pullbacks follows from finite limits. The nerve isomorphism is the comparison theorem's
specified identification, without replacing the equivalence by an arbitrary one. -/
theorem siteOfSheafGenerators
    {C E : Type u} [SmallCategory C] [SmallCategory E] [HasFiniteLimits E]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (F : E ⥤ Sheaf J.toGrothendieck (Type u))
    [F.Full] [F.Faithful] [PreservesFiniteLimits F]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U))) :
    ∃ (K : Precoverage E) (_ : K.HasIsos) (_ : K.IsStableUnderComposition)
      (_ : K.IsStableUnderBaseChange) (_ : K.HasPullbacks)
      (e : Sheaf J.toGrothendieck (Type u) ≌ Sheaf K.toGrothendieck (Type u)),
      Nonempty (e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅
        sheafSubcategoryNerve F) ∧
      ∀ T (R : PreZeroHypercover.{u} T), R.presieve₀ ∈ K T ↔
        ⟨T, R⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F := by
  have hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g) := by
    intro A B T f g
    exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
      (IsPullback.of_hasPullback f g).map F⟩
  obtain ⟨_, Cov, K, hK, e, _, _, hsub, hCov, _, hsupp, hmem, hnerve, _⟩ :=
    sheafSubcategory_comparison.{u, u, 0} J (siteForCoverings_of_axioms J) F hrep hpb
      ∅ (by infer_instance) (by simp)
  have hepi : ∀ T (R : PreZeroHypercover.{u} T), R.presieve₀ ∈ K T ↔
      ⟨T, R⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F := by
    intro T R
    constructor
    · intro h
      obtain ⟨S, hS, heq⟩ := (hmem T R.presieve₀).1 h
      exact epi_of_support F heq (hsub hS)
    · intro h
      obtain ⟨S, hS, heq⟩ := hsupp T R h
      exact (hmem T _).2 ⟨S, hS, heq⟩
  obtain ⟨hiso, hcomp, hbase⟩ := siteAxioms_of_familyComparison F K Cov hCov hsub hmem hepi
  exact ⟨K, hiso, hcomp, hbase, inferInstance, e, hnerve, hepi⟩

end CategoryTheory
