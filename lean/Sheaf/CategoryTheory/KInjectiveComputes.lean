/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# K-injective resolutions compute derived functors

Source: Weil conjectures blueprint, sec-abelian-varieties, sk-prop-av-pqf-finite,
lemma lem-sp-kinjective-computes (blueprint: lem-sp-kinjective-computes).
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private theorem lift_to_resolution
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {K L : CochainComplex C ℤ} (r : CochainComplex.KInjectiveResolutionChoice K)
    (s : CochainComplex.KInjectiveResolutionChoice L) (f : K ⟶ L) :
    ∃ u : r.complex ⟶ s.complex,
      Nonempty (Homotopy (r.map ≫ u) (f ≫ s.map)) ∧
      ∀ u', Nonempty (Homotopy (r.map ≫ u') (f ≫ s.map)) →
        Nonempty (Homotopy u' u) := by
  let := HasDerivedCategory.standard C
  let := r.quasiIso
  let := s.isKInjective
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have h := CochainComplex.IsKInjective.precomp_bijective_of_quasiIso r.map s.complex
  obtain ⟨a, ha⟩ := h.surjective (Q.map (f ≫ s.map))
  obtain ⟨u, hu⟩ := Q.map_surjective a
  subst a
  dsimp only [Q] at ha
  refine ⟨u, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩, ?_⟩
  · simpa only [Functor.map_comp] using ha
  · rintro u' ⟨h'⟩
    refine ⟨HomotopyCategory.homotopyOfEq _ _ (h.injective ?_)⟩
    simpa only [Functor.map_comp] using
      (HomotopyCategory.eq_of_homotopy _ _ h').trans ha.symm

private theorem compare_resolutions
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {K : CochainComplex C ℤ} (r s : CochainComplex.KInjectiveResolutionChoice K) :
    ∃ u : r.complex ⟶ s.complex, ∃ v : s.complex ⟶ r.complex,
      Nonempty (Homotopy (r.map ≫ u) s.map) ∧
      Nonempty (Homotopy (s.map ≫ v) r.map) ∧
      Nonempty (Homotopy (u ≫ v) (𝟙 r.complex)) ∧
      Nonempty (Homotopy (v ≫ u) (𝟙 s.complex)) ∧
      (∀ u', Nonempty (Homotopy (r.map ≫ u') s.map) → Nonempty (Homotopy u' u)) ∧
      (∀ v', Nonempty (Homotopy (s.map ≫ v') r.map) → Nonempty (Homotopy v' v)) := by
  obtain ⟨u, hu, huniq⟩ := lift_to_resolution r s (𝟙 K)
  obtain ⟨v, hv, vuniq⟩ := lift_to_resolution s r (𝟙 K)
  simp only [Category.id_comp] at hu hv huniq vuniq
  let := HasDerivedCategory.standard C
  let := r.quasiIso
  let := s.quasiIso
  let := r.isKInjective
  let := s.isKInjective
  have eu := HomotopyCategory.eq_of_homotopy _ _ hu.some
  have ev := HomotopyCategory.eq_of_homotopy _ _ hv.some
  simp only [Functor.map_comp] at eu ev
  refine ⟨u, v, hu, hv, ?_, ?_, huniq, vuniq⟩
  · refine ⟨HomotopyCategory.homotopyOfEq _ _
      ((CochainComplex.IsKInjective.precomp_bijective_of_quasiIso
        r.map r.complex).injective ?_)⟩
    simp only [Functor.map_comp, Functor.map_id, ← Category.assoc, eu, ev,
      Category.comp_id]
  · refine ⟨HomotopyCategory.homotopyOfEq _ _
      ((CochainComplex.IsKInjective.precomp_bijective_of_quasiIso
        s.map s.complex).injective ?_)⟩
    simp only [Functor.map_comp, Functor.map_id, ← Category.assoc, ev, eu,
      Category.comp_id]

private def mapped_comparison_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {I J : CochainComplex C ℤ}
    (u : I ⟶ J) (v : J ⟶ I)
    (hu : Homotopy (u ≫ v) (𝟙 I)) (hv : Homotopy (v ≫ u) (𝟙 J)) :
    (HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      (HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj J) where
  hom := (HomotopyCategory.quotient D (.up ℤ)).map
    ((F.mapHomologicalComplex (.up ℤ)).map u)
  inv := (HomotopyCategory.quotient D (.up ℤ)).map
    ((F.mapHomologicalComplex (.up ℤ)).map v)
  hom_inv_id := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy hu)
  inv_hom_id := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy hv)

/-- K-injective resolutions compute the derived functor, independently of the chosen resolution.
Source: blueprint lem-sp-kinjective-computes, clauses (1)--(3)
(blueprint: lem-sp-kinjective-computes).

Proof: The comparison principle (lem-sp-kinjective-comparison-principle) says that
precomposition by a quasi-isomorphism is bijective on homotopy classes of maps into a
K-injective complex: its cone is acyclic and Hom into every shift of the target vanishes.
Apply it to both resolution maps to obtain mutually inverse comparison maps under K.
Apply uniqueness again to their composites to obtain homotopies to the identities.
Additivity carries these homotopies to homotopies (def-sp-kinjective-bridge), hence gives a
canonical isomorphism after quotienting. Homotopic maps induce equal cohomology maps
(lem-weil-pbc-homotopic-maps-equal-cohomology). The same bijection lifts every morphism
between resolved complexes uniquely up to homotopy. Uniqueness gives identity, composition,
and compatibility with changing resolutions, so these maps form a functor.

A bounded-below complex of injectives is K-injective
(lem-weil-pbc-dplus-injective-representative): starting below its bound, construct a
null-homotopy of a map from an acyclic complex inductively. At each degree the remaining
map kills boundaries, hence factors through the next image; injectivity extends it to the
next term. Grothendieck categories have enough injectives
(lem-sp-grothendieck-enough-injectives), so an injective resolution of X is such a complex
and its augmentation is a quasi-isomorphism (def-sp-injective-resolutions). Comparing it
with any chosen K-injective resolution identifies the homology with the ordinary right
derived functors (def-sp-left-exact-additive). More explicitly, apply the homology
functor on the homotopy category to the comparison isomorphism. Its factorization through
complex homology identifies the endpoints. `HomologicalComplex.mapExtendIso` commutes the
termwise functor with extension from natural to integer degrees, and `extendHomologyIso`
identifies homology in degree `p : ℕ`. Finish with `InjectiveResolution.isoRightDerivedObj`.

Finally shifts preserve K-injectivity and quasi-isomorphisms
(lem-weil-pbc-kinjective-shift). Thus the shifted resolution resolves the shifted complex.
Additivity makes the termwise functor commute with shifts; comparison with any other
resolution gives the displayed isomorphism in the homotopy category. -/
theorem kInjective_computes
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [IsGrothendieckAbelian.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    let M := F.mapHomologicalComplex (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient D (ComplexShape.up ℤ)
    (∀ (K : CochainComplex.Plus C)
      (r s : CochainComplex.KInjectiveResolutionChoice K.obj),
      ∃ (u : r.complex ⟶ s.complex) (v : s.complex ⟶ r.complex),
        Nonempty (Homotopy (r.map ≫ u) s.map) ∧
        Nonempty (Homotopy (s.map ≫ v) r.map) ∧
        Nonempty (Homotopy (u ≫ v) (𝟙 r.complex)) ∧
        Nonempty (Homotopy (v ≫ u) (𝟙 s.complex)) ∧
        (∀ (u' : r.complex ⟶ s.complex),
          Nonempty (Homotopy (r.map ≫ u') s.map) → Nonempty (Homotopy u' u)) ∧
        (∀ (v' : s.complex ⟶ r.complex),
          Nonempty (Homotopy (s.map ≫ v') r.map) → Nonempty (Homotopy v' v)) ∧
        ∃ (e : Q.obj (F.rightDerivedComplexWithResolution K r) ≅
          Q.obj (F.rightDerivedComplexWithResolution K s)),
          e.hom = Q.map (M.map u) ∧ e.inv = Q.map (M.map v)) ∧
    (∀ (r : (K : CochainComplex.Plus C) →
      CochainComplex.KInjectiveResolutionChoice K.obj),
      ∃ (RF : CochainComplex.Plus C ⥤ HomotopyCategory D (ComplexShape.up ℤ))
        (e : ∀ K : CochainComplex.Plus C,
          RF.obj K ≅ Q.obj (F.rightDerivedComplexWithResolution K (r K))),
        ∀ (K L : CochainComplex.Plus C) (f : K ⟶ L),
          ∃ (u : (r K).complex ⟶ (r L).complex),
            Nonempty (Homotopy ((r K).map ≫ u) (f.hom ≫ (r L).map)) ∧
            (∀ (u' : (r K).complex ⟶ (r L).complex),
              Nonempty (Homotopy ((r K).map ≫ u') (f.hom ≫ (r L).map)) →
                Nonempty (Homotopy u' u)) ∧
            RF.map f ≫ (e L).hom = (e K).hom ≫ Q.map (M.map u)) ∧
    (∀ (I : CochainComplex.Plus C),
      (∀ n : ℤ, Injective (I.obj.X n)) → I.obj.IsKInjective) ∧
    (∀ (X : C) (I : InjectiveResolution X),
      QuasiIso (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat) ∧
        CochainComplex.IsKInjective (I.cocomplex.extend ComplexShape.embeddingUpNat)) ∧
    (∀ (X : C),
      let K₀ : CochainComplex.Plus C :=
        ⟨((CochainComplex.single₀ C).obj X).extend ComplexShape.embeddingUpNat,
          ⟨0, inferInstance⟩⟩
      ∀ (r : CochainComplex.KInjectiveResolutionChoice K₀.obj) (p : ℕ),
        Nonempty (F.rightDerivedCohomologyWithResolution K₀ r (p : ℤ) ≅
          (F.rightDerived p).obj X)) ∧
    (∀ (K : CochainComplex.Plus C)
      (r : CochainComplex.KInjectiveResolutionChoice K.obj) (n : ℤ)
      (s : CochainComplex.KInjectiveResolutionChoice (K⟦n⟧).obj),
        Nonempty (Q.obj (F.rightDerivedComplexWithResolution (K⟦n⟧) s) ≅
          (Q.obj (F.rightDerivedComplexWithResolution K r))⟦n⟧)) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K r s
    obtain ⟨u, v, hu, hv, huv, hvu, uu, vv⟩ := compare_resolutions r s
    exact ⟨u, v, hu, hv, huv, hvu, uu, vv,
      mapped_comparison_iso F u v huv.some hvu.some, rfl, rfl⟩
  · intro r
    let u {K L : CochainComplex.Plus C} (f : K ⟶ L) :=
      (lift_to_resolution (r K) (r L) f.hom).choose
    have hu {K L : CochainComplex.Plus C} (f : K ⟶ L) :
        Nonempty (Homotopy ((r K).map ≫ u f) (f.hom ≫ (r L).map)) :=
      (lift_to_resolution (r K) (r L) f.hom).choose_spec.1
    have huniq {K L : CochainComplex.Plus C} (f : K ⟶ L)
        (a : (r K).complex ⟶ (r L).complex)
        (ha : Nonempty (Homotopy ((r K).map ≫ a) (f.hom ≫ (r L).map))) :
        Nonempty (Homotopy a (u f)) :=
      (lift_to_resolution (r K) (r L) f.hom).choose_spec.2 a ha
    let M := F.mapHomologicalComplex (.up ℤ)
    let Q := HomotopyCategory.quotient D (.up ℤ)
    let RF : CochainComplex.Plus C ⥤ HomotopyCategory D (.up ℤ) :=
      { obj := fun K ↦ Q.obj (M.obj (r K).complex)
        map := fun f ↦ Q.map (M.map (u f))
        map_id := fun K ↦ by
          have h := huniq (𝟙 K) (𝟙 (r K).complex)
            ⟨Homotopy.ofEq (by simp)⟩
          simpa only [Functor.map_id] using
            (HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h.some)).symm
        map_comp := fun {K L T} f g ↦ by
          have h : Nonempty (Homotopy (u f ≫ u g) (u (f ≫ g))) := by
            apply huniq
            refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
            have hf := HomotopyCategory.eq_of_homotopy _ _ (hu f).some
            have hg := HomotopyCategory.eq_of_homotopy _ _ (hu g).some
            simp only [Functor.map_comp] at hf hg ⊢
            change (HomotopyCategory.quotient C (.up ℤ)).map (r K).map ≫
              ((HomotopyCategory.quotient C (.up ℤ)).map (u f) ≫
                (HomotopyCategory.quotient C (.up ℤ)).map (u g)) =
              (HomotopyCategory.quotient C (.up ℤ)).map (f.hom ≫ g.hom) ≫
                (HomotopyCategory.quotient C (.up ℤ)).map (r T).map
            rw [← Category.assoc, hf, Category.assoc, hg,
              ← Category.assoc, ← Functor.map_comp]
          simpa only [Functor.map_comp] using
            (HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h.some)).symm }
    refine ⟨RF, fun _ ↦ Iso.refl _, ?_⟩
    intro K L f
    exact ⟨u f, hu f, huniq f, by simp [RF, Q, M]⟩
  · intro I hI
    obtain ⟨n, hn⟩ := I.property
    let := hn
    let := hI
    exact CochainComplex.isKInjective_of_injective I.obj n
  · intro X I
    exact ⟨inferInstance, inferInstance⟩
  · intro X r p
    let I := injectiveResolution X
    let ri : CochainComplex.KInjectiveResolutionChoice
        (((CochainComplex.single₀ C).obj X).extend ComplexShape.embeddingUpNat) :=
      { complex := I.cocomplex.extend ComplexShape.embeddingUpNat
        map := HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat
        quasiIso := inferInstance
        isKInjective := inferInstance }
    obtain ⟨u, v, _, _, huv, hvu, _, _⟩ := compare_resolutions r ri
    let e := mapped_comparison_iso F u v huv.some hvu.some
    let H := HomotopyCategory.homologyFunctor D (.up ℤ) (p : ℤ)
    let H' := HomologicalComplex.homologyFunctor D (.up ℤ) (p : ℤ)
    let M := F.mapHomologicalComplex (.up ℤ)
    let a := (HomotopyCategory.homologyFunctorFactors D (.up ℤ) (p : ℤ)).app
      (M.obj r.complex)
    let b := (HomotopyCategory.homologyFunctorFactors D (.up ℤ) (p : ℤ)).app
      (M.obj ri.complex)
    exact ⟨a.symm ≪≫ H.mapIso e ≪≫ b ≪≫
      H'.mapIso (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F) ≪≫
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat (j := p) rfl ≪≫
      (I.isoRightDerivedObj F p).symm⟩
  · intro K r n s
    let := r.quasiIso
    let := r.isKInjective
    let rn : CochainComplex.KInjectiveResolutionChoice (K⟦n⟧).obj :=
      { complex := r.complex⟦n⟧
        map := ((CochainComplex.Plus.ι C).commShiftIso n).hom.app K ≫ r.map⟦n⟧'
        quasiIso := inferInstance
        isKInjective := inferInstance }
    obtain ⟨u, v, _, _, huv, hvu, _, _⟩ := compare_resolutions s rn
    exact ⟨mapped_comparison_iso F u v huv.some hvu.some ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app r.complex) ≪≫
      ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso n).app
        ((F.mapHomologicalComplex (.up ℤ)).obj r.complex)⟩

end CategoryTheory.Functor
