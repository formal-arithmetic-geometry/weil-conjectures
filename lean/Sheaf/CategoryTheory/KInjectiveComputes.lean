/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.CategoryTheory.KInjectiveBridge
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# K-injective resolutions compute derived functors

Source: Weil conjectures blueprint, sec-abelian-varieties, sk-prop-av-pqf-finite,
lemma lem-sp-kinjective-computes (blueprint: lem-sp-kinjective-computes).
-/

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

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
derived functors (def-sp-left-exact-additive).

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
  sorry

end CategoryTheory.Functor
