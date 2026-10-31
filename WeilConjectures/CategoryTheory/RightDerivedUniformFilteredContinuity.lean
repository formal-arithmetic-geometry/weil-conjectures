/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-!
# Uniform filtered continuity of a right derived functor

Source: Stacks Project, literature/stacks-project/derived.tex, Tag 015J
(second spectral sequence and finite filtrations; blueprint:
lem-per-right-derived-uniform-filtered-continuity).

## Main statements

* rightDerived_uniform_filtered_continuity states filtered continuity on complexes
  with a common lower cohomological bound and preservation of the standard lower
  truncation.
-/

@[expose] public section

set_option autoImplicit false

universe wC wD vC vD uC uD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
  [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vC} D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- The total right derived functor selected by the K-injective construction for a
Grothendieck abelian source. Source: Stacks Project, Tag 015J
(blueprint: lem-per-right-derived-uniform-filtered-continuity). -/
noncomputable def grothendieckRightDerived (F : C ⥤ D) [F.Additive] :
    DerivedCategory C ⥤ DerivedCategory D :=
  F.rightDerivedFunctorOfQuasiIsoResolutions (fun K => by
    obtain ⟨I, hI, i, _, hi⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, i, hI, hi⟩)

/-- The chain-level functor used for the filtered comparison: first take the
functorial K-injective replacement and then apply F degreewise. Source: Stacks Project,
Tag 015J (blueprint: lem-per-right-derived-uniform-filtered-continuity). -/
noncomputable def kInjectiveFilteredFunctor (F : C ⥤ D) [F.Additive] :
    CochainComplex C ℤ ⥤ CochainComplex D ℤ :=
  CochainComplex.kInjectiveResolutionFunctor.{vC} C ⋙
    F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- If every object-level right derived functor preserves filtered colimits, then the
K-injective total right derived functor preserves filtered colimits of complexes having
a common lower cohomology bound, and preserves that lower bound. Source: Stacks Project,
Derived Categories, Tag 015J (lemma-two-ss-complex-functor, second spectral sequence
and finite filtrations; blueprint: lem-per-right-derived-uniform-filtered-continuity).

Proof plan:
1. Exact filtered colimits are part of the Grothendieck hypotheses, so homology
   commutes with the termwise colimit and the lower bound is retained.
2. Replace every complex functorially by its smart lower truncation at r; exact
   colimits preserve the kernels and cokernels in this construction.
3. Apply the functorial K-injective replacement and use its natural resolution maps
   to identify the actual chain comparison with the original cocone.
4. Apply the truncation hypercohomology theorem, obtaining E₂^{p,q} = R^p F(H^q)
   for p >= 0 and q >= r, functorially in the diagram and its cocone.
5. Form the exact couple in the abelian category of J-diagrams in B. AB5 makes the
   filtered-colimit functor exact, so the colimit couple has the colimit filtration.
6. On page two the comparison is the composite of the assumed R^pF-colimit
   isomorphism and the homology-colimit isomorphism; induction gives every page map.
7. For fixed total degree only 0 <= p <= n-r occurs. A uniform finite page and
   finite-filtration induction give the colimit cohomology isomorphism and hence the
   displayed Q.map comparison is an isomorphism.
8. The same smart truncation and bounded-below derived vanishing show that RF sends
   every D^{>= s}(A) into D^{>= s}(B), with no bound on the nonzero R^pF.
9. The chain maps are defined from the original cocone. The colimit universal property
   gives naturality in diagram maps and cocones (the third clause). For a compatible
   termwise quasi-isomorphism of representative diagrams, the K-injective comparison
   makes every stage map and the target map quasi-isomorphisms, and exact
   filtered-colimit homology keeps the colimit of the stage maps a quasi-isomorphism
   (the fourth clause); with the naturality square this identifies the two derived
   comparisons, i.e. independence of compatible quasi-isomorphic representatives.
-/
theorem rightDerived_uniform_filtered_continuity
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (hF : ∀ p : ℕ,
      PreservesFilteredColimitsOfSize.{vC, vC} (F.rightDerived p)) :
    ∀ (J : Type vC) [Category.{vC} J] [IsFiltered J]
      (K : J ⥤ CochainComplex C ℤ) [HasColimit K]
      [HasColimit (K ⋙ F.kInjectiveFilteredFunctor)] (r : ℤ),
      (∀ j : J,
        (DerivedCategory.Q.obj (K.obj j)).IsGE r) →
      IsIso (DerivedCategory.Q.map
        (colimit.desc (K ⋙ F.kInjectiveFilteredFunctor)
          (F.kInjectiveFilteredFunctor.mapCocone (colimit.cocone K)))) ∧
        (F.grothendieckRightDerived.obj
            (DerivedCategory.Q.obj (colimit K))).IsGE r ∧
        (∀ {L : J ⥤ CochainComplex C ℤ} [HasColimit L]
          [HasColimit (L ⋙ F.kInjectiveFilteredFunctor)] (α : K ⟶ L),
          colimit.post K F.kInjectiveFilteredFunctor ≫
              F.kInjectiveFilteredFunctor.map (colim.map α) =
            colim.map (Functor.whiskerRight α F.kInjectiveFilteredFunctor) ≫
              colimit.post L F.kInjectiveFilteredFunctor) ∧
        (∀ {L : J ⥤ CochainComplex C ℤ} [HasColimit L]
          [HasColimit (L ⋙ F.kInjectiveFilteredFunctor)] (α : K ⟶ L),
          (∀ j : J, QuasiIso (α.app j)) →
          IsIso (DerivedCategory.Q.map
              (colim.map (Functor.whiskerRight α F.kInjectiveFilteredFunctor))) ∧
            IsIso (DerivedCategory.Q.map
              (F.kInjectiveFilteredFunctor.map (colim.map α)))) ∧
        (∀ (s : ℤ) (X : DerivedCategory C), X.IsGE s →
          (F.grothendieckRightDerived.obj X).IsGE s) := by
  sorry

end CategoryTheory.Functor
