/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.EssentialImage
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.SixFunctors.OpenTensorNormalizationData

/-! # Exact open/closed calculus on unbounded derived categories

Source: blueprint `det-prop-scalar-six-pullback`, proof (2), exact open/closed route;
Stacks 015F, 04VG, 010N, 05QB, 05RT and 05RU.
(blueprint: lem-sfb-exact-open-closed-unbounded-calculus).

The four functors below are Mathlib's termwise-localized `mapDerivedCategory`.
The four component equations specify the actual localized adjunction maps using
`mapDerivedCategoryFactors`, rather than merely asserting existence of some adjunction.
The triangle identities are part of each resulting `Adjunction` structure.
-/

@[expose] public section

set_option autoImplicit false

universe uX uU uZ vX vU vZ wX wU wZ

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exact open/closed localization data descend to the ordinary unbounded derived
categories with their actual adjunction maps and support calculus.
Source: blueprint `det-prop-scalar-six-pullback`, proof (2), exact open/closed route;
Stacks 015F, 04VG, 010N, 05QB, 05RT and 05RU.
(blueprint: lem-sfb-exact-open-closed-unbounded-calculus).

Proof: (1) Apply `lem-weil-pbc-exact-functor-derived-factorization` to all four exact
functors; their standard factorizations identify the derived value on a complex
with termwise application. (2) Localize the degreewise adjunctions as in
`def-weil-exact-derived-adjunction`. The localization universal property
`lem-weil-pbc-localization-universal-property` gives precisely the four component
formulas displayed below. (3) Precompose both triangle equations with the complex
localization functor. They become the original triangle equations in each degree;
localization extensionality proves the derived triangle identities.
(4) Localize the inverses of the open unit and closed counit, and the two mixed
zero functors; this proves the first four support conclusions.
(5) Descend the natural cohomology comparisons of
`lem-weil-pbc-exact-functor-complex-cohomology` through localization in every integer
degree. (6) For a derived morphism whose two restrictions are invertible, apply the
assumed short exact sequence to its cohomology objects. Naturality gives a diagram
of short exact rows. Its outside maps are invertible, so
`lem-weil-pbc-short-five-lemma` makes the middle map invertible. Apply
`lem-weil-pbc-unbounded-derived-iso-cohomology` in all degrees.
(7) If the open restriction of H is zero, the open restriction of the closed unit
is a map between zero objects. Its closed restriction is the inverse closed
counit by the left triangle identity. Joint reflection makes that unit invertible.
(8) On two objects X,Y in the essential image of the derived closed extension,
their closed units are invertible. The inverse on Hom sets sends a to
`eta_X ≫ D(I).map a ≫ inv eta_Y`. Naturality of eta proves one inverse equation;
the closed triangle identity and naturality of the counit prove the other.
No step imposes a bound, an injective resolution or a recollement hypothesis. -/
theorem exactOpenClosedUnboundedCalculus
    {AX : Type uX} {AU : Type uU} {AZ : Type uZ}
    [Category.{vX} AX] [Category.{vU} AU] [Category.{vZ} AZ]
    [Abelian AX] [Abelian AU] [Abelian AZ]
    [HasDerivedCategory.{wX} AX] [HasDerivedCategory.{wU} AU]
    [HasDerivedCategory.{wZ} AZ]
    (J : AU ⥤ AX) (P : AX ⥤ AU) (Q : AX ⥤ AZ) (I : AZ ⥤ AX)
    [J.Additive] [P.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (a : J ⊣ P) (b : Q ⊣ I)
    (hopen : IsIso a.unit) (hclosed : IsIso b.counit)
    (hPI : ∀ M : AZ, IsZero (P.obj (I.obj M)))
    (hQJ : ∀ M : AU, IsZero (Q.obj (J.obj M)))
    (hseq : ∀ M : AX, ∃ h : a.counit.app M ≫ b.unit.app M = 0,
      (ShortComplex.mk (a.counit.app M) (b.unit.app M) h).ShortExact) :
    ∃ (da : J.mapDerivedCategory ⊣ P.mapDerivedCategory)
      (db : Q.mapDerivedCategory ⊣ I.mapDerivedCategory),
      (∀ K : CochainComplex AU ℤ,
        da.unit.app (DerivedCategory.Q.obj K) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
            P.mapDerivedCategoryFactors.inv.app ((J.mapHomologicalComplex (.up ℤ)).obj K) ≫
            P.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app K)) ∧
      (∀ K : CochainComplex AX ℤ,
        da.counit.app (DerivedCategory.Q.obj K) =
          J.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
            J.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K)) ∧
      (∀ K : CochainComplex AX ℤ,
        db.unit.app (DerivedCategory.Q.obj K) =
          DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
            I.mapDerivedCategoryFactors.inv.app ((Q.mapHomologicalComplex (.up ℤ)).obj K) ≫
            I.mapDerivedCategory.map (Q.mapDerivedCategoryFactors.inv.app K)) ∧
      (∀ K : CochainComplex AZ ℤ,
        db.counit.app (DerivedCategory.Q.obj K) =
          Q.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app K) ≫
            Q.mapDerivedCategoryFactors.hom.app ((I.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).counit.app K)) ∧
      IsIso da.unit ∧ IsIso db.counit ∧
      (∀ H : DerivedCategory AZ,
        IsZero (P.mapDerivedCategory.obj (I.mapDerivedCategory.obj H))) ∧
      (∀ H : DerivedCategory AU,
        IsZero (Q.mapDerivedCategory.obj (J.mapDerivedCategory.obj H))) ∧
      (∀ (K L : DerivedCategory AX) (f : K ⟶ L),
        IsIso (P.mapDerivedCategory.map f) → IsIso (Q.mapDerivedCategory.map f) → IsIso f) ∧
      (∀ H : DerivedCategory AX,
        IsZero (P.mapDerivedCategory.obj H) → IsIso (db.unit.app H)) ∧
      (∀ K L : DerivedCategory AX,
        I.mapDerivedCategory.essImage K → I.mapDerivedCategory.essImage L →
          Function.Bijective (fun f : K ⟶ L ↦ Q.mapDerivedCategory.map f)) := by
  sorry

end CategoryTheory
