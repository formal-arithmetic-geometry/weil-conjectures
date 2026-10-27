module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.ProjectionMateExact

/-! # Unbounded descent under local cohomological bounds

Source: Stacks Project, Cohomology on Sites, Tag 0D7V,
`lemma-equivalence-unbounded-one`, and Tag 0D6R, `situation-olsson-laszlo`
(blueprint: lem-sfb-ringed-unbounded-descent-criterion).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wC wD wAb

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedSiteSectionFunctors

namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- Elaborating the two full-subcategory functor comparisons needs additional heartbeats.
/-- Exact pullback inducing a heart equivalence gives unbounded descent under the
local cohomological bounds of Stacks 0D6R.
Source: Stacks Project, Tag 0D7V, `lemma-equivalence-unbounded-one`
(blueprint: lem-sfb-ringed-unbounded-descent-criterion).

The pullback is specified by its adjunction to the induced module direct image;
left-adjoint uniqueness identifies any such presentation with module pullback.
The good covering presieves form the cofinal collection in 0D6R: every covering
presieve admits an actual refinement with the indicated bound on every domain.
Cohomology is computed by the total right derived section functor on a module in
degree zero; nonnegative degrees suffice, and the bound itself is an integer.

Proof:
1. Exact-functor derived factorization identifies Lf* with termwise f*, commutes
with cohomology and good truncation, and preserves the specified cohomology class
(lem-weil-pbc-exact-functor-derived-factorization,
lem-weil-pbc-exact-functor-derived-functor,
lem-weil-pbc-exact-functor-complex-cohomology, def-kun-truncations).
2. Write F in A as f*G for G in B. The degree-zero unit assumption gives
Rf*F = G[0], hence higher direct-image vanishing. Apply the bounded-below criterion
lem-sfb-ringed-bounded-below-descent-criterion to obtain unit and counit there.
3. Apply lem-sfb-ringed-local-bound-direct-image-truncation with N = 0 and both
local bound hypotheses. Rf* preserves the cohomology class and its comparison to
Rf* of a sufficiently low good truncation is invertible in the fixed degree.
4. In the naturality square for the unit and such a truncation, both vertical
cohomology arrows and the bounded-below bottom unit are invertible. Thus the
unbounded unit is invertible in every degree and is an isomorphism.
5. The counit square works likewise, using exactness of f* to commute it with
cohomology and the comparison from step 3. Its counit is therefore an isomorphism.
6. Weak Serre closure gives the inherited triangulated subcategories
(lem-sbc-cohomology-in-weak-serre-subcategory). K-injective resolutions exist
(prop-pur-kinjective-resolutions-exist), so Rf* is triangulated by
lem-pc-right-derived-functor-triangulated. Restrict the canonical derived
adjunction (lem-weil-pbc-ringed-projection-mate-exact); the invertible unit and
counit give the claimed mutually quasi-inverse triangulated equivalences. -/
theorem ringedUnboundedDescentCriterion
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (O : Sheaf J CommRingCat.{u}) (R : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    [HasDerivedCategory.{wC} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{wD} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wAb} AddCommGrpCat.{u}]
    (L : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ f.modules)
    (A : ObjectProperty (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
    (B : ObjectProperty (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)))
    [A.ContainsZero] [A.IsClosedUnderIsomorphisms]
    [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels] [A.IsClosedUnderExtensions]
    [B.ContainsZero] [B.IsClosedUnderIsomorphisms]
    [B.IsClosedUnderKernels] [B.IsClosedUnderCokernels] [B.IsClosedUnderExtensions]
    (heart : ∃ e : B.FullSubcategory ≌ A.FullSubcategory,
      Nonempty (e.functor ⋙ A.ι ≅ B.ι ⋙ L) ∧
      Nonempty (e.inverse ⋙ B.ι ≅ A.ι ⋙ f.modules))
    (unit₀ : ∀ G, B G → IsIso
      (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor _ 0).obj G)))
    (boundC : ∃ V : Set C,
      (∀ U : C, ∃ P : Presieve U, Sieve.generate P ∈ J U ∧
        ∀ (W : C) (a : W ⟶ U), P a → W ∈ V) ∧
      ∀ U ∈ V, ∃ d : ℤ, ∀ P : Presieve U, Sieve.generate P ∈ J U →
        ∃ Q : Presieve U, Sieve.generate Q ∈ J U ∧
          (∀ (W : C) (a : W ⟶ U), Q a →
            ∃ (W' : C) (b : W' ⟶ U) (c : W ⟶ W'), P b ∧ c ≫ b = a) ∧
          ∀ (W : C) (a : W ⟶ U), Q a → ∀ F, A F → ∀ p : ℕ, d < (p : ℤ) →
            IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat p).obj
              ((sectionEvaluation
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) W).rightDerivedFunctor.obj
                ((DerivedCategory.singleFunctor _ 0).obj F))))
    (boundD : ∃ V : Set D,
      (∀ U : D, ∃ P : Presieve U, Sieve.generate P ∈ K U ∧
        ∀ (W : D) (a : W ⟶ U), P a → W ∈ V) ∧
      ∀ U ∈ V, ∃ d : ℤ, ∀ P : Presieve U, Sieve.generate P ∈ K U →
        ∃ Q : Presieve U, Sieve.generate Q ∈ K U ∧
          (∀ (W : D) (a : W ⟶ U), Q a →
            ∃ (W' : D) (b : W' ⟶ U) (c : W ⟶ W'), P b ∧ c ≫ b = a) ∧
          ∀ (W : D) (a : W ⟶ U), Q a → ∀ F, B F → ∀ p : ℕ, d < (p : ℤ) →
            IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat p).obj
              ((sectionEvaluation
                ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) W).rightDerivedFunctor.obj
                ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    L.mapDerivedCategory.{wD, wC}.IsLeftDerivedFunctor L.mapDerivedCategoryFactors.{wD, wC}.hom
      (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
    (∀ G, DerivedCategory.homologyProperty.{wD} B G →
      IsIso (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app G)) ∧
    (∀ F, DerivedCategory.homologyProperty.{wC} A F →
      IsIso (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app F)) ∧
    ∃ e : (DerivedCategory.homologyProperty.{wD} B).FullSubcategory ≌
      (DerivedCategory.homologyProperty.{wC} A).FullSubcategory,
      Nonempty (e.functor ⋙ (DerivedCategory.homologyProperty.{wC} A).ι ≅
        (DerivedCategory.homologyProperty.{wD} B).ι ⋙ L.mapDerivedCategory.{wD, wC}) ∧
      Nonempty (e.inverse ⋙ (DerivedCategory.homologyProperty.{wD} B).ι ≅
        (DerivedCategory.homologyProperty.{wC} A).ι ⋙ f.modules.rightDerivedFunctor) ∧
      ∃ (_ : e.functor.CommShift ℤ) (_ : e.inverse.CommShift ℤ),
        e.functor.IsTriangulated ∧ e.inverse.IsTriangulated := by
  sorry

end CategoryTheory
