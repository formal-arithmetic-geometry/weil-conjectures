module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Uniqueness of composition on unbounded derived categories

Source: Stacks Project, Tag 04VG, and the natural-transformation localization universal
property in `Mathlib.CategoryTheory.Localization.Predicate`.
(blueprint: lem-sfb-exact-derived-composition)
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- Exact additive functors induce a unique composition isomorphism compatible with their
factorizations through the localization functors on unbounded cochain complexes.
The last map is the image of the termwise identity identifying `C(G) C(F)` with `C(GF)`.

Source: Stacks Project, Tag 04VG, enhanced to natural transformations by
`Localization.fullyFaithfulWhiskeringLeft` and `Localization.liftNatIso`.
(blueprint: lem-sfb-exact-derived-composition)

Proof: First, the composite is additive and preserves finite limits and finite colimits,
so the exact-functor derived-factorization lemma applies to `F`, `G`, and `F ⋙ G`.
Second, whisker the factorization of `F` by `D(G)`, then compose with the factorization
of `G` and the termwise identity comparison. This gives a factorization of `D(F) ⋙ D(G)`
through `Q` with the same complex-level functor as `D(F ⋙ G)`.
Third, lift the identity isomorphism of that complex-level functor using the localization
universal property. Its component formula gives the displayed normalization.
Finally, any two normalized comparisons agree on all objects `Q(K)` by cancellation of
the factorization isomorphisms. `Localization.natTrans_ext` makes their hom transformations
equal; `Iso.ext` then makes the natural isomorphisms equal.
-/
theorem existsUnique_mapDerivedCategoryCompIso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    ∃! μ : @mapDerivedCategory C _ _ _ E _ _ _ (F ⋙ G) inferInstance
        (comp_preservesFiniteLimits F G) (comp_preservesFiniteColimits F G) ≅
          F.mapDerivedCategory ⋙ G.mapDerivedCategory,
      ∀ K : CochainComplex C ℤ,
        μ.hom.app (DerivedCategory.Q.obj K) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.up ℤ)).hom.app K) =
        (@mapDerivedCategoryFactors C _ _ _ E _ _ _ (F ⋙ G) inferInstance
          (comp_preservesFiniteLimits F G) (comp_preservesFiniteColimits F G)).hom.app K := by
  refine ⟨mapDerivedCategoryCompIso F G, mapDerivedCategoryCompIso_fac F G, ?_⟩
  intro μ hμ
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  intro K
  have h := (hμ K).trans (mapDerivedCategoryCompIso_fac F G K).symm
  simpa only [← Category.assoc, cancel_mono] using h

end CategoryTheory.Functor
