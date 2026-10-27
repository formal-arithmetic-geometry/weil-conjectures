module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SiteCechComplex

/-!
# Čech vanishing along compatible covering nerves

Source: Stacks Project, Cohomology on Sites, Tag 0D6X,
`lemma-pullback-injective-pre-limp`, the Čech comparison in the proof
(blueprint: lem-trf-cover-nerve-cech-vanishing-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SiteCechComplex

/-- Čech vanishing transfers along compatible isomorphisms of covering nerves and
naturally isomorphic presheaf coefficients.

Source: Stacks Project, Cohomology on Sites, Tag 0D6X,
`lemma-pullback-injective-pre-limp`, the Čech comparison in the proof
(blueprint: lem-trf-cover-nerve-cech-vanishing-transport).

Proof:
1. In degree `n`, on the factor indexed by `t`, compose the component of `e` at
   `W.W n t` with restriction by `(c n t).inv`. Its inverse is restriction by
   `(c n t).hom` followed by the inverse component of `e`. Functoriality and the
   inverse identities make these inverse group homomorphisms on the products.
   In negative degrees both complexes are zero.
2. The assumed square for each omitted factor, after applying the contravariant
   functor `G`, and naturality of `e` show that these maps commute with every
   restriction term. Additivity then gives commutation with the alternating sums
   defining the differentials. The inverse degree maps also commute with them.
3. For `p > 0`, send an `F`-cocycle to a `G`-cocycle. Vanishing of the latter
   cohomology supplies a primitive in degree `p - 1`. Apply the inverse degree
   map to that primitive; commutation with the differential makes its boundary
   the original cocycle. Thus every `F`-cocycle is a boundary, and the kernel/image
   definition of `cohomologyFunctor` gives the required vanishing.
-/
theorem isZero_cohomology_of_coverNerve
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (_hJ : J.IsSiteForCoverings) (_hK : K.IsSiteForCoverings)
    (u : C ⥤ D) {T : Type u} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (_hcover : Presieve.ofArrows f hom ∈ J U)
    (_himage : Presieve.ofArrows (fun t ↦ u.obj (f t))
      (fun t ↦ u.map (hom t)) ∈ K (u.obj U))
    (W : SiteCechComplex f hom)
    (P : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t)))
    (c : ∀ (n : ℕ) (t : Fin (n + 1) → T), u.obj (W.W n t) ≅ P.W n t)
    (_hc : ∀ (n : ℕ) (t : Fin (n + 2) → T) (j : Fin (n + 2)),
      u.map (W.indexMap t j.succAbove) ≫ (c n (t ∘ j.succAbove)).hom =
        (c (n + 1) t).hom ≫ P.indexMap t j.succAbove)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (G : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (_e : F ≅ u.op ⋙ G) (p : ℕ) (_hp : 0 < p) :
    IsZero ((P.cohomologyFunctor p).obj G) →
      IsZero ((W.cohomologyFunctor p).obj F) := by
  sorry

end CategoryTheory.SiteCechComplex
