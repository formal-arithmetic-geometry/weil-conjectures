module

public import Sheaf.RingTheory.CanonicalNaiveCotangentFunctor
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The canonical filtered-colimit comparison for naive cotangent complexes

Source: Stacks Project, Algebra, Tag 07BQ (lemma-colimits-NL), with constant base
and a small filtered category
(blueprint: lem-sfb-filtered-colimit-naive-cotangent-comparison).

The canonical complexes and maps have their concrete polynomial and free-module
formulas in `Algebra.CanonicalNaiveCotangent`. An arbitrary degreewise colimit
cocone is allowed. Its comparison is the unique chain map induced by the
algebra colimit legs, and is asserted to be inverted in the derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CanonicalNaiveCotangent

/-- The canonical chain map from the degreewise colimit to the complex of the
colimit algebra, characterized by its composites with every colimit leg.
Source: Stacks, Tag 07BQ
(blueprint: lem-sfb-filtered-colimit-naive-cotangent-comparison). -/
def comparison {R : Type u} [CommRing R]
    {J : Type (max u v)} [SmallCategory J]
    (F : J ⥤ CommAlgCat.{max u v} R) (c : Cocone F)
    (k : Cocone (F ⋙ functor R))
    (hk : ∀ n : ℤ, IsColimit
      ((HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℤ) n).mapCocone k)) :
    k.pt ⟶ (functor R).obj c.pt :=
  (HomologicalComplex.isColimitOfEval _ k hk).desc ((functor R).mapCocone c)

/-- The canonical comparison is a quasi-isomorphism and its image under Q is
an isomorphism in D(Mod(R)). Source: Stacks, Tag 07BQ (lemma-colimits-NL),
constant-base specialization for a small filtered category
(blueprint: lem-sfb-filtered-colimit-naive-cotangent-comparison).

Proof for stage 3:
1. Use lem-weil-pbc-filtered-colimit-algebras-elementwise and
lem-pc-filtered-colimit-commrings-elementwise: elements have representatives,
and equality is witnessed at a common later object. Filteredness gives a
common target for finitely many objects and equalizes finitely many parallel
arrows. Thus finitely many relations hold simultaneously at one later stage.
2. The polynomial universal property (def-weil-pbc-mv-polynomial-ring) shows
R[S] is the colimit of R[S_j]. Assign the variable of an element s the value
assigned to any representative of s; eventual equality proves independence.
3. Every element of the augmentation kernel I lifts to a polynomial at a
stage. Its evaluation becomes zero later, so it lifts to a stage kernel.
Apply lem-sfb-filtered-colimit-conormal-modules to identify the colimit of
I_j/I_j² with I/I², by the prescribed renaming map on representatives.
4. The degree-zero free-module map is onto: lift the finitely many labels
and coefficients to one stage. For injectivity, partition a finite support
by equality of its image labels. Make each part's labels equal at one stage,
then kill each coefficient sum at a later stage. This gives eventual
vanishing. Apply lem-weil-pbc-filtered-colimit-modules-criterion.
5. The polynomial derivative product rule gives differential compatibility:
both sides vanish on R and send [t] to d[u(t)], including variable collisions.
Renaming respects identities and composition. Thus these two component
comparisons give exactly the chain map characterized by the colimit legs
(def-weil-pbc-category-colimit), namely `comparison`.
6. Both nonzero component comparisons are invertible; the other components
are zero objects. The inverse components commute with the differential by
multiplying the chain-map equation by their inverses. The chain map is an
isomorphism, hence induces isomorphisms on all homology objects and is a
quasi-isomorphism. The localization Q in def-weil-abstract-derived-category
inverts it. No injectivity, flatness or finite-presentation assumption is used. -/
theorem filteredColimit_comparison
    {R : Type u} [CommRing R]
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{max u v} R) (c : Cocone F) (hc : IsColimit c)
    (k : Cocone (F ⋙ functor R))
    (hk : ∀ n : ℤ, IsColimit
      ((HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℤ) n).mapCocone k))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] :
    QuasiIso (comparison F c k hk) ∧
      IsIso (DerivedCategory.Q.map (comparison F c k hk)) := by
  sorry

end Algebra.CanonicalNaiveCotangent
