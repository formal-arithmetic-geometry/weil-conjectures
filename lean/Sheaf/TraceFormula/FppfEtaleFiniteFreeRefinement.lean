module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.SecTraceFormula.FppfLocalQfRefinement
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint

@[expose] public section

universe v u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-!
# An fppf covering admits an étale-local finite locally free refinement

Source: Stacks Project, `more-morphisms.tex`, Tag 0DET, `lemma-dominate-fppf-etale-locally`;
blueprint: `lem-trf-fppf-etale-finite-free-refinement`.
-/

/-- An fppf covering is refined, after an étale covering of the target, by surjective finite
locally free morphisms mapping to members of the original covering.

The proof follows Stacks Tag 0DET. First reduce an fppf covering to a jointly surjective family
which is flat, locally of finite presentation and locally quasi-finite. At each point, the
étale-local finite-piece lemma gives an étale neighbourhood and a finite open piece. Flatness
and local finite presentation pass to the base change and open restriction, yielding a finite
locally free map; its open image is used to make it surjective. Repeating over all points gives
a small jointly surjective étale family, with the resulting maps factoring through the original
fppf family. Empty schemes and empty indexing families are included by the existential
formulation.
(blueprint: lem-trf-fppf-etale-finite-free-refinement) -/
theorem exists_etale_finiteLocallyFree_refinement
    (S : Scheme.{u}) {I : Type v} (S_i : I → Scheme.{u})
    (f : ∀ i : I, S_i i ⟶ S)
    (hf : Presieve.ofArrows S_i f ∈ Scheme.fppfPrecoverage S) :
    ∃ (A : Type v) (S' V : A → Scheme.{u})
      (e : ∀ a : A, S' a ⟶ S) (p : ∀ a : A, V a ⟶ S' a)
      (i : A → I) (r : ∀ a : A, V a ⟶ S_i (i a)),
      (∀ a : A, Etale (e a)) ∧
      (∀ a : A, Surjective (p a)) ∧
      (∀ a : A, (p a).IsFiniteLocallyFree) ∧
      (∀ s : S, ∃ a : A, ∃ x : S' a, e a x = s) ∧
      (∀ a : A, (r a) ≫ f (i a) = (p a) ≫ e a) := by
  sorry

end AlgebraicGeometry.Scheme
