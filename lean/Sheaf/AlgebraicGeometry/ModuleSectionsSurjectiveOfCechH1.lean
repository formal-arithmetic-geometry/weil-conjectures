import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Surjectivity of module sections from vanishing Čech H¹

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EU (lemma-ses-cech-h1).
(blueprint: lem-weil-pbc-module-ses-cech-h1-surjective).
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- Vanishing Čech H¹ on a cofinal system of open coverings makes sections of a
short exact sequence of `O_X`-modules surjective.
Source: Stacks Project, Cohomology, Tag 01EU.
(blueprint: lem-weil-pbc-module-ses-cech-h1-surjective).
Proof: local lifts are refined to a chosen covering; their differences form a
Čech cocycle in the kernel, which is a coboundary by the vanishing hypothesis.
Subtracting the coboundary makes the lifts compatible, and the sheaf axiom glues
them to a global lift. The empty open is included by the sheaf zero-section axiom.
-/
theorem module_sections_surjective_of_cech_h1_vanishing
    (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (U : Opens X)
    (Cov : ∀ (I : Type v) (V : I → Opens X), (∀ i, V i ≤ U) → Prop)
    (hcofinal : ∀ (I : Type v) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      (∀ x, x ∈ U → ∃ i, x ∈ V i) →
      ∃ (K : Type v) (W : K → Opens X) (hW : ∀ k, W k ≤ U),
        Cov K W hW ∧ ∀ k, ∃ (i : I), W k ≤ V i)
    (hcech : ∀ (I : Type v) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      (hCov : Cov I V hV) →
      ∀ (f : ∀ i, V i ⟶ U),
      ∀ (Scech : SiteCechComplex V f),
        IsZero ((Scech.cohomologyFunctor 1).obj
          ((S.X₁.val.presheaf)))) :
    Function.Surjective (S.g.val.app (op U)) := by
  sorry

end AlgebraicGeometry.Scheme
