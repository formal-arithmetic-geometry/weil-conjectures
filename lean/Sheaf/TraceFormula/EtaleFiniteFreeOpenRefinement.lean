import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.TraceFormula.StandardEtaleFiniteFreePrimeLifts

/-!
# Étale finite locally free open refinement

Source: Stacks Project, More on Morphisms, Tag 02LI, remark-topologies
(blueprint: lem-trf-etale-finite-free-open-refinement).
-/

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

/--
Every small jointly surjective étale family admits, Zariski locally on its base,
a refinement by open pieces of surjective finite locally free morphisms.

Source: Stacks Project, More on Morphisms, Tag 02LI, remark-topologies
(blueprint: lem-trf-etale-finite-free-open-refinement).

Proof plan (the six steps of the node): handle the empty base and reduce to a
point of the base; choose affine charts and a standard étale presentation at a
point of a member of the family; apply the prescribed-prime finite-free lift;
shrink the base using the closed image of the finite complement; localize the
finite free algebra and restrict the factorization maps; finally assemble the
pointwise choices into small indexing families. The cited affine, étale,
finite-free, finite-closed-map, localization, and size-convention nodes supply
the individual steps.
-/
theorem etale_finite_free_open_refinement
    {S : Scheme.{u}} {I : Type u} (E : I → Scheme.{u})
    (e : ∀ i, E i ⟶ S) [he : ∀ i, Etale (e i)]
    (hjoint : ∀ s : S, ∃ i x, e i x = s) :
    ∃ (J : Type u) (U : J → Scheme.{u}) (u : ∀ j, U j ⟶ S)
      (W : J → Scheme.{u}) (q : ∀ j, W j ⟶ U j)
      (K : ∀ j, Type u) (V : ∀ j, K j → Scheme.{u})
      (ι : ∀ j k, V j k ⟶ W j) (a : ∀ j k, I)
      (h : ∀ j k, V j k ⟶ E (a j k)),
      (∀ j, IsOpenImmersion (u j)) ∧
      (∀ s : S, ∃ j x, u j x = s) ∧
      (∀ j, Scheme.Hom.IsFiniteLocallyFree (q j)) ∧
      (∀ j, Surjective (q j)) ∧
      (∀ j k, IsOpenImmersion (ι j k)) ∧
      (∀ j t, ∃ k x, ι j k x = t) ∧
      (∀ j k, h j k ≫ e (a j k) = ι j k ≫ q j ≫ u j) := by
  sorry

end AlgebraicGeometry
