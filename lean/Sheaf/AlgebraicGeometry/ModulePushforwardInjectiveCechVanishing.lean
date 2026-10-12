module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Positive Čech cohomology of a direct image of an injective module vanishes.

Source: Stacks Project, Cohomology of Sheaves, Tag 01EX (1), using Tag 01EP.
(blueprint: lem-weil-pbc-module-pushforward-injective-cech-vanishing).

Proof: Fix an open U, a covering (V_i), and a choice C of its iterated fibre products.
Pull back the opens along h. Inverse image preserves their union, so they cover h⁻¹U.
In the poset of opens, the universal property identifies C.W p t with the intersection
of the V_(t k); inverse image preserves these finite intersections. Choose the Čech
products on X to be these inverse images, with their induced projection and index maps.
The underlying additive groups of h_*I on C.W p t are exactly those of I on h⁻¹(C.W p t).
The change of scalar rings in module direct image does not change these additive groups.
Their restriction maps also agree. Taking products and alternating sums therefore
identifies the two additive Čech complexes degree by degree, including differentials.
Apply module_injective_open_cover_cech_acyclic to I and the pulled-back covering.
Transport its positive-degree IsZero statements across the resulting cohomology
isomorphisms. Uniqueness of products makes this work for every choice C. -/
theorem module_pushforward_injective_cech_vanishing {X S : Scheme.{u}} (h : X ⟶ S)
    (I : X.Modules) [Injective I] :
    ∀ (U : S.Opens) (J : Type (max u w)) (V : J → S.Opens)
      (hom : ∀ j, V j ⟶ U), (⨆ j, V j) = U →
      ∀ (C : SiteCechComplex V hom) (p : ℕ), 0 < p →
        IsZero ((C.cohomologyFunctor p).obj
          ((toPresheaf S).obj ((pushforward h).obj I))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
