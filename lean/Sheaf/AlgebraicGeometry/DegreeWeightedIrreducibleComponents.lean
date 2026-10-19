/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Length
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import Sheaf.Topology.ClosedImmersionPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Degree as a multiplicity-weighted sum over reduced irreducible components

Source: Stacks Project, Varieties, Tag 0AYW, `lemma-degree-in-terms-of-components`,
rank-one case, and the preceding multiplicity definition
(blueprint: lem-trf-degree-weighted-irreducible-components).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree of an invertible module on a proper scheme of dimension at most one is the
sum of its degrees on the reduced one-dimensional irreducible components, weighted by
lengths of the ambient generic local rings. The component set is finite. Every complete,
irredundant finite list of reduced closed component schemes satisfies the formula; its
members are integral proper curves and their multiplicities are finite positive integers.
The degree is zero for an empty component list, also for an empty or zero-dimensional scheme.

Source: Stacks Project, Varieties, Tag 0AYW, rank-one case and preceding multiplicity paragraph.
(blueprint: lem-trf-degree-weighted-irreducible-components)

Proof:
1. A field is Noetherian, so Spec k is Noetherian. Properness and
   lem-weil-pbc-finite-type-over-noetherian make X Noetherian. The structure module and N
   are quasi-coherent of finite type, hence coherent by pqf-lem-coherent-ft-locnoeth.
   The same holds on proper closed subschemes. Tensoring with N preserves coherence locally.
   Apply lem-pc-euler-characteristic-well-defined to justify all Euler sums.
2. Use lem-weil-pbc-noetherian-finitely-many-components for finiteness and
   lem-weil-pbc-reduced-induced-closed-subscheme for the reduced structures. These are
   integral, proper by lem-weil-pbc-closed-immersion-proper, and of dimension one.
   The generic points exist uniquely by lem-weil-pbc-scheme-sober. On affine opens the
   defining radical ideals are prime since the components are irreducible.
3. Apply lem-weil-pbc-coherent-filtration-integral-subschemes to O_X: its finite coherent
   filtration has quotients j_* I for nonzero coherent ideals I on integral closed Z.
   All such Z are proper, hence Noetherian, by step 1.
4. Every Z has dimension zero or one. A one-dimensional Z is a component: choose an
   ambient component by lem-sc-irreducible-components-cover. A proper inclusion would
   extend a strict irreducible closed chain to length two. Reduced-structure uniqueness
   identifies Z with the chosen reduced component. A zero-dimensional integral Z is
   one point by sobriety, since every point closure must be all of Z.
5. Take stalks of the filtration using lem-weil-pbc-module-stalk-exact. By
   lem-weil-pbc-closed-pushforward-stalks a factor vanishes at a component generic point
   unless its support is that component. Otherwise lem-weil-pbc-integral-scheme-ideal-generic-stalk
   identifies it with the component function field. The ambient stalk maps onto that field
   because the immersion is closed, so this factor has length one. Repeated
   lem-weil-pbc-length-additive-short-exact counts such factors as the ambient local-ring
   length. That number is finite and positive, since the local ring has a nonzero residue field.
6. Put D(G) = chi(N tensor G) - chi(G). Tensor the filtration by N, using
   lem-sc-ext-tensor-exact, and subtract the two additivity formulas of lem-pc-euler-additive.
   Thus degree(N) is the sum of D over the filtration factors, by def-pc-degree-line-bundle.
7. Locally trivializing N identifies N tensor j_* I with j_*(j^* N tensor I).
   The local identifications agree under changes of generator and glue, without requiring
   flatness of j. Here j^* is the tensor pullback of def-pc-module-pullback.
8. Use lem-sc-zariski-module-abelian-cohomology-agree and
   lem-sc-cohomology-closed-immersion-pushforward to compare cohomology on Z and X.
   Naturality for multiplication by elements of k makes this comparison k-linear.
   Hence D(j_* I) = chi(j^* N tensor I) - chi(I), computed on Z.
9. On a one-dimensional Z, the pullback is invertible by
   lem-weil-pbc-invertible-pullback-tensor, and I has generic rank one by
   lem-weil-pbc-integral-scheme-ideal-generic-stalk. Apply
   lem-trf-curve-euler-tensor-generic-rank with rank one to obtain degree(j^* N).
10. On a zero-dimensional Z, an invertible module is trivial because Z is one point.
    Thus the two Euler characteristics agree and this factor contributes zero.
11. Regroup the finite sum by supports. Each component occurs as many times as its
    generic local-ring length by step 5, proving the formula. If the list is empty all
    factors contribute zero. For empty X use the length-zero filtration of the zero module. -/
theorem degree_weighted_irreducible_components (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X ≤ 1) (N : X.Modules) [N.IsInvertible] :
    Set.Finite {c : Set X | c ∈ irreducibleComponents X ∧ topologicalKrullDim c = 1} ∧
      ∀ (t : ℕ) (C : Fin t → Scheme.{u}) (j : (i : Fin t) → C i ⟶ X)
        (_hclosed : ∀ i, IsClosedImmersion (j i)) (_hreduced : ∀ i, IsReduced (C i))
        (_hcomponent : ∀ i, Set.range (j i) ∈ irreducibleComponents X ∧
          topologicalKrullDim (Set.range (j i)) = 1)
        (_hcomplete : ∀ c : Set X, c ∈ irreducibleComponents X →
          topologicalKrullDim c = 1 → ∃ i, Set.range (j i) = c)
        (_hdistinct : Function.Injective (fun i ↦ Set.range (j i)))
        (ξ : Fin t → X) (_hgeneric : ∀ i, closure ({ξ i} : Set X) = Set.range (j i)),
        (∀ i, IsIntegral (C i) ∧ IsProper (j i ≫ X ↘ Spec (.of k)) ∧
          topologicalKrullDim (C i) = 1 ∧
          ∃ m : ℕ, 0 < m ∧
            Module.length (X.presheaf.stalk (ξ i)) (X.presheaf.stalk (ξ i)) = m) ∧
        degree k N = ∑ i : Fin t,
          ((Module.length (X.presheaf.stalk (ξ i)) (X.presheaf.stalk (ξ i))).toNat : ℤ) *
            @degree k _ (C i) ⟨j i ≫ X ↘ Spec (.of k)⟩ ((tensorPullback (j i)).obj N) ∧
        (t = 0 → degree k N = 0) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
