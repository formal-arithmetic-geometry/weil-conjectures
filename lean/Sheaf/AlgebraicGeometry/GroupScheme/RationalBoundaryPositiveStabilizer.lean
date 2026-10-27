/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # A boundary point with positive-dimensional partial stabilizer

Source: Milne, Algebraic Groups (2017), Proposition 8.25, p.154; Milne, A Proof of the
Barsotti-Chevalley Theorem (2013), Proposition 4.1, pp.8--9, and Lemmas 4.3--4.4
(blueprint: lem-sfb-rational-boundary-positive-stabilizer).

The partial map `a` represents the rational extension of left multiplication. Its domain
is explicitly the maximal domain of its rational equivalence class. The map `t` identifies
its restriction on `G × G`, and `V` is its inverse image along `g ↦ (g,P)`. The kernel ideal
of the closed immersion `i` specifies the reduced closure of the partial stabilizer.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A nonproper smooth connected algebraic group has a rational boundary point whose partial
stabilizer has positive-dimensional reduced closure.

Source: Milne, Algebraic Groups (2017), Proposition 8.25, p.154; Milne (2013), Proposition 4.1,
pp.8--9 (blueprint: lem-sfb-rational-boundary-positive-stabilizer).

Proof plan:
1. Use `lem-sfb-normal-divisorial-completion` to compactify the integral underlying group
   with a pure divisorial boundary. Extend left multiplication rationally, using
   `lem-sfb-rational-action-domain-laws`, and apply `lem-sfb-rational-boundary-divisor-model`
   to obtain an invariant integral boundary divisor and a birational involution on it.
2. Choose a closed point of the involution's nonempty open domain using
   `lem-sc-lft-over-field-jacobson-space`; it is rational by
   `lem-weil-pbc-closed-point-residue-field-base`. The involution and rational action laws
   show that the identity acts at its second coordinate `P`, which lies in the boundary.
3. Pull back the maximal domain along `g ↦ (g,P)` to obtain `V`. The partial orbit map
   factors through the divisor. Its fibre at `P` contains the identity and is closed under
   multiplication on rational points, by `lem-sfb-rational-action-domain-laws`.
4. By `lem-sfb-closed-submonoid-group-subscheme`, the reduced closure of these rational
   points is a closed subgroup scheme. Its kernel ideal is the vanishing ideal of their
   topological closure, giving precisely the scheme structure asserted here.
5. `lem-sc-integral-locally-algebraic-opens-dimension` gives `dim V = dim G`. Apply
   `lem-zl-irreducible-fibre-dimension-lower-bound` to the partial orbit map into the boundary
   divisor, whose dimension is `dim G - 1`. The fibre has local dimension at least one at
   the identity. Its closed rational points are dense by the Jacobson and residue-field
   lemmas of step 2, so their closure has dimension at least one. Reduction preserves the
   underlying topological space. -/
theorem exists_rational_boundary_positive_stabilizer (k : Type u) [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [ConnectedSpace G.left]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hG : ¬ IsProper G.hom) :
    ∃ (X : Over (Spec (.of k))) (j : G ⟶ X),
      IsOpenImmersion j.left ∧ IsIntegral X.left ∧ IsProper X.hom ∧
      (∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.left.presheaf.stalk x)) ∧
      Dense (Set.range j.left) ∧
      ∃ (P : 𝟙_ (Over (Spec (.of k))) ⟶ X)
        (a : (G ⊗ X).left.PartialMap X.left)
        (t : (G ⊗ G).left ⟶ a.domain.toScheme) (V : G.left.Opens)
        (S : Over (Spec (.of k))) (_ : GrpObj S) (i : S ⟶ G),
        (Set.range P.left ⊆ (Set.range j.left)ᶜ) ∧
        a.domain = a.toRationalMap.domain ∧
        t ≫ a.domain.ι = (𝟙 G ⊗ₘ j).left ∧
        t ≫ a.hom = μ[G].left ≫ j.left ∧
        V = (lift (𝟙 G) (toUnit G ≫ P)).left ⁻¹ᵁ a.domain ∧
        (Set.range η[G].left ⊆ (V : Set G.left)) ∧
        IsClosedSubgroupScheme i ∧ IsReduced S.left ∧
        i.left.ker = Scheme.IdealSheafData.vanishingIdeal
          ⟨closure {x : G.left | ∃ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
              (q : (𝟙_ (Over (Spec (.of k)))).left ⟶ a.domain.toScheme),
              x ∈ Set.range g.left ∧ q ≫ a.domain.ι = (lift g P).left ∧
                q ≫ a.hom = P.left}, isClosed_closure⟩ ∧
        (1 : WithBot ℕ∞) ≤ topologicalKrullDim S.left := by
  sorry

end AlgebraicGeometry
