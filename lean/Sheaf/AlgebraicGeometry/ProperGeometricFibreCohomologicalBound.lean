/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-!
# Uniform dimension and torsion cohomology bounds for proper fibres

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-proper,
`sk-prop-ctf-finite-proper-localizing.proof.md`, Étale statements, uniform bound;
Stacks Project, Tags 0A3V, 00P3, 0F0V and 03QU
(blueprint: lem-sfb-finite-proper-geometric-cd-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper morphism to a quasi-compact scheme has one nonnegative bound on every
base-changed fibre dimension and twice that bound on torsion cohomology of its
fibres over separably closed fields. Empty fibres are included.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-proper,
`sk-prop-ctf-finite-proper-localizing.proof.md`, Étale statements, uniform bound;
Stacks Project, Tags 0A3V, 00P3, 0F0V and 03QU
(blueprint: lem-sfb-finite-proper-geometric-cd-bound).

Proof:
1. Properness implies finite type. Apply `lem-fin-finite-type-fibre-dimension-bound`
   to obtain a natural number e bounding all ordinary fibres over the quasi-compact
   base. If the base is empty, choose e = 0; empty fibres have dimension bottom.
2. For any field-valued point u : Spec L → Y, residue-field point naturality
   (`lem-weil-pbc-residue-field-point-naturality`) factors u through Spec κ(y),
   where y is its image. The fibre-product universal property identifies its fibre
   with the ordinary fibre at y extended to L. Finite type is preserved under
   arbitrary base change (`lem-sfb-finite-type-composition-base-change`), so the
   field-extension clause of `lem-kun-dimension-extension` keeps its dimension
   unchanged, including for empty fibres. Isomorphic schemes have identical
   chains of irreducible closed subsets and hence identical Krull dimensions.
3. For any S → Y and s in S, pullback pasting identifies the fibre of X ×_Y S → S
   at s with X ×_Y Spec κ(s). The maps in both directions have the same projections,
   hence are inverse by the pullback universal property. Apply step 2; no
   quasi-compactness condition on S is needed.
4. For a separably closed Ω and Spec Ω → Y, the fibre Z is finite type over Ω
   and has dimension at most e. By `lem-weil-pbc-torsion-sheaf-characterizations`,
   the colimit torsion hypothesis implies locally annihilated sections.
   `lem-sf-separably-closed-torsion-cd` gives torsion cohomological dimension zero
   for Ω. Apply `new-thm-sc-affine-torsion-cd-bound` with d = e and c = 0, then
   `new-thm-sc-finite-type-torsion-cd-affine-reduction` to obtain vanishing above
   2e. These bounds cover empty schemes and arbitrary torsion without a common
   annihilator or invertibility hypothesis. The cohomology here is derived global
   sections of F in degree zero, as in `def-weil-pbc-etale-cohomology`. -/
theorem exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [CompactSpace Y] :
    ∃ e : ℕ,
      (∀ (S : Scheme.{u}) (g : S ⟶ Y) (s : S),
        topologicalKrullDim ((pullback.snd f g).fiber s) ≤ (e : WithBot ℕ∞)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ybar : Spec (.of Ω) ⟶ Y)
        (F : Sheaf (pullback f ybar).smallEtaleTopology AddCommGrpCat.{u + 1}),
        Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ, 2 * e < q →
          IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback f ybar) (q : ℤ)).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (pullback f ybar).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  sorry

end AlgebraicGeometry
