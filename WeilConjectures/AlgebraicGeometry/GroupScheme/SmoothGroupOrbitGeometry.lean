/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GenericFlatness
import WeilConjectures.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import WeilConjectures.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.FiniteTypeLocalDimension
import WeilConjectures.DeligneLaumon.IrreducibleFibreDimensionLowerBound
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Geometry of smooth connected group orbits

Source: Milne, Algebraic Groups (2022 corrected text), Propositions 1.65, 7.4--7.6,
5.23 and 7.11--7.12 (blueprint: lem-sfb-smooth-group-orbit-geometry).

The stabilizer is characterized on all test schemes. The orbit, closure and boundary
are characterized by reduced immersions with their prescribed underlying images.
Invariance is expressed by factorization of the scheme action, including nilpotent
valued test points. The dimension formula is written additively as in Milne 5.23.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Smooth connected algebraic groups have smooth locally closed reduced orbits, faithfully
flat orbit maps, the stabilizer dimension formula, and invariant closures and boundaries
whose orbits have strictly smaller dimension.

Source: Milne, Algebraic Groups (2022), Propositions 1.65, 7.4--7.6, 5.23 and 7.11--7.12
(blueprint: lem-sfb-smooth-group-orbit-geometry).

Proof, following the seven steps of the node:
1. Finite type over a field is Noetherian (lem-weil-pbc-finite-type-over-noetherian).
   Finite-type cancellation into separated targets and finite presentation over Noetherian
   rings give the finiteness conditions for Chevalley and generic flatness. Smoothness gives
   regularity (lem-weil-pbc-smooth-scheme-over-field-regular); connectedness and the identity
   make G integral (lem-sc-regular-connected-integral). Locally closed nonempty subsets have
   closed rational points by lem-sc-lft-over-field-jacobson-space and
   lem-weil-pbc-closed-point-residue-field-base. Closed and open subschemes retain finite type
   by lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-qc-open-immersion-finite-type and
   lem-sfb-finite-type-composition-base-change.
2. Chevalley makes the orbit image constructible (lem-weil-pbc-chevalley-constructible-image).
   The affine constructible-open lemma gives an open in its irreducible closure.
   Translate this open by G(k). Closed rational point detection, applied also to the
   nonempty finite-type fibres of the orbit map, proves that these translates equal the
   whole orbit image. Hence that image is locally closed.
3. Give the closure its reduced structure and restrict to this open orbit, using
   lem-weil-pbc-reduced-induced-closed-subscheme. Reduced-source factorization gives the
   orbit map to O (lem-weil-pbc-reduced-source-factors-through-closed-subscheme).
   It is surjective. Generic flatness (lem-sbc-generic-flatness) gives a nonempty flat open;
   its translates cover O by closed rational point detection. Translation isomorphisms
   transport the flat stalk maps, giving flatness everywhere and faithful flatness.
4. The algebraically closed field is perfect. The reduced orbit is geometrically reduced
   by lem-kun-geometric-reduced-perfect. Its dense smooth open exists by
   lem-pur-geometrically-reduced-dense-smooth-open. Translations preserve the smooth locus
   and carry one closed smooth point to every closed point, so O is smooth everywhere.
5. Form the stabilizer fibre over x. The action laws make it a subgroup; separatedness
   makes its inclusion closed. The finite local dimension lemma and
   lem-ag-group-identity-local-dimension make dim G finite. The irreducible fibre dimension
   lower bound and dense-open dimension comparison make dim O finite. Apply
   lem-sbc-flat-composite-fibre-dimension-at-point at the identity to G -> O -> Spec k.
   Use lem-ag-rational-point-stalk-topological-local-dimension,
   lem-ag-group-identity-local-dimension and lem-sbc-equidimensional-open-local-dimension
   to identify these local dimensions with dim G, dim K and dim O. This gives the formula
   without reducing the stabilizer.
6. Translations preserve O, its closure Z and its boundary B. The products G times Z and
   G times B are reduced by sbc-lem-smooth-geometrically-reduced, lem-pc-smooth-flat and
   lem-sfb-flat-geometrically-reduced-pullback. They are finite type. Closed rational point
   detection puts the action image in the prescribed closed subset. Reduced-source
   factorization produces the displayed action factorizations through Z and B; the laws
   follow by cancelling their closed immersions.
7. The dense open O has the dimension of its irreducible closure Z by
   lem-weil-pbc-dense-open-dimension-comparison and subspace monotonicity. Every irreducible
   chain in the proper closed B extends strictly by Z, so dim B < dim O when B is nonempty.
   Invariance puts each boundary orbit in B; subspace monotonicity bounds its dimension by
   dim B. If B is empty there is no boundary rational point to check. -/
theorem exists_smooth_group_orbit_geometry
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (X : Over (Spec (.of k))) [ModObj G X]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    ∃ (K : Grp (Over (Spec (.of k)))) (i : K.X ⟶ G),
      IsClosedSubgroupScheme i ∧
      (∀ (T : Over (Spec (.of k))) (g : T ⟶ G),
        (∃ h : T ⟶ K.X, h ≫ i = g) ↔ g • (toUnit T ≫ x) = toUnit T ≫ x) ∧
      ∃ (O : Over (Spec (.of k))) (j : O ⟶ X) (q : G ⟶ O),
        IsReduced O.left ∧ IsImmersion j.left ∧ Smooth O.hom ∧
        Set.range j.left = Set.range (lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X]).left ∧
        q ≫ j = lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X] ∧
        Flat q.left ∧ Surjective q.left ∧
        topologicalKrullDim G.left = topologicalKrullDim K.X.left +
          topologicalKrullDim O.left ∧
        ∃ (Z B : Over (Spec (.of k))) (z : Z ⟶ X) (b : B ⟶ X),
          IsReduced Z.left ∧ IsClosedImmersion z.left ∧
          Set.range z.left = closure (Set.range j.left) ∧
          IsReduced B.left ∧ IsClosedImmersion b.left ∧
          Set.range b.left = closure (Set.range j.left) \ Set.range j.left ∧
          (∃ aZ : G ⊗ Z ⟶ Z, aZ ≫ z = (𝟙 G ⊗ₘ z) ≫ γ[G, X]) ∧
          (∃ aB : G ⊗ B ⟶ B, aB ≫ b = (𝟙 G ⊗ₘ b) ≫ γ[G, X]) ∧
          ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
            y.left (IsLocalRing.closedPoint k) ∈ Set.range b.left →
            topologicalKrullDim
              (Set.range (lift (𝟙 G) (toUnit G ≫ y) ≫ γ[G, X]).left) <
                topologicalKrullDim O.left := by
  sorry

end AlgebraicGeometry
