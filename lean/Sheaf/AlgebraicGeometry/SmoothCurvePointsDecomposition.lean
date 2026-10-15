/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint

/-!
# Decomposition of smooth curves into connected curves and points

Source: `literature/stacks-project/etale-cohomology.tex`, Tag 0A5B
(label `lemma-constant-smooth-statements`) (blueprint: lem-sbc-smooth-curve-points-decomposition).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/--
For an algebraically closed field, a smooth separated finite-type scheme of dimension at most
one is a finite coproduct of smooth connected one-dimensional curves and copies of the base point.
Source: Stacks Project, Etale Cohomology, Tag 0A5B, opening reduction in the proof,
under Situation `situation-what-to-prove`; Properties, Tags 0569 and 033N; Varieties, Tag 06LH.
(blueprint: lem-sbc-smooth-curve-points-decomposition)

Proof:
1. The field is Noetherian, so `Spec k` is Noetherian. Finite type makes `C` Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`), hence it has finitely many irreducible
   components (`lem-weil-pbc-noetherian-finite-components`).
2. The irreducible components cover `C` (`lem-sc-irreducible-components-cover`). Join
   intersecting components in a finite graph. The union for each graph component is closed,
   and its complement is a finite union of closed components, so it is also open. Each union
   is connected: irreducible subsets are connected, and unions along intersecting graph
   paths remain connected. These disjoint unions are the nonempty connected components;
   there are none if `C` is empty (`def-weil-irreducible-components`).
3. Equip each clopen union with its open-subscheme structure. Its inclusion is an open
   immersion (`def-weil-open-immersion`) and a closed immersion (`def-weil-closed-immersion`):
   on stalks the map to its pushforward is an isomorphism inside and has zero target outside.
   Smoothness restricts to this open (`lem-weil-pbc-smooth-restrict-open-subschemes`). Smooth
   implies locally of finite presentation, hence locally of finite type
   (`def-sbc-smooth-morphisms`, `def-sbc-locally-finite-presentation`); the closed subset of
   the quasi-compact `C` is quasi-compact, giving finite type (`def-weil-finite-type-morphism`).
   Its diagonal is a base change of the closed diagonal of `C`, giving separatedness
   (`lem-pc-closed-imm-base-change`, `def-weil-proper-morphism`).
4. Smoothness gives regular stalks (`lem-sc-smooth-regular`). The component is locally
   Noetherian as an open of `C`, hence regular (`def-weil-regular-scheme`), and its
   nonempty connected space makes it integral (`lem-sc-regular-connected-integral`).
   Chains of irreducible closed subsets of this closed component are chains in `C`, so its
   dimension is at most one; nonemptiness makes it zero or one
   (`def-sc-curves`, `def-kun-topological-krull-dimension`).
5. Partition the finite indices by dimension. The dimension-one components give the `D i`
   (`def-sc-curves`); each integral finite-type dimension-zero component is `Spec k` over `k`
   (`lem-weil-pbc-zero-dim-integral-point`). Form their coproduct
   (`lem-weil-pbc-scheme-coproduct-family`). Component inclusions give a map to `C`;
   its inverses on the disjoint covering opens glue, and both composites are identities
   on that cover. This gives an isomorphism over `k`. Replace the zero-dimensional summands
   by `Spec k` and reorder the indices. The coprojections are the clopen component
   inclusions of step 3. For empty `C`, use the empty coproduct.
-/
theorem smooth_curve_points_decomposition
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    : ∃ (I J : Type u) (_ : Fintype I) (_ : Fintype J)
        (D : I → Scheme.{u}) (d : ∀ i, D i ⟶ Spec (.of k)),
        (∀ i, IsConnectedCurve (d i)) ∧
        (∀ i, Smooth (d i)) ∧
        ∃ (q : (∐ fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)) ⟶ Spec (.of k)),
          (∀ i, Sigma.ι (fun s : Sum I J ↦ match s with
            | Sum.inl i => D i
            | Sum.inr _ => Spec (.of k)) (Sum.inl i) ≫ q = d i) ∧
          (∀ j, Sigma.ι (fun s : Sum I J ↦ match s with
            | Sum.inl i => D i
            | Sum.inr _ => Spec (.of k)) (Sum.inr j) ≫ q = 𝟙 _) ∧
          ∃ (e : C ≅ ∐ fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)),
            e.hom ≫ q = f ∧
            (∀ s, IsOpenImmersion (Sigma.ι (fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)) s)) ∧
            (∀ s, IsClosedImmersion (Sigma.ι (fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)) s))
 := by
  sorry

end AlgebraicGeometry
