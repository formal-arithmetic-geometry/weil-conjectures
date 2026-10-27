/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Properties

/-! # Generic spreading of fibre-assassin noncontainment

Source: Stacks Project, More on Morphisms, Tag 05KN, `lemma-bad-case`
(blueprint: lem-sfb-generic-fibre-assassin-noncontainment-spreads).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Failure of containment of the associated points of the generic fibre in an open
persists over a nonempty open of an irreducible base. No Noetherian hypothesis on the
base or quasi-compactness hypothesis on the open is required.

Source: Stacks Project, More on Morphisms, Tag 05KN, `lemma-bad-case`
(blueprint: lem-sfb-generic-fibre-assassin-noncontainment-spreads).

Proof, following the corrected DAG argument using Tags 05F1 and 05F5:
1. Choose an associated point of the generic fibre outside the inverse image of U.
   Its image xi in X lies in the relative assassin [def-trf-relative-assassin] and
   outside U. Choose an affine neighbourhood Y0 = Spec A of the generic point, and
   a finite-type affine chart X0 = Spec B above it containing xi, using
   [def-weil-finite-type-morphism]. Open restriction leaves the fibre stalk rings and
   module stalks unchanged, hence preserves association. It suffices to work on X0/Y0.
2. Give Z = closure {xi} in X0 its reduced induced closed structure by
   [lem-weil-pbc-reduced-induced-closed-subscheme]. It lies in the closed complement
   of U. Apply [lem-sfb-relative-assassin-neighbourhood] to obtain a nonempty open W
   of Z whose fibre-component generic points map to associated points of the fibre
   module. Every nonempty open of Z contains xi. Choose a principal affine open P
   containing xi inside W.
3. Write Z = Spec (B/I) and P = Spec ((B/I)_g). The latter algebra is finite type
   over A: adjoin the images of generators of B and the inverse of g. Thus P -> Y0
   is finite type [def-weil-finite-type-morphism], and its generic fibre is nonempty.
   Apply [lem-sbc-generic-closed-subset-fibre-nonempty] with the entire closed subset
   of P. It supplies an open V containing the generic point with P_y nonempty for
   every y in V. This V is also open in Y.
4. For y in V choose a point of P_y, hence of W_y, and an irreducible component
   containing it by [lem-sc-irreducible-components-cover]. Scheme sobriety
   [lem-sc-scheme-sober] supplies its generic point. Step 2 makes its image associated
   to the fibre module. Its image lies in Z, hence outside U_y. The stalk observation
   of Step 1 transfers this witness to X_y. Thus containment fails for every y in V,
   and V is nonempty since it contains the generic point.

The local Stacks proof has an invalid support inference; the node records this repaired
proof without changing the statement. -/
theorem genericFibreAssassinNoncontainment_spreads {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    (hF : F.IsQuasiCoherentFiniteType) (U : X.Opens) [IrreducibleSpace Y]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hU : ¬ associatedPoints ((tensorPullback (f.fiberι η)).obj F) ⊆
      (f.fiberι η) ⁻¹' (U : Set X)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ (y : Y), y ∈ V →
        ¬ associatedPoints ((tensorPullback (f.fiberι y)).obj F) ⊆
          (f.fiberι y) ⁻¹' (U : Set X) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
