/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AmpleIso
import Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection
import Sheaf.AlgebraicGeometry.FiniteSurjectiveAmpleReflection
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Ample line-bundle descent through a finite-branch quotient

Source: Stacks Project, Properties Tag 0F20, Modules Tag 01CY, Sheaves Tags
00AL, 00AM, 04TN, Coherent Tag 0B5V, and Morphisms Tags 01VT, 01W6.
The finite closed-image shrinking and two-open gluing are the agent extraction
recorded in the DAG (blueprint: lem-sfb-finite-branch-ample-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample invertible module descends through a finite surjective morphism that is
an isomorphism off a closed subscheme with finitely many points upstairs, provided
those points lie in one affine open. The descended module is trivial near the closed
subscheme, agrees with the original module on its complement, and is ample. The target
admits a closed immersion into a finite projective space over the affine base.

`D` is precisely the open complement of the range of `t`; thus `a ⁻¹ᵁ D` is the
complement of `Z = pullback a t`. The isomorphism is the restriction of `a` itself.
Neither this formulation nor the proof requires branch points to be closed.

Source: Stacks Project, Properties Tag 0F20; Modules Tag 01CY; Sheaves Tags
00AL, 00AM, 04TN; Coherent Tag 0B5V; Morphisms Tags 01VT, 01W6;
Constructions Tags 01NH, 01N2; and the agent extraction in the DAG
(blueprint: lem-sfb-finite-branch-ample-descent).

Proof:
1. Apply `lem-sfb-affine-invertible-finite-set-section` to `U` and `L|U`.
   The resulting section is nonzero at all points of `Z`. By
   `lem-weil-pbc-nonvanishing-section-trivializes` it trivializes `L` on an
   open `V` containing `Z` and contained in `U`.
2. By `lem-weil-pbc-finite-closed-map-finite-fibres`, `a(X minus V)` is closed.
   Its complement `W` contains `T`, and its inverse image is contained in `V`.
   Restrict the trivialization to `a ⁻¹ᵁ W`.
3. Transport `L` on the complement of `Z` across the given isomorphism to a
   module `N` on `D`. The opens `W,D` cover `Y`. The trivialization supplies
   the transition between the structure sheaf on `W` and `N` on `D`.
   The two-open cocycle consists of this map, its inverse, and identities.
   Apply `lem-weil-pbc-glue-sheaves-of-modules` to obtain `M` and both charts.
   The charts show that `M` is invertible, using `def-sc-invertible-module`.
4. Pull back these charts using `def-pc-module-pullback`,
   `lem-pc-module-pullback-identity-composition`, and
   `lem-weil-pbc-open-immersion-module-pullback-restriction`. On the overlap
   both maps into `L` are multiplication by the same section. Glue the maps
   and their inverses by `lem-weil-pbc-glue-sheaves-of-modules`. They give
   `a^*M` isomorphic to `L`, with the asserted identification on `D`.
5. Apply `lem-sc-ample-iso` and
   `lem-trf-finite-surjective-ample-reflection` to deduce that `M` is ample.
6. Properness gives finite type over the affine base. Apply
   `lem-weil-pbc-ample-very-ample-immersion-affine-base` to obtain an immersion
   into a finite projective space over that base.
7. Use `lem-weil-pbc-projective-space-proj-separated`,
   `lemma-nagata-proper-to-separated-target`, and
   `lem-weil-pbc-proper-immersion-closed` to make the immersion closed.
   `lem-nagata-affine-proj-scalar-extension` identifies the affine Proj model
   with the base-change projective space of `def-kun-projective`.
   The empty case needs no change: surjectivity makes `T` empty when `Z` is
   empty, and gluing then transports the bundle across the global isomorphism.
-/
theorem exists_ample_descent_of_finite_branches
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of R))]
    [Y.Over (Spec (CommRingCat.of R))]
    [IsProper (X ↘ Spec (CommRingCat.of R))]
    [IsProper (Y ↘ Spec (CommRingCat.of R))]
    (a : X ⟶ Y) [a.IsOver (Spec (CommRingCat.of R))] [IsFinite a] [Surjective a]
    (T : Scheme.{u}) (t : T ⟶ Y) [IsClosedImmersion t]
    [Finite (CategoryTheory.Limits.pullback (C := Scheme.{u}) a t)]
    (D : Y.Opens) (hD : (D : Set Y) = (Set.range t)ᶜ) [IsIso (a ∣_ D)]
    (L : X.Modules) [L.IsInvertible] (hL : IsAmple X L)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hZU : Set.range (CategoryTheory.Limits.pullback.fst (C := Scheme.{u}) a t) ⊆
      (U : Set X)) :
    ∃ W : Y.Opens, Set.range t ⊆ (W : Set Y) ∧
      Nonempty (L.restrict (a ⁻¹ᵁ W).ι ≅ SheafOfModules.unit _) ∧
      ∃ (M : Y.Modules) (hM : M.IsInvertible),
        Nonempty (M.restrict W.ι ≅ SheafOfModules.unit _) ∧
        Nonempty ((tensorPullback a).obj M ≅ L) ∧
        Nonempty (M.restrict D.ι ≅
          (tensorPullback (inv (a ∣_ D))).obj (L.restrict (a ⁻¹ᵁ D).ι)) ∧
        @IsAmple Y M hM ∧
        (∃ (n : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of R))),
          IsClosedImmersion i ∧
          i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of R)) ↘
            Spec (CommRingCat.of R) = Y ↘ Spec (CommRingCat.of R)) ∧
        IsHProjective (Y ↘ Spec (CommRingCat.of R)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
