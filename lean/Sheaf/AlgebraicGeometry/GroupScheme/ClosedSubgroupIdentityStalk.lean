/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Algebra.Basic

/-!
# Detecting a closed subgroup by the stalk at the identity

Source: Milne, Algebraic Groups (2017), 1.8, printed p.9, translation argument;
the scheme-theoretic identity-stalk consequence is agent-formulated in the DAG.
(blueprint: lem-sfb-closed-subgroup-identity-stalk-detection)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed subgroup of a connected affine group scheme of finite type over an algebraically
closed field is the whole group if its inclusion induces an isomorphism on the identity stalk.
No reducedness, smoothness or characteristic assumption is made.

Source: the scheme-theoretic consequence of Milne, Algebraic Groups (2017), 1.8, printed p.9,
assembled in the DAG (blueprint: lem-sfb-closed-subgroup-identity-stalk-detection).

Proof plan:
1. Write `G = Spec A`. By `lem-weil-pbc-lft-affine-pairs`, `A` is finitely generated over `k`;
   `lem-wf-affine-noetherian-components` makes it Noetherian. The affine description of
   `def-weil-closed-immersion` gives `K = Spec (A/I)`. Choose finitely many generators of `I`
   using `def-weil-pbc-noetherian-ring`, allowing an empty list.
2. Each generator has zero image in the stalk of `K` at its identity. Compatibility of the
   stalk map with germs (`def-weil-locally-ringed-space-morphism`) and its injectivity make
   its germ in `G` zero. The denominator criterion of
   `lem-weil-pbc-affine-open-stalk-localization` gives an element outside the identity prime
   annihilating each generator. Their product `s` is outside that prime and annihilates `I`.
3. By `lem-weil-pbc-affine-open-section-vanishing-prime`, `U = D(s)` contains the identity.
   `lem-weil-pbc-localization-quotient-commute` identifies the quotient localization with
   `A_s`, since `I A_s = 0`. Thus the restriction of the inclusion over `U` is an isomorphism
   (`def-weil-affine-spectrum`), with inverse `t : U → K` over `G`.
4. For `h ∈ K(k)`, put `g = j(h)`. The translations of `def-sc-group-scheme-translate` and
   `lem-sc-translation-automorphism` satisfy `j L_h = L_g j`. Transport `t` to `gU` to obtain
   an inverse for the restriction of `j` there; cancellation uses
   `def-sc-group-scheme-subgroup`. Let `V` be the union of all these translated opens.
5. If the closed subset `|K| \\ V` were nonempty, `lem-sc-lft-over-field-jacobson-space`
   would give a point closed in `G` in it. By `lem-weil-pbc-closed-point-residue-field-base`
   this point is rational. Its evaluation kills `I`, so it comes from `h ∈ K(k)` and belongs
   to `j(h)U`, a contradiction. Hence `V = |K|` is clopen and contains the identity.
   Connectedness (`def-weil-connected-scheme`) gives `V = |G|`.
6. Every section represented by an element of `I` restricts to zero on every translated open,
   because `j` is an isomorphism there. Sheaf uniqueness
   (`def-weil-locally-ringed-space-morphism`) gives `I = 0`, so `j` is an isomorphism of
   schemes by `def-weil-affine-spectrum`. Its inverse is over `k` and preserves all group
   operations by composing with `j` and cancelling, as in `def-sc-group-scheme`. -/
theorem isIso_of_isIso_stalkMap_onePoint
    {k : Type u} [Field k] [IsAlgClosed k]
    (G K : Over (Spec (.of k))) [GrpObj G] [GrpObj K]
    [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (j : K ⟶ G) [IsClosedSubgroupScheme j]
    (hj : IsIso (j.left.stalkMap (GrpObj.onePoint K))) : IsIso j := by
  sorry

end AlgebraicGeometry
