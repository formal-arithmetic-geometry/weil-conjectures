/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.ReducedNormalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Recognition of componentwise normalization

Source: Stacks Project, Morphisms, Tags 035Q (3), (4), and 0H7D
(blueprint: lem-sfb-integral-normal-generic-recognition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An integral normal source with the same component generic points and generic residue
fields as a locally Noetherian target is uniquely its componentwise normalization.
Source: Stacks Project, Morphisms, Tags 035Q (3), including its reductions footnote,
035Q (4), and 0H7D (blueprint: lem-sfb-integral-normal-generic-recognition).

Proof:
1. Every quasi-compact open of T is Noetherian and has finitely many components, by
   lem-weil-pbc-noetherian-finitely-many-components and pqf-def-locnoeth.
2. The generic points of an open are precisely the component generic points of the
   ambient scheme lying in it. The generic-point bijection therefore restricts over
   each affine open U of T, giving finitely many components in its inverse image.
   A finite cover by such inverse images shows that every quasi-compact open of Z
   has finitely many component generic points, hence finitely many components.
3. Domain stalks imply Z is reduced. By
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme, a factors through
   T_red (def-weil-pbc-scheme-reduction). Reduction preserves points and residue fields.
   By lem-weil-pbc-minimal-prime-reduced-localization-field, the generic stalks of
   the reductions are their residue fields; their maps are the assumed isomorphisms.
4. Apply lem-sfb-normalization-integral-birational-factor (035Q (3)) with the
   component finiteness of steps 1 and 2 and the reduced generic isomorphisms of step 3.
   It identifies T's normalization with Z's normalization over T.
5. By lem-sfb-normalization-normal-locally-finite (0H7D), Z's normalization map is
   an isomorphism. Compose with the preceding identification and invert to obtain
   an isomorphism Z to T's normalization over T.
6. Every component of Z dominates its corresponding component of T. The uniqueness
   in lem-sfb-component-dominant-normalization-lift (035Q (4)) gives uniqueness of
   this isomorphism. An empty target forces an empty source, giving the empty case.
No local Noetherianity of Z, finiteness of a, excellence, or reducedness of T is used. -/
theorem existsUnique_iso_reducedNormalization_of_integral_normal_generic
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] (a : Z ⟶ T) [IsIntegralHom a]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z))
    (hgeneric : Set.BijOn a
      {z : Z | ∃ C ∈ irreducibleComponents Z, IsGenericPoint z C}
      {t : T | ∃ C ∈ irreducibleComponents T, IsGenericPoint t C})
    (hresidue : ∀ z : Z, (∃ C ∈ irreducibleComponents Z, IsGenericPoint z C) →
      IsIso (a.residueFieldMap z)) :
    ∃! e : Z ≅ T.reducedNormalization, e.hom ≫ T.fromReducedNormalization = a := by
  sorry

end AlgebraicGeometry.Scheme
