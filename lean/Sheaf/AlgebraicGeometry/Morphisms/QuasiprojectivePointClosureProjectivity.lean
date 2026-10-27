/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.AlgebraicGeometry.Morphisms.GenericDvrPropernessCriterion
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen

/-!
# Projectivity of the reduced closure of a generic rational point

Source: Stacks Project, Tag 0208, `limits-lemma-Noetherian-dvr-valuative-proper`,
(1) equivalent to (4); de Jong, Claim 3.10 and sections 3.11--3.12, p.609;
Stacks Tags 01WC, 01W6, 01QS and 0BAJ
(blueprint: lem-sfb-quasiprojective-point-closure-projectivity).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- If the generic rational point extends over every DVR subring of the base function
field, its reduced closure in an open of an H-projective scheme is proper and H-projective,
embeds as a closed subscheme of the ambient projective scheme, and becomes an isomorphism
on the full inverse image of a dense base open. Every given DVR lift factors uniquely
through the closure.

Here `K = S.functionField`, with generic inclusion `S.fromSpecStalk (genericPoint S)`.
The closed immersion `i`, the integral (hence reduced) source `R`, and `hclosure` express
exactly the reduced induced closed structure on the closure of the image of `m`.
The square in `hgeneric` says that the generic fibre is `Spec K`, compatibly with `m`.
The equality `hf` specifies the structure map of `R`.

Source: Stacks Project, Tag 0208, `limits-lemma-Noetherian-dvr-valuative-proper`,
(1) equivalent to (4); de Jong, Claim 3.10 and sections 3.11--3.12, p.609;
Stacks Tags 01WC, 01W6, 01QS and 0BAJ
(blueprint: lem-sfb-quasiprojective-point-closure-projectivity).

Proof:
1. Factor `m` as `a` through `R` using the generic-fibre identification. Its image is
   generic in `R` by `hclosure`. On affine neighbourhoods `Spec B` and `Spec C` of the
   two generic points, the generic fibre says `(C \\ {0})⁻¹ B = K`, compatibly with
   `Frac C = K`. Integrality embeds `B` in `K` and gives `Frac B = K`. Thus `a` is the
   canonical generic-point map and `f` is birational (def-pc-integral-scheme and
   def-sc-function-field).
2. For each DVR lift `v`, apply lemma-nagata-valuation-factor-closed,
   `IsClosedImmersion.exists_lift_of_isFractionRing`, to `i`, `v` and `a`.
   A closed immersion is a monomorphism, so the factor is unique, lies over `b`, and
   restricts to `a` on the generic point.
3. Apply lem-sfb-generic-dvr-properness-criterion to `f`. The integral source,
   locally Noetherian base, separatedness and finite type are given. Steps 1 and 2
   supply precisely its canonical generic-point DVR extensions, so `f` is proper.
4. The immersion `i ≫ j` is proper over the separated scheme `H`, since `f` is proper
   and `q` is proper by lem-kun-projective-implies-proper. Use
   lem-weil-pbc-proper-over-separated and lem-weil-pbc-proper-immersion-closed
   to conclude that `i ≫ j` is a closed immersion.
5. Compose this closed immersion with a projective-space embedding of `H` supplied by
   def-kun-projective. By lem-weil-pbc-closed-immersion-comp this is a closed immersion,
   giving H-projectivity of `f`.
6. Both integral schemes have one irreducible component; step 1 identifies their
   generic points and local rings. Apply lem-sfb-birational-isomorphism-dense-open,
   using the given separatedness and local finite presentation, to obtain the dense
   base open on whose full inverse image `f` is an isomorphism.
-/
theorem quasiprojective_point_closure_projectivity
    {S H M R : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S] [CompactSpace S]
    (q : H ⟶ S) [IsHProjective q] [LocallyOfFiniteType q] [QuasiCompact q]
    (j : M ⟶ H) [IsOpenImmersion j]
    (m : Spec S.functionField ⟶ M)
    (hm : m ≫ j ≫ q = S.fromSpecStalk (genericPoint S))
    (i : R ⟶ M) [IsClosedImmersion i] [IsIntegral R]
    (hclosure : Set.range i = closure (Set.range m))
    (f : R ⟶ S) (hf : i ≫ j ≫ q = f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFinitePresentation f]
    (hgeneric : ∃ a : Spec S.functionField ⟶ R,
      a ≫ i = m ∧ IsPullback a (𝟙 (Spec S.functionField)) f
        (S.fromSpecStalk (genericPoint S)))
    (hext : ∀ (A : Subring S.functionField) [IsDiscreteValuationRing A]
      [IsFractionRing A S.functionField] (b : Spec (.of A) ⟶ S),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ b =
        S.fromSpecStalk (genericPoint S) →
      ∃ v : Spec (.of A) ⟶ M,
        v ≫ j ≫ q = b ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ v = m) :
    (∀ (A : Subring S.functionField) [IsDiscreteValuationRing A]
      [IsFractionRing A S.functionField] (b : Spec (.of A) ⟶ S),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ b =
        S.fromSpecStalk (genericPoint S) →
      ∀ v : Spec (.of A) ⟶ M,
        v ≫ j ≫ q = b → Spec.map (CommRingCat.ofHom A.subtype) ≫ v = m →
        ∃! w : Spec (.of A) ⟶ R, w ≫ i = v) ∧
    IsProper f ∧ IsClosedImmersion (i ≫ j) ∧ IsHProjective f ∧
      ∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (f ∣_ U) := by
  sorry

end AlgebraicGeometry
