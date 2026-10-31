/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RingHom.Flat

import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.TraceFormula.EtaleLocalRingFlatness
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Module flatness over a local ring and its strict henselization

Source: Stacks Project, More on Flatness, Tag 05VL, equivalence (1) and (3),
applied at the closed point of Spec R
(blueprint: lem-sfb-strict-henselization-module-flatness).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module

/-- A module over a strict henselization is flat over the base exactly when it is
flat over the strict henselization. The base action is restriction along its structural map.

Source: Stacks Project, Tag 05VL, equivalence (1) and (3)
(blueprint: lem-sfb-strict-henselization-module-flatness).

Proof:
1. Identify the pointed-etale presentation with the triples presentation of
   lem-weil-pbc-strict-henselization-triples: a pointing determines its kernel and the
   embedding of its residue field into K, and conversely. Morphisms agree. Since R is local,
   its localization at its maximal ideal is R. The triples result gives filteredness and
   a residue map C to K whose kernel is the maximal ideal and whose composites are the pointings.
2. If M is C-flat, lem-sc-strict-henselization-faithfully-flat makes C flat over R, using
   def-weil-pbc-faithfully-flat-ring-map. Apply lem-pc-module-flat-transitive to obtain R-flatness.
3. If M is R-flat, localize each pointed-etale algebra S at the kernel q of its pointing.
   Elements outside q have nonzero residue in K, so their images in the local ring C are units.
   Thus S_q maps to C. By lem-trf-etale-local-ring-flatness, M is flat over S_q. The stalk
   identifications of lem-weil-pbc-affine-open-stalk-localization identify the base stalk
   with R and the source stalk with S_q; evaluating on r/1 checks the restricted action.
4. In any finite C-linear relation in M, lift all coefficients to a common pointed-etale
   stage using lem-weil-pbc-filtered-colimit-algebras-elementwise and filteredness. Its
   localization S_q acts on M through C, so the same relation holds there. For an empty
   relation, choose any stage using nonemptiness of the filtered category.
5. Apply lem-weil-pbc-flat-equational-criterion over S_q to write this relation as a trivial
   relation. Map its coefficient matrix through S_q to C; the module equations and vanishing
   coefficient sums are preserved. Every finite C-relation is therefore trivial. The reverse
   direction of the same criterion gives C-flatness, completing the equivalence. -/
theorem flat_iff_strictHenselization (R : Type u) (K C : Type (max u v))
    [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C]
    (_P : Algebra.StrictHenselizationPresentationIn.{u, v} R K C)
    (M : Type w) [AddCommGroup M] [Module C M] :
    @Module.Flat R M _ _ (Module.compHom M (algebraMap R C)) ↔ Module.Flat C M := by
  sorry

end Module
