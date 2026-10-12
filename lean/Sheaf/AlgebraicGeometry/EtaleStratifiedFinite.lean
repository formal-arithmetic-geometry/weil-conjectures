/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite
import Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluing
import Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import WeilConjectures.ConstructibleSheaf.Refinement

/-!
# Etale morphisms become finite etale on constructible strata

Source: Stacks Project, Etale Cohomology, Lemma 59.72.1, Tag 03S0
(blueprint: lem-weil-pbc-etale-stratified-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An etale morphism between quasi-compact quasi-separated schemes is finite etale
after restriction to each member of a finite constructible locally closed stratification.
Source: Stacks Project, Tag 03S0 (blueprint: lem-weil-pbc-etale-stratified-finite).

Proof:
1. For separated `j`, use the separated stratification theorem
   (`lem-weil-pbc-etale-separated-stratified-finite`, Stacks 07RZ). Etaleness is
   preserved by base change, so its finite locally free restrictions are finite etale.
2. On an affine base choose a finite affine cover of `U` and apply the separated case
   to its charts and overlaps (`lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`). Take
   a common refinement (`lemma-constructible-common-refinement`) and refine to affine
   strata. The charts and overlaps are now finite etale; the finite-cover gluing lemma
   (`lem-weil-pbc-etale-affine-cover-gluing`) makes each glued restriction separated.
3. Apply the separated case to these restrictions and take a finite common refinement.
   Fibre products throughout are those of `def-pc-fibre-product`.
4. Cover the original base by finitely many affine opens
   (`lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`). Glue their partitions using
   `lem-weil-pbc-etale-stratification-local-gluing`; constructibility, local closedness
   and the finite etale property are preserved on each resulting piece. -/
theorem exists_etale_stratified_finite {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j] :
    ∃ S : LocallyClosedStratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i))) := by
  sorry

end AlgebraicGeometry.Scheme
