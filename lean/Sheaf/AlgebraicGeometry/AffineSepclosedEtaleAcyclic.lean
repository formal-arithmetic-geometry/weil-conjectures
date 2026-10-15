/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Sheaf.RingTheory.StrictlyHenselianOfDimensionZero
import Sheaf.Paper.StrictHenselianZariskiEtaleComparison
import Sheaf.Topology.ProfiniteCohomologyVanishing

/-!
# Étale acyclicity of affine schemes with closed separably closed points

Source: Stacks Project, Étale Cohomology, Tag 09AY, `lemma-affine-only-closed-points`
(blueprint: lem-cbc-affine-sepclosed-etale-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An affine scheme whose points are closed and whose residue fields are separably
closed has zero higher étale cohomology for every abelian sheaf.
Source: Stacks Project, Étale Cohomology, Tag 09AY
(blueprint: lem-cbc-affine-sepclosed-etale-acyclic).

Proof:
1. Write T as Spec A. A point's closure is V(p), so closedness of every singleton
   makes every prime maximal: a larger proper ideal would lie in a prime by
   lem-weil-pbc-minimal-prime-over-proper-ideal. Apply
   lem-weil-pbc-zero-dimensional-spectrum-profinite to obtain a profinite space.
2. Every prime is also minimal. The stalk is A_p by
   lem-weil-pbc-spec-domain-stalks-function-field. Applying
   lem-weil-pbc-minimal-prime-localization-radical to the zero ideal shows that its
   maximal ideal is its nilradical, hence its only prime. The residue field is the
   assumed separably closed field. Now
   lem-weil-pbc-dimension-zero-local-strictly-henselian makes every stalk strictly henselian.
3. By lem-weil-pbc-gabber-strict-henselian-zariski-comparison, étale cohomology is
   canonically isomorphic to Zariski cohomology of the direct image epsilon_* F.
   This does not identify F itself with a Zariski sheaf.
4. By def-sc-topological-abelian-cohomology, Zariski cohomology is cohomology on
   the open-set site of the underlying space. Apply
   lem-cbc-profinite-topological-cohomology-vanishing to epsilon_* F and transport
   vanishing through the comparison isomorphism. The recorded global `Sheaf.H`
   computes right derived global sections; no noetherian, finite-type or torsion
   assumption enters the argument. -/
theorem subsingleton_H_of_affine_closed_isSepClosed
    (T : Scheme.{u}) [IsAffine T]
    (hclosed : ∀ t : T, IsClosed ({t} : Set T))
    (hsep : ∀ t : T, IsSepClosed (T.residueField t))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : ℕ) (hi : 0 < i) : Subsingleton (Sheaf.H F i) := by
  sorry

end AlgebraicGeometry.Scheme
