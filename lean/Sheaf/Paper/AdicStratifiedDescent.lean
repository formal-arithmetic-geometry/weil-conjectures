/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData
import Sheaf.Paper.TorsionLimitSheafCompleteness
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.ConstantModuleSectionProperties

/-!
# Descent and boundedness of stratified coefficient models

Source: Bhatt--Scholze, Definition 6.5.1, Remark 6.3.2 and Proposition 6.6.11.
(blueprint: lem-sfb-adic-stratified-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

/-- Finite stratified coefficient models give completeness, a constructible etale
residue with finite Tor amplitude, and global cohomological bounds.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse direction, and Lemma 6.5.3.
(blueprint: lem-sfb-adic-stratified-descent).

Proof: Each finite projective term is the image of an idempotent on a finite free
module. Its completed realization is the inverse limit of the corresponding
idempotent summands modulo I^n, since equalizers and finite products commute with
limits. Torsion-limit completeness and the constant/completed equivalence make
these terms complete; bounded complexes of them remain complete. Restriction to
stratum immersions and slices commutes with the Koszul completion unit, so finite
stratum detection gives global completeness. Quasi-compactness of the strata and
the pro-etale covering axiom select finitely many quasi-compact pieces of model
covers. The minimum and maximum term degrees bound K, by exact restriction and
stratum detection. Use [0,0] for an empty scheme. The local bounded flat models are
K-flat, and completed constant reduction computes their residue as P tensor_A A/I.
Exact constant realization identifies its cohomology with finite-dimensional
vector spaces; it vanishes outside the same finite term intervals. Finite-stratum
detection bounds the reduction globally. Noetherian global constructibility
identifies its finite stratification with the affine-local predicate of the
constructible comparison theorem. That theorem descends the bounded reduction to
an etale complex C. Finite modules over A/I are finitely presented. Apply the
etale global constructibility equivalence to its cohomology. Exact conservative
geometric stalks show that tensoring C with every degree-zero residue module
retains its cohomological interval, proving the finite Tor-amplitude clause. -/
theorem sfb_adic_stratified_descent
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    IsSfbAdicComplete X I K ∧ IsSfbResidueConstructible X I K ∧
      ∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b := by sorry

end AlgebraicGeometry.Scheme
