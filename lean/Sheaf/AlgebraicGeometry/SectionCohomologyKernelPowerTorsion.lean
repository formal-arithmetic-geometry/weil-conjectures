/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.AlgebraicGeometry.InvertSCOhomology
import Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero

/-! # Power torsion in the kernel of resolution cohomology restriction

Source: Stacks Project, Tags 09MR and 01E4.
(blueprint: lem-pc-section-cohomology-kernel-power-torsion).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A raw resolution cohomology class vanishing on a principal open is power torsion.

Source: Stacks Project, Tag 09MR (lemma-invert-s-cohomology), injectivity of the
canonical comparison specialized to the tensor unit; Tag 01E4 for its resolution model.
(blueprint: lem-pc-section-cohomology-kernel-power-torsion).

Proof: Set Y = f⁻¹W, b = f^♯a and G = F restricted to Y. The qcqs hypotheses on
f and affineness of W make Y qcqs, and G is quasi-coherent. Exact open
restriction preserves injectives. Sections of the restricted resolution on Y
and D(b) are the evaluations of f_*I at W and D(a), because f⁻¹D(a) = D(b).
Exact evaluation commutes with homology. These comparisons identify the raw
presheaf restriction with the cohomology restriction and scalar multiplication
by a with multiplication by b, rather than merely identifying the two groups.

Apply invertS_cohomology to Y, the tensor unit and b. Use the unitors to view the
class x as the degree-zero numerator ξ in H^q(Y,G tensor O_Y^{tensor 0}). The
canonical comparison sends [0,ξ] to its restriction: its equation at n = 0
is the cohomology restriction equation, with the tensor unitors cancelled.
The hypothesis therefore says that this comparison sends [0,ξ] to zero.
Injectivity of the additive equivalence implies [0,ξ] = 0. Apply
cohomologyFraction_eventually_zero to obtain k with the transition numerator
zero. Under the canonical tensor-unit identifications this transition is
multiplication by b^k: tensorPowSection of b evaluates to b^k, and its tensor
product with G acts by that scalar. Functoriality of cohomology and the
resolution comparisons then give a^k • x = 0. This is only the kernel
assertion; it gives no lifting on D(a). For a = 0 use k = 1, since the target
is cohomology of the empty open; for a a unit restriction is an isomorphism
and x = 0. Empty W, zero F and degree zero are also included. -/
theorem sectionCohomologyPresheaf_kernel_pow_annihilates {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    ∀ x : P.obj (op W), (P.map (homOfLE (T.basicOpen_le a)).op).hom x = 0 →
      ∃ n : ℕ, a ^ n • x = 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
