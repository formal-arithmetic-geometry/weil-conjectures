/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic
import Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

/-!
# Prime cyclic detection of a geometric-point coefficient

Source: Stacks Project, Tag 0F08, coefficient reduction in the proof, with
underlying-abelian comparison from Tag 03FD and qcqs colimits from Tag 0739.
(blueprint: lem-sbc-prime-cyclic-detection)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Nonvanishing with a geometric-point coefficient detects a prime cyclic abelian
coefficient, with a prime that is not a unit in the original coefficient ring.

Source: Stacks Project, Tag 0F08, proof's cyclic-coefficient reduction; Tag 03FD
for forgetting coefficients; Tag 0739 for qcqs cohomology and filtered colimits.
(blueprint: lem-sbc-prime-cyclic-detection)

Proof:
1. The small etale topos of Spec K is the point topos, since K is algebraically
closed. Thus F is constant with some Lambda-module M; exact inverse image takes
it to the constant M-sheaf on Y. The derived inverse image of F[0] is this sheaf
in degree zero. Forgetting the module structure identifies the underlying
higher direct image with the abelian higher direct image, by an injective module
resolution whose underlying abelian terms are acyclic (03FD).
2. As an abelian group M is killed by the nonzero integer n. Decompose it as a
sum of primary components and express each component as the filtered union of
its finitely generated subgroups. Each finite subgroup is a finite sum of cyclic
prime-power groups Z/r^k, where r divides n. On affine etale objects of X the
pullbacks of Y are qcqs, so 0739 gives commutation of cohomology with these
filtered unions; sheafifying gives the same commutation for higher direct images.
3. If r is a unit in Lambda, its action on M is invertible, so its primary
component is zero. If every remaining prime cyclic constant sheaf has zero
higher direct image in degree q, the exact sequences
0 -> Z/r^(k-1) -> Z/r^k -> Z/r -> 0 and their long exact sequences imply by
induction that all prime-power cyclic groups have zero image in degree q.
Finite additivity and step 2 then give zero for M, contradicting the hypothesis.
4. Choose a remaining prime with nonzero image. The underlying abelian group of
ULift(ZMod r) is Z/r; its constantModSheaf of order r equals its constant free
rank-one sheaf, since r = 0 in that ring. The comparison in step 1 and faithful
forgetting give the stated nonvanishing in prime-field module sheaves. For q < 0
all higher direct images here are zero, so the premise is impossible. -/
theorem exists_prime_cyclic_higherDirectImage
    (Λ : Type (u + 1)) [CommRing Λ] {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (n : ℕ) (hn : n ≠ 0)
    (hΛ : (n : Λ) = 0) (q : ℤ)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ¬ IsZero ((baseChangeTargetFunctor Λ e h q).obj F)) :
    ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ ¬ IsUnit (r : Λ) ∧
      ¬ IsZero (higherDirectImage (ULift.{u + 1} (ZMod r)) h q
        (constantModSheaf (ULift.{u + 1} (ZMod r)) Y r)) := by sorry

end AlgebraicGeometry.Etale
