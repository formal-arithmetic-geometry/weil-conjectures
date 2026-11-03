/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernClassAssembly
import WeilConjectures.AlgebraicGeometry.PurityChernKummerNaturality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernCupComparison

/-! # Independence of the Chern equation from its projective realization

Source: Stacks Project, Tags 01OB, 01O3, 01NR and 0FI5;
ordinary splitting-principle definition in localized-top-Chern Step 4 (L4).
(blueprint: lem-pur-chern-relation-realization).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Two normalized presentations of Proj(Sym F) give the same equation for any
specified family of coefficients. This is a compatibility statement; it asserts
neither existence nor uniqueness of a family satisfying that equation.
Source: Stacks Tags 01OB and 01O3, normalized relative Proj and its degree-one twist;
Tag 0FI5, equation-chern-classes; blueprint localized-top-Chern Step 4 (L4).
(blueprint: lem-pur-chern-relation-realization).

Proof:
1. Use the stipulated normalized comparison b over the identity. Its generator
condition fixes scalars and degree-one generators, and its over equation makes
its scheme isomorphism a map over T. No frame or new comparison is chosen.
2. The normalized degree-one twist comparison identifies the pullback of L with
L'. The quotient-generator condition identifies this with the actual O(1)
comparison; no scalar multiple of a twist isomorphism is substituted.
3. The proved ordinaryFiniteCohomologyComparison_bijective lifts each input
coordinate to an etale arrow. The proved projectiveBundleChern_pullback identifies
the pulled-back first Chern classes. Naturality of the unit diagonal, tensor
comparison and the positive shifted Tate pullbacks
identifies the recursive full-support cup products. Induct on their exponents;
the zero case uses the unit comparison and each successor uses tensor naturality.
The proved ordinaryFiniteCohomologyPullback_comp supplies composition of the
normalized cohomology pullbacks, and projectiveBundlePositivePullback_comp supplies
the coefficient composition law, both with their actual recorded comparisons.
Consequently pullback takes each summand of one
signed relation, and its right-hand side h^r, to the other.
4. Apply the proved ordinaryFiniteCohomologyPullback_injective from
PurityChernClassAssembly: normalized pullback along the scheme isomorphism reflects equality.
This proves both directions of the stated equivalence, including when T is
empty. Only finite-coefficient comparison and Kummer naturality are used; no
purity, supported Euler class, or higher Chern-class theorem is invoked. -/
theorem ordinaryFiniteProjectiveRelation_realization (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r]
    (D D' : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (hL' : D'.L.IsInvertible)
    (b : ProjectiveBundleBaseChangeDatum D D' (𝟙 T)
      ((projectiveBundlePullbackId T).app F).symm) [IsIso b.map]
    (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteProjectiveRelation t a D hL r c ↔
      P.ordinaryFiniteProjectiveRelation t a D' hL' r c := by sorry

end WeilConjectures.PurityFiniteSetting
