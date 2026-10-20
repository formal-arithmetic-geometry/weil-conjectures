/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.IntegralStratumHomFormula
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension
import Sheaf.Paper.IntegralCriterionReductions
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.CompletedConstantSheafReduction
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Sheaf.Paper.FormalClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Paper.CartesianCoefficients
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.BoundedHeartAmplitude
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.IntegralConstructibleHeart
import Sheaf.Paper.IntegralModels

/-!
# Uniform vanishing of integral constructible Ext

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext,
sk-lem-int-ext-bound.md and sk-lem-int-ext.proof.md
(blueprint: det-lem-int-ext-bound).

Both clauses concern the ordinary unbounded derived category over the completed integral
coefficient sheaf. The stratum sheaf may have torsion. The cohomological dimensions use
the recorded classical, locally ell-power torsion convention.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Ext from a stratum extension vanishes above `cd_ell(j) + cd_ell(S) + 3`;
every integral constructible sheaf has a nonnegative bound uniform in the target sheaf.
The natural number `d` names the finite displayed cohomological-dimension bound, while
Ext degrees are arbitrary integers. The qcqs instances only supply the domains of the
recorded dimensions: every locally closed subscheme and complementary open of the
Noetherian finite-type X has these properties.

Source: blueprint main-20261015, sk-lem-int-ext-bound and its twelve-step DAG proof;
Stacks Project, Tags 099M, 08JJ and 08TB (blueprint: det-lem-int-ext-bound).

Proof:
1. The algebraically closed base has ell-cohomological dimension zero by
sk-lem-base-field-cd. Finite-type finiteness in sk-def-cd gives finite nonnegative
c = cd_ell(j) and s = cd_ell(S). Write B_T = O_{E,T} and A_{n,T} = (O_E/pi^n)_T.
2. For constructible N, sk-lem-int-integral-heart puts N[0] in Dbc. By
sk-lem-integral-models, N is derived complete. Its canonical derived reductions N_n
are bounded constructible by det-prop-integral-criterion-reductions and classical by
sk-thm-pe-constructible-comparison. The quotient maps define the tower, with
N isomorphic to its derived inverse limit.
3. The length-one free quotient resolution from lem-weil-pbc-standard-quotients-perfect
and lem-weil-pbc-completed-constant-sheaf-reduction represents N_n by
[N --pi^n--> N] in degrees [-1,0]. Its cohomology is killed by pi^n and a power of ell.
4. Use the derived dual D = RHom(L,B_S), including when L has torsion.
sk-lem-int-integral-heart gives dualizability and Tor amplitude [0,1]. Evaluation and
coevaluation identify RHom(L,M) with D tensor M by their triangle identities and
def-sfb-derived-tensor-hom-adjunction-modules. The support adjunction of
sk-lem-formal-closed-support and the exact open adjunction of
sk-def-sfb-module-lower-shriek, derived using lem-pc-derived-adjoint-functors and
lem-weil-pbc-exact-functor-derived-functor, give
Ext^r(a_!L,K) = H^r RΓ(S,D tensor u^* RΓ_Z K) by lem-pur-rhom-global-sections.
5. D_n = D tensor A_n has Tor amplitude [0,1] by tensor associativity. Locally resolve
the finite O_E-module modeling L by two finite free modules: O_E is a DVR by
lem-weil-l-adic-extension-integers-dvr and the kernel is free by
lem-sc-dvr-saturation-line-smith-normal-form. Flatness of the completed coefficient
sheaf preserves that resolution. Dualize it and reduce its constant matrices modulo
pi^n. This proves bounded constructibility and classicality of D_n, using
sk-def-sfb-constructible and sk-thm-pe-constructible-comparison. The coefficient tensor
comparison is lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
6. For the open complement, lem-weil-pbc-ring-sheaf-change-adjunction identifies
restriction of scalars of Rj_{A,*} with Rj_{B,*} of restriction of scalars, including
units. Its coefficient squares commute by sk-prop-sfb-cartesian-coefficients and
naturality of pullback of O_E -> O_E/pi^n. Inverse images also commute with restriction.
7. By sk-def-cd, det-pbc-conventions-module-cohomology and
sk-thm-pe-direct-image-comparison, Rj_{A,*} has upper bound c on classical torsion
sheaves. The lower bound zero is lem-weil-pbc-derived-functor-negative-vanishing,
using lem-weil-pbc-ring-sheaves-grothendieck. Triangulatedness is
lem-pc-right-derived-functor-triangulated. Thus lem-pur-bounded-heart-amplitude sends
j^*N_n in [-1,0] to [-1,c]. The same comparison proves classicality.
8. The support fibre of N_n -> Rj_*j^*N_n lies in [-1,c+1] by
lem-sf-derived-homology-long-exact. Exact inverse images, using
sk-prop-sfb-cartesian-coefficients and lem-weil-pbc-exact-functor-complex-cohomology,
give M_n = u^* RΓ_Z N_n in that interval. Direct-image comparison identifies its
fibre with the pullback of the etale fibre, so M_n is classical.
9. Put T_n = D_n tensor_{A_n} M_n = D tensor_{B_S} M_n. Filter M_n by its finitely
many shifted cohomology sheaves using lem-weil-pbc-truncation-triangle. Tor amplitude
[0,1], exact tensor and lem-sf-derived-homology-long-exact place T_n in [-1,c+2].
Exactness follows by tensoring K-flat cones as in lem-weil-pbc-site-derived-tensor-descent.
The classical equivalence det-pe-classical-derived-equivalence, its unit from
sk-prop-sf-comparison, Tor reflection det-pe-finite-tor-comparison-noetherian and the
ringed tensor pullback comparison make this a bounded classical A_n-complex.
10. Apply derived sections to that finite cohomology filtration. The definition of s,
sk-prop-sf-comparison, det-pbc-conventions-module-cohomology and triangulatedness of
derived sections give upper bound c+s+2. The scalar-extension/restriction adjunction
lem-weil-derived-scalar-extension-restriction-adjunction and
lem-pur-rhom-global-sections identify integral and finite-coefficient sections here.
Step 4 gives Hom(a_!L,N_n[r]) = 0 for r > c+s+2, uniformly in n and N.
11. det-pe-products-derived and def-weil-derived-limit give the Roos triangle
N -> P -> P -> N[1], with P the product of the N_n. Hom into each shifted P is the
product of the Hom groups into the shifted N_n. For r > c+s+3 both Hom(a_!L,P[r-1])
and Hom(a_!L,P[r]) vanish. Exactness from lem-weil-pbc-hom-into-triangle-exact then
annihilates Hom(a_!L,N[r]). No immersion inverse image is commuted with this limit.
12. Clause (1) of det-lem-int-ext-formula filters a constructible sheaf C by finitely
many degree-zero stratum extensions. Take d_C to be the maximum of their bounds,
or zero for the empty filtration. At each triangle, the outside terms of the
contravariant Hom exact sequence lem-weil-pbc-hom-out-of-triangle-exact vanish.
Induction gives the required bound simultaneously for all constructible N. -/
theorem integral_stratum_ext_bound
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    (∀ (S Z V : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
      [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j],
      Set.range j = (Set.range i)ᶜ →
      ∀ L : pulledBackModuleObjects (integralCoefficientRing l E) S,
        IsConstantModelConstructible (integralCoefficientRing l E) S L →
        HasFiniteConstantLocalModel (integralCoefficientRing l E) S L →
        ∃ d : ℕ,
          (d : WithTop ℕ) = relativeCohomologicalDimension l (Fact.out : l.Prime) j +
            cohomologicalDimension l (Fact.out : l.Prime) S + 3 ∧
          ∀ N : pulledBackModuleObjects (integralCoefficientRing l E) X,
            IsConstantModelConstructible (integralCoefficientRing l E) X N →
            ∀ r : ℤ, (d : ℤ) < r →
              Subsingleton (((DerivedCategory.singleFunctor _ 0).obj
                ((lowerStar (integralCoefficientRing l E) i).obj
                  ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))) ⟶
                ((DerivedCategory.singleFunctor _ 0).obj N) ⟦r⟧)) ∧
    (∀ C : pulledBackModuleObjects (integralCoefficientRing l E) X,
      IsConstantModelConstructible (integralCoefficientRing l E) X C →
      ∃ d : ℕ, ∀ N : pulledBackModuleObjects (integralCoefficientRing l E) X,
        IsConstantModelConstructible (integralCoefficientRing l E) X N →
        ∀ r : ℤ, (d : ℤ) < r →
          Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C) ⟶
            ((DerivedCategory.singleFunctor _ 0).obj N) ⟦r⟧)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
