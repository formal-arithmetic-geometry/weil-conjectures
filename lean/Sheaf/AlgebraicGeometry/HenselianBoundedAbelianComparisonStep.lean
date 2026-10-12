module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass
import Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Mathlib.CategoryTheory.Abelian.Basic
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder

/-! # The finite-coefficient successor step for henselian comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The successor step assumes comparison only in the preceding degree,
uniformly for abelian sheaves killed by the fixed integer n.

Source: Stacks Project, Tags 09ZE and 09ZI, finite Z/n coefficient construction.
(blueprint: lem-weil-pbc-henselian-bounded-abelian-comparison-step)

Proof:
1. Put Lambda = ULift (ZMod n). On a sheaf killed by n, scalar multiplication
   by an integer depends only on its residue mod n. Define this action on each
   group of sections; restriction maps preserve it. Thus G has its canonical
   Lambda-module sheaf structure, without choosing an arbitrary existence witness.
2. For any positive-degree closed-fibre class of a Lambda-module sheaf F,
   constructible filtered-colimit presentation, continuity of cohomology, and
   inverse-image/forgetful compatibility give a constructible C mapping to F
   and a class on its restriction representing the given class. Embed C in a
   finite sum of finite pushforwards of finite constant Lambda-modules.
   Finite base change and the finite-pushforward edge isomorphism transport each
   component class to a finite constant class on the finite cover's closed fibre.
   Kill each component by a finite surjective cover (09ZD). The corresponding
   adjunction unit is monic, and unit/edge compatibility says its cohomology map
   kills the component. Finite sums and composition give a monomorphism C to C'
   killing the represented class. Push out along C to F in Lambda-module sheaves.
   The map F to F' is monic and kills the class, by the pushout identity and
   functoriality. F', and its cokernel Q, are still Lambda-module sheaves, hence
   killed by n. Taking the closed subscheme to be the whole affine scheme gives
   the same effacement for source classes. This uses only the finite-coefficient
   construction of 09ZE, not the general-coefficient effacement in Gabber.lean.
3. Use pullbackCohomology_longExact_ladder for the following boundary squares
   and exact rows. For injectivity take a source class x in degree q+1 whose
   restriction is zero.
   Efface x by a monomorphism G to G', with cokernel Q as above. Exactness gives
   y in H^q(X,Q) with boundary x. On the fibre the boundary of the restriction
   of y is zero, so that restriction comes from z0 in H^q(Z,G'|Z).
   By hprev for G', lift z0 to z in H^q(X,G'). By naturality, the difference
   y minus the image of z restricts to zero. By hprev for Q it is zero. Thus y
   comes from G', so its boundary x is zero.
4. For surjectivity take a fibre class x0 in degree q+1. Efface it by another
   monomorphism G to G' killed by n. Exactness on the fibre gives y0 in
   H^q(Z,Q|Z) with boundary x0. By hprev for Q lift y0 to y in H^q(X,Q).
   Naturality of the boundary maps shows that the boundary of y restricts to x0.
5. Forget the canonical Lambda-module structure. Exact inverse image and exact
   forgetting give the same short exact sequences of abelian sheaves, and the
   compatible cohomology maps are the ones in the statement. For q=0 the
   argument uses only degree-zero comparison and the first boundary. For n=1
   all the coefficient sheaves are zero. For empty spectra the groups are zero.
-/
theorem bijective_cohomologyMap_succ_of_henselianRing_of_nsmul_eq_zero
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (n : ℕ) (hn : 0 < n) (q : ℕ)
    (hprev : ∀ (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      n • 𝟙 F = 0 → Function.Bijective
        (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q))
    (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : n • 𝟙 G = 0) :
    Function.Bijective
      (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G (q + 1)) := by sorry

end AlgebraicGeometry.Etale
