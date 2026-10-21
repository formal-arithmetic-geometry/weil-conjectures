/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import Mathlib.GroupTheory.Exponent

import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ConstructibleSheafDevissage
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt
import Sheaf.Paper.SfAffineChartFactorizationGluing
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback
import WeilConjectures.RingTheory.FiniteFreeResolution
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.Paper.StratumAmbientHom
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility

/-!
# Constructibility of the finite-coefficient Verdier dual over a field

Source: BBD, Faisceaux pervers, §§4.1 and 4.2.4, with the finite-coefficient background
of §§2.2.12–2.2.13 and 4.0 (blueprint: lem-per-finite-coefficient-dual-constructible).
The ordinary unbounded small-etale categories are used throughout. No finite Tor
amplitude of the input complex or algebraic closedness of the base field is assumed.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- Over a field, the exceptional dualizing complex for finite coefficients of invertible
additive exponent is bounded constructible. The Verdier dual of every bounded constructible
complex is bounded below and has constructible cohomology in every degree.
Source: BBD, §§4.1 and 4.2.4, with §§2.2.12–2.2.13 and 4.0 as background
(blueprint: lem-per-finite-coefficient-dual-constructible).

Proof:
1. Both claims are local on T. Exceptional-adjoint locality and internal-Hom restriction
   identify their restrictions to opens. Constructibility glues along a finite open cover;
   bounds glue by taking the minimum and maximum. The affine-chart factorization lemma
   gives a finite affine cover with closed embeddings into affine spaces. The empty
   scheme is immediate.
2. On a chart i:T -> P = A^n_k, composition of compact supports and uniqueness of right
   adjoints identify omega_T with Ri^! p^! Lambda. Affine-space adjunction gives
   p^! Lambda = Lambda_P(n)[2n], bounded constructible since the finite twist is lisse of
   rank one. The closed-support triangle i_*Ri^!M -> M -> Rh_*h^*M and finite-type
   direct-image constructibility make i_*Ri^!M bounded constructible. Constructible
   sheaves form a Serre subcategory. Closed direct image is exact and i^*i_* = 1, so
   Ri^!M is bounded constructible too. This proves the first claim on every chart.
3. If K is bounded above by r and omega_T below by c, bounded-above RHom hyper-Ext
   gives the lower bound c-r. The finite truncation tower and constructible devissage
   reduce constructibility to G = c_*u_!L on a locally closed stratum S, with L finite
   lisse. On U = T minus (closure(S) minus S), S is closed; write s = i followed by j,
   with i closed and j open. Restriction identifies j^*G with i_*L, and the counit
   j_!j^*G -> G is an isomorphism because the stalks off U vanish. Thus G = Rs_!L.
   Stratum ambient Hom identifies its dual with Rs_*RHom(L,omega_S); composition of
   compact supports identifies s^!omega_T with omega_S. Each S is separated finite type.
4. Etale locally L is constant with finite module value L0. The finite ring is
   Noetherian, so L0 has a bounded-above finite free resolution. The bounded-free RHom
   model against a constructible sheaf F has finite sums of F as its nonnegative
   terms and zero negative terms. Serre closure makes every Ext sheaf constructible.
   The bounded-above RHom hyper-Ext spectral sequence for omega_S has a finite
   abutment filtration in each degree and stabilizes there. Kernels, cokernels and
   extensions therefore make every cohomology sheaf of RHom(L,omega_S) constructible.
   Internal-Hom restriction and descent along a finite union of affine etale
   trivializing charts descend these calculations. The same hyper-Ext bound gives D+.
5. For N bounded below with constructible cohomology, a bounded-below injective
   resolution of tau^{>=q+1}N is zero in degrees <=q; so is its termwise direct image.
   The truncation triangle gives H^q(Rs_*N) = H^q(Rs_*tau^{<=q}N). The latter is
   constructible by finite-type direct-image constructibility. Serre closure along
   the finite towers in step 3 finishes the second claim. -/
theorem finiteCoefficient_dual_constructible
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (_hΛ : IsUnit (AddMonoid.exponent Λ : k))
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    DerivedCategory.isBoundedConstructible Λ T (dualizingComplex (ModuleCat.{u + 1} Λ) a) ∧
      ∀ K : DerivedCategoryModule Λ T, DerivedCategory.isBoundedConstructible Λ T K →
        _root_.DerivedCategory.TStructure.t.plus
          ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) ∧
        ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
            ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K))) := by
  sorry

end AlgebraicGeometry.Etale
