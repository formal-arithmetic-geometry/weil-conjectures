module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
import Sheaf.SixFunctors.FlatModelGeneration
import Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant
import Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Paper.StratumAmbientHom
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility

/-! # Finite-Tor internal Hom over an arbitrary field

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemma 6.7.13,
Definition 6.5.1 and its finite-coefficient comparison paragraph
(blueprint: lem-per-finite-tor-internal-hom-any-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Ambient internal Hom of finite-Tor bounded constructible finite-coefficient complexes
is bounded constructible and has bounded constructible étale origin over any ground field.

Source: Bhatt–Scholze, Lemma 6.7.13, p. 57, and Definition 6.5.1, p. 49
(blueprint: lem-per-finite-tor-internal-hom-any-field).

Proof:
1. The coefficient ring A = O_E/ϖ^n is finite and Noetherian, and is killed by ℓ^n,
which is invertible in k. Finite A-modules are precisely finitely presented ones.
2. Finite-type k-schemes, their locally closed strata, closures and open complements
are Noetherian and qcqs. No perfection or separable closedness of k is required.
3. Bounded complexes with constructible finite-valued cohomology form a thick subcategory:
use the constructible weak Serre property for triangles and kernels of idempotents for retracts.
4. Exact constant-coefficient inverse image preserves cohomological bounds and pulls back
finite constructible stratifications and their finite locally constant models.
5. Finite-type direct image preserves bounded constructibility: choose a bounded constructible
étale origin, apply finite-type étale finiteness, and use the qcqs direct-image comparison.
6. For a closed immersion g with open complement h, the support triangle
 g_* Rg^! N → N → Rh_* h^* N
and steps 3--5 give constructibility of g_* Rg^! N. Apply exact g^* and g^*g_* ≅ 1.
7. For a locally constant finite projective sheaf L on a stratum, perfect duality gives
RHom(L,N) ≅ L^∨ ⊗ᴸ N. Locally this is a finite projective summand of finite sums of N,
so it has bounded constructible finite-valued cohomology.
8. Finite-Tor constructible K is generated, under shifts, cones, isomorphisms and retracts,
by a_! L with a locally closed and L locally constant finite projective. Factor a = j ≫ g
with j open in the closure and g closed, so a_! L = g_* j_! L.
9. Apply ambient internal adjunction first to g and then to j:
RHom(g_*j_!L,M) ≅ Rg_* Rj_* RHom(L,j^*Rg^!M).
Steps 4--7 and 5 show that this is bounded constructible.
10. For fixed M, the inputs P for which RHom(P,M) is bounded constructible form a thick
subcategory by the exactness, shifts and contravariance of ambient Hom. Steps 8--9 put K in it.
11. Finite-ring constructible derived comparison gives the bounded constructible étale
origin of the resulting object. Empty X and zero inputs give zero; n = 1 is included.
The finite-Tor hypothesis on M is retained as stated, though this argument needs only its
bounded constructibility. There is no characteristic assumption beyond ℓ being invertible.
-/
theorem finiteTor_internalHom_constructible_anyField
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (K M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hK : WeilConjectures.finiteTorConstructible l E n hn X K)
    (_hM : WeilConjectures.finiteTorConstructible l E n hn X M) :
    intrinsicFiniteTorsionConstructible l E n hn X
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, M)) ∧
    ∃ L : ProEtale.FiniteCoefficientEtaleDerivedCategory X
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)),
      @Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
        (Finite.of_equiv (Padic.coefficientExtensionRing l E n)
          (h := Padic.finite_coefficientExtensionRing l E n hn) Equiv.ulift.symm) X L ∧
      Nonempty ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison X
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj L ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, M)) := by
  sorry

end AlgebraicGeometry.Scheme
