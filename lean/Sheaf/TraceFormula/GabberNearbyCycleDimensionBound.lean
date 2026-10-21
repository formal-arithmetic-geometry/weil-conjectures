module

public import Sheaf.Paper.OrientedNearbyCycles
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Algebra.ZMod
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.TraceFormula.OrientedPointCohomology
import Sheaf.Paper.OrientedProductPointsConservative
import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.StrictLocalDerivedGlobalExchange
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.AlgebraicGeometry.ProjectiveStrictLocalIntersectionAcyclic
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel

/-!
# Gabber dimension bound for torsion nearby cycles

Source: Illusie, Around the Thom--Sebastiani theorem, Theorem 1.14, printed p. 15
(PDF page 15) (blueprint: lem-trf-gabber-nearby-cycle-dimension-bound).

## Main statements

* `gabberNearbyCycleDimensionBound` states the vanishing of higher cohomology sheaves
  of nearby cycles above twice the fibre dimension for torsion coefficients.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles
open CategoryTheory.AdicSites

namespace AlgebraicGeometry

/--
Source: Illusie, Around the Thom--Sebastiani theorem, Theorem 1.14, printed p. 15
(PDF page 15) (blueprint: lem-trf-gabber-nearby-cycle-dimension-bound).

Proof (Gabber, Orgogozo Proposition 2.3, author version p. 4):
1. Fix an oriented geometric point `z = (x, t, c)` of `V_f`, `s = f(x)`, and put
   `M = X_(x) ×_{S_(s)} S_(t)`. The oriented-point cohomology theorem (second scheme `S`,
   `K = F[0]`) identifies `z^* RΨ_f(F[0])` with `RΓ(M, F|_M)`; constant-coefficient inverse
   image is exact and commutes with forgetting scalars, and the bounded-below
   evaluation/forget theorem identifies degree `q` with `H^q(M, A)`, `A` the underlying
   abelian sheaf of `F|_M`, with `m A = 0`.
2. The projective-local-model lemma for `f, x, N` gives, over `B = S_(s)`, a proper and
   projective `p : P → B` with fibre dimension at most `N`, a point `y` and
   `X_(x) ≃ P_(y)`. Put `C = S_(t)`, `Z = P ×_B C`, `p_C : Z → C`, `τ : M → Z`.
3. `P_(y)` is affine and `P` is separated (separated over affine `B`), so `P_(y) → P` is
   affine; its base change `τ` is affine, hence quasi-compact and quasi-separated.
4. Put `Q = Rτ_* A`, `i : Z_0 → Z` the closed geometric fibre over the residue field `k`
   of `C`. The strict-henselization stalk formula and ind-étale strict-local invariance give
   `(H^a Q)_u ≅ H^a(P_(y) ×_P P_(v), A)`, which vanishes for `a > 0` by strict-local
   intersection acyclicity (`P` projective over affine `B`); so `i^{-1} Q = H[0]`,
   `H = i^{-1} τ_* A`, with `m H = 0`.
5. Leray gives `H^q(M, A) = H^q(Z, Q)`; bounded-below proper base change for `p_C` and the
   strict-local global-exchange lemma give `H^q(M, A) ≅ H^q(Z_0, H)`.
6. `Z_0 → Spec k` is proper with fibre dimension at most `N` (fibre-dimension base change),
   so the proper torsion cohomological-dimension bound and the strict-local exchange give
   `H^q(Z_0, H) = 0` for `q > 2 * N`.
7. Hence `z^* H^q(RΨ_f(F[0])) = 0` for every oriented point `z` and `q > 2 * N`; joint
   conservativity of oriented geometric points gives the vanishing of the cohomology sheaf.
-/
theorem gabberNearbyCycleDimensionBound {X S : Scheme.{u}} (m : ℕ) (hm : 1 ≤ m)
    (Λ : Type (u + 1)) [CommRing Λ] [Algebra (ZMod m) Λ] (f : X ⟶ S)
    [LocallyOfFiniteType f] (N : ℕ)
    (hN : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (N : WithBot ℕ∞))
    (F : (OrientedNearbyCycles.etaleDatum.{u, u + 1} X).modules
      (OrientedNearbyCycles.Coeff.{u, u + 1} Λ)) (q : ℤ) (hq : 2 * (N : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((OrientedNearbyCycles.nearbyCycles f Λ).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry
