module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful

/-! # High cohomology of relatively degreewise pseudo-coherent complexes

Source: Stacks Project, More on Morphisms, Tag 0CSU, first assertion, using
Definition 09UI (blueprint: lem-sfb-relative-m-pseudocoherent-high-qcoh).

The derived object is unbounded, and the cohomology bound is strict.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Relative `m`-pseudo-coherence implies quasi-coherence of cohomology in degrees
strictly greater than `m`.
Source: Stacks Project, More on Morphisms, Tag 0CSU, first assertion, with
Definition 09UI (blueprint: lem-sfb-relative-m-pseudocoherent-high-qcoh).

Proof:
1. Fix `q > m`. Unpack `def-sfb-relative-pseudo-coherent-complex` to cover the source
   by affine opens `U` admitting closed embeddings `i : U → Y` into finite affine
   space over affine base opens, such that `L = Ri_*(E|_U)` is `m`-pseudo-coherent.
   Quasi-coherence is local by `pqf-def-coherent`; restriction is exact and thus
   commutes with cohomology, without requiring a bound on the complex.
2. By `def-sfb-m-pseudo-coherent-complex`, locally a strictly perfect complex maps
   to `L` inducing an isomorphism on degree `q` cohomology. A strictly perfect
   complex is perfect by `def-pc-perfect-complex`, so `lem-sc-perfect-qcoherent`
   makes this cohomology quasi-coherent. Locality gives quasi-coherence of `H^q(L)`.
3. Compute `Ri_*` on a K-injective representative `J` of `E|_U`, using
   `def-pc-ringed-spaces-derived-direct-image`. Apply
   `lem-pc-closed-module-pushforward-homology` to the triple in degrees
   `q-1, q, q+1`: ordinary module pushforward gives
   `H^q(L) ≅ i_*H^q(E|_U)`, also for an unbounded complex.
4. Put `F = H^q(E|_U)`. Its pushforward is quasi-coherent, so its pullback is
   quasi-coherent by `lem-weil-pbc-module-pullback-quasi-coherent`.
   The counit `i^*i_*F → F` is an isomorphism by
   `lem-weil-pbc-closed-immersion-pushforward-fully-faithful`. Thus `F` is
   quasi-coherent. Apply locality on the covering of `X` to conclude for `H^q(E)`.
-/
theorem isQuasicoherent_homology_of_isMPseudoCoherentRelativeTo
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (m : ℤ) (E : schemeDerivedCategory X) (hE : IsMPseudoCoherentRelativeTo f m E) :
    ∀ i : ℤ, m < i →
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme
