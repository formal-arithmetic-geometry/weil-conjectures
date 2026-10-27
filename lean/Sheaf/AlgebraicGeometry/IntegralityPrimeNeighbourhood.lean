module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso

/-!
# Integrality near a prime localization

Source: Stacks Project, Properties, Tags 01OL, 01OM and 01ON, together with the
Noetherian finite affine localization-kernel argument recorded in the DAG.
This is an agent-formulated consequence, not a verbatim assertion of Tag 01ON.
(blueprint: lem-per-integrality-prime-neighbourhood)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-type scheme over a Noetherian ring which is integral after localization
at a prime is integral after localization at some element outside that prime.

Source: Stacks Project, Properties, Tags 01OL, 01OM and 01ON; the finite affine
localization-kernel consequence formulated in the DAG, supplying the integrality
step in the spreading paragraph of Kurano--Shimomoto, Lemma 4.4.
(blueprint: lem-per-integrality-prime-neighbourhood)

Proof:
1. Choose a finite affine cover `U_i = Spec B_i` using finite type
   (`def-weil-finite-type-morphism`). The `B_i` are Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. By
   `lem-weil-pbc-affine-chart-base-change-iso`, their inverse images on the two
   base changes are affine with tensor-product coordinate rings, and still cover.
2. Write `S = R ∖ p` and `C_i = S⁻¹ B_i`. Identify the tensor products with
   `C_i` and `B_i[1/b]`: send `(r/s) ⊗ x` to `rx/s`, with inverse sending `x/s`
   to `(1/s) ⊗ x`. The fraction relations and tensor balancing prove that these
   maps are well defined and inverse (`def-weil-pbc-localization-at-prime`,
   `def-weil-ring-localization-away`, `def-weil-pbc-module-localization`).
3. Each ideal `K_i = ker (B_i → C_i)` has finitely many generators. Choose an
   element of `S` killing each generator, using the zero-fraction criterion.
   Their finite product `a` lies outside `p` and kills all `K_i`; an empty product
   is `1`. Thus `B_i[1/a] → C_i` is injective: a fraction mapping to zero has
   numerator in `K_i`, so multiplication by `a` kills it.
4. Let `J` index the nonempty charts on the prime base change. For `i ∈ J`,
   `C_i` is a domain, so its unital subring `B_i[1/a]` is a domain. For `i ∉ J`,
   `C_i` is the zero ring; injectivity forces `B_i[1/a]` to be the zero ring,
   so this chart is empty. Hence the charts indexed by `J` still cover, and `J`
   is nonempty because the prime base change is integral and therefore nonempty.
5. By `lem-pc-integral-scheme-irreducible`, nonempty prime-base-change charts
   meet pairwise. The canonical map from the prime base change to the `a` base
   change sends each intersection witness into the corresponding intersection
   (`def-pc-fibre-product`). No intersection of affine opens need be affine.
6. Apply `lem-per-integral-affine-cover-criterion`: this nonempty affine cover
   has domain coordinate rings and pairwise nonempty intersections. The `a`
   base change is therefore integral, as required. -/
theorem exists_isIntegral_localizationAway_of_isIntegral_atPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (h : IsIntegral (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
    ∃ a : R, a ∉ p ∧ IsIntegral (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a))))) := by
  sorry

end AlgebraicGeometry
