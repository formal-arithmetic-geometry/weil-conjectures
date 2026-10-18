/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.RingTheory.AffineGeometricallyIntegralProjective
import Sheaf.RingTheory.LocalUniversalInjectiveResidue
import Sheaf.RingTheory.UniversalInjectiveLocalization
import Sheaf.TraceFormula.LocalUIFlatCokernel

/-!
# Local generic-basis subtraction criterion

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, implication (1)⇒(2).
(blueprint: lem-trf-local-generic-basis-universal-injective)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z t

namespace RingHom
open scoped TensorProduct

/-- The fibre domain condition transports from a universe containing the rings to an
arbitrary universe of residue-field extensions.

Source: Stacks Project, Algebra, Tag 05DX, `definition-geometrically-integral`; Tag 05I3,
`lemma-induction-step`, geometric-integrality hypothesis.
(blueprint: lem-trf-local-generic-basis-universal-injective)

Proof: Fix `p` and a residue-field extension `K`. Each finite family of elements of
`K ⊗[R] S` is represented using finitely many coefficients of `K`. The subfield generated
by these coefficients and the image of `κ(p)` is small in `max u v w`: its cardinality
is bounded by the maximum of the cardinality of `κ(p)` and that of the natural numbers.
Shrink this subfield, lift to `max u v w`, and transport the `R`-algebra structure and
residue-field map along the field equivalence. Apply `hgeom` to that field. Tensor
extension along its embedding into `K` is injective, since a field extension is faithfully
flat. Thus a product of two nonzero elements in `K ⊗[R] S` cannot vanish: choose the
subfield for both elements and use the domain property there. The same argument with
`1` shows nontriviality. Tensor associativity identifies this with extending the affine
fibre `p.asIdeal.Fiber S`; tensor symmetry accounts for either order of the factors.
This supplies the universe transport, including the identity extension and extensions
whose universe is smaller or larger than the universes of the rings.
-/
theorem geometricFibres_domain_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S))
    (p : PrimeSpectrum R) (K : Type z) [Field K] [Algebra R K]
    (ι : p.asIdeal.ResidueField →+* K)
    (hι : algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField)) :
    IsDomain (K ⊗[R] S) := by
  sorry

/-- The maximal ideal extension is prime under geometric integrality of the fibres.

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, implication (1)⇒(2).
(blueprint: lem-trf-local-generic-basis-universal-injective)

Proof: use `geometricFibres_domain_baseChange` at the maximal ideal, with its residue
field and the identity residue-field extension. This yields that the closed fibre is a
domain in its own universe. Since `R` is local, this fibre is canonically isomorphic to
`S` modulo the extended maximal ideal. A quotient is a nonzero domain exactly when its
ideal is prime. This is the derived canonical structure used
by the main statement; no prime ideal is assumed separately.
-/
theorem maximalIdeal_map_isPrime_of_geometricFibres
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S)) :
    Ideal.IsPrime (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) := by
  sorry

/-- A generic-basis map into a finite module over a flat finitely presented algebra is
universally injective, with flat localized cokernel.

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, implication (1)⇒(2).
(blueprint: lem-trf-local-generic-basis-universal-injective)

Proof:
1. Use `maximalIdeal_map_isPrime_of_geometricFibres` to obtain primality of `ξ = mS`.
   The node `lem-trf-local-fibres-integral-projective`, recorded as
   `Algebra.projective_of_geometricallyIntegral_fibres`, gives projectivity of `S`
   over `R`, hence of `S^r`. Tensor symmetry and `Spec.residueFieldIso` identify
   its fibre hypothesis with `hgeom`; `geometricFibres_domain_baseChange` handles
   arbitrary universes of field extensions.
2. Reduce `S^r → N_q` modulo `m`. Its composite to `N ⊗[S] κ(ξ)` factors through
   the injection `(S/mS)^r → κ(ξ)^r` and the isomorphism induced by `α`.
   Here `ξ ⊆ q`, so localization at `ξ` factors through localization at `q`.
   Consequently the reduction is injective. Apply
   `lem-trf-local-universal-injective-residue`, recorded as
   `Module.universallyInjective_of_residueField_injective`, to the projective
   source and the flat module `N_q`. This makes `S^r → N_q` universally injective.
3. This map is the composite of `α` with `N → N_q`. Injectivity of that composite
   after tensoring makes `α` universally injective. By
   `lem-trf-local-universal-injective-localization`, recorded as
   `LinearMap.universally_injective_localizedModule_map`, the map localized at `q`
   is also universally injective. Tensor right exactness now makes the localized
   cokernel sequence universally exact. Apply `lem-trf-local-ui-flat-cokernel`,
   recorded as `Module.flat_of_universally_exact`, with flat middle term `N_q`.
   This gives flatness of `(coker α)_q`.

The cases `r = 0`, the zero module and a field base use the same tensor and quotient
constructions. Restricted `R`-actions on localized modules are explicitly `Module.compHom`.
The compatible `R`-action on `N` is its unique restriction along `R → S`.
-/
theorem local_generic_basis_universal_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    (hflat : RingHom.Flat (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S))
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S))
    (r : ℕ) (N : Type t) [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [Module.Finite S N]
    (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (hNq : @Module.Flat R (LocalizedModule q.asIdeal.primeCompl N) _ _
      (Module.compHom (LocalizedModule q.asIdeal.primeCompl N) (algebraMap R S)))
    (α : (Fin r → S) →ₗ[S] N)
    (hα : Function.Bijective
      (LinearMap.lTensor
        (@Ideal.ResidueField S _ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
          (maximalIdeal_map_isPrime_of_geometricFibres (R := R) (S := S) hgeom)) α)) :
    (∀ (L : Type z) [AddCommGroup L] [Module R L],
      Function.Injective (LinearMap.lTensor L (α.restrictScalars R))) ∧
      @Module.Flat R (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)) _ _
        (Module.compHom (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α))
          (algebraMap R S)) := by
  sorry

end RingHom
