/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyClosed
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# Extension by zero preserves finite-Tor constructibility

Source: Weil conjectures blueprint, sec-six-functors/sk-lem-sf-open-ctf,
order 2161 (blueprint: lem-trf-open-ctf).

The cohomological interval and the Tor interval are independent. The functor on
derived categories is the termwise descent of the recorded exact extension by zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Termwise extension by zero at a positive finite coefficient stage, descended
along quasi-isomorphisms using its recorded exactness. The coefficient ring is the
recorded quotient by the chosen uniformizer, with its canonical finiteness witness.
Source: blueprint lem-trf-open-ctf, proof step 1; Stacks, Tag 03DJ
(blueprint: lem-trf-open-ctf). -/
noncomputable def finiteStageDerivedExtensionByZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E n)).mapDerivedCategory

/-- Extension by zero preserves bounded constructibility, finite Tor amplitude,
every cohomological interval, and every Tor interval, independently.
Source: blueprint sec-six-functors/sk-lem-sf-open-ctf, order 2161
(blueprint: lem-trf-open-ctf).

Proof, following the four steps of the node:
1. Use the finite coefficient convention A = O_E / varpi_E^n, n >= 1 and l != p.
The prime l is invertible over the global base field. Exactness of j_!
(lem-weil-extension-by-zero-exact) identifies H^r(j_!K) with j_!H^r(K), by
preservation of kernels, images and their quotients
(def-weil-derived-cohomology-sheaves). Thus termwise extension descends through
quasi-isomorphisms and preserves any supplied cohomological range [c,d].
2. Finite-type schemes over a field are Noetherian. Their locally closed subsets
are constructible (def-weil-constructible-subset), so j is quasi-compact
(def-weil-finite-type-morphism). Extend each finite stratification of H^r(K) from
U to Y: a locally closed stratum of the open U is locally closed in Y
(def-weil-locally-closed-subset). Add the reduced closed complement Y minus U.
3. The full module-sheaf identities j^*j_! = id and i^*j_! = 0 from
lem-weil-pbc-proetale-ringed-open-closed identify the restrictions on these strata.
Pullback composition (lem-weil-pbc-proetale-derived-pullback-composition) applies
with constant coefficient identifications: both send every constant section to
the same section. The original strata retain their finite locally constant
modules; the complement carries the finite zero module. Separate stratifications
for each r suffice for def-weil-finite-torsion-constructibility.
4. For an arbitrary degree-zero A-module sheaf M on Y, exact constant-coefficient
pullback gives j^*(M[0]) = (j^*M)[0]
(def-weil-derived-pullback-tensor-hom). The open tensor formula
(lem-trf-open-tensor) identifies (j_!K) tensor^L M with
j_!(K tensor^L j^*M). The Tor hypothesis on K kills its cohomology outside [a,b];
exactness and step 1 give the same vanishing after j_!. This tests every M,
without a constructibility assumption on M, and proves the original Tor bound
and membership in D^b_ctf (def-weil-finite-tor-amplitude). -/
theorem finiteStageDerivedExtensionByZero_constructibleFiniteTor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (j : U ⟶ Y) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of D.k))]
    (K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn U K)
    (hTor : HasFiniteProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E n) K) :
    WeilConjectures.finiteTorConstructible l E n hn Y
        ((finiteStageDerivedExtensionByZero l E n hn j).obj K) ∧
      (∀ c d : ℤ,
        (∀ r : ℤ, (r < c ∨ d < r) →
          IsZero ((DerivedCategory.homologyFunctor
            (proEtaleRingModules U
              (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj K)) →
        ∀ r : ℤ, (r < c ∨ d < r) →
          IsZero ((DerivedCategory.homologyFunctor
            (proEtaleRingModules Y
              (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) r).obj
                ((finiteStageDerivedExtensionByZero l E n hn j).obj K))) ∧
      (∀ a b : ℤ,
        HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E n) K a b →
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
          ((finiteStageDerivedExtensionByZero l E n hn j).obj K) a b) := by
  sorry

end AlgebraicGeometry.Scheme
