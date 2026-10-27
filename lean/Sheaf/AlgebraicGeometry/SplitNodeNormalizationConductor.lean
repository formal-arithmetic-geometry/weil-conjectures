/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Affine normalization and the split-node conductor

Source: Stacks Project, Morphisms, Tags 035P and 0CDV; Models, Tag 0CDD.
The conductor and fibre-product formulas are the explicit polynomial calculation
(blueprint: lem-sfb-split-node-normalization-conductor).

The auxiliary constructions below spell out the rings and canonical maps appearing
in this node; they do not choose normalization data from an existence theorem.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace SplitNodeNormalization

/-- The product of the component fraction fields, Stacks Tag 035P (2)
(blueprint: lem-sfb-split-node-normalization-conductor). -/
abbrev Fractions (T : Type u) [CommRing T] {t : ℕ} (p : Fin t → PrimeSpectrum T) :=
  ∀ i, FractionRing (T ⧸ (p i).asIdeal)

/-- The product of the component integral closures, Stacks Tag 035P (3)
(blueprint: lem-sfb-split-node-normalization-conductor). -/
abbrev Components (T : Type u) [CommRing T] {t : ℕ} (p : Fin t → PrimeSpectrum T) :=
  ∀ i, integralClosure (T ⧸ (p i).asIdeal) (FractionRing (T ⧸ (p i).asIdeal))

/-- The quotient-and-inclusion structural homomorphism, Stacks Tag 035P (3), (4)
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def componentMap (T : Type u) [CommRing T] {t : ℕ}
    (p : Fin t → PrimeSpectrum T) : T →+* Components T p :=
  RingHom.pi (fun i ↦
    (algebraMap (T ⧸ (p i).asIdeal)
      (integralClosure (T ⧸ (p i).asIdeal) (FractionRing (T ⧸ (p i).asIdeal)))).comp
        (Ideal.Quotient.mk (p i).asIdeal))

/-- The actual inclusion in the product of fraction fields, Stacks Tag 035P (3)
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def inclusion (T : Type u) [CommRing T] {t : ℕ}
    (p : Fin t → PrimeSpectrum T) : Components T p →+* Fractions T p :=
  RingHom.pi (fun i ↦
    (integralClosure (T ⧸ (p i).asIdeal)
      (FractionRing (T ⧸ (p i).asIdeal))).val.toRingHom.comp (Pi.evalRingHom _ i))

/-- The diagonal map through the minimal-prime quotients, Stacks Tag 035P (2), (3)
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def fractionMap (T : Type u) [CommRing T] {t : ℕ}
    (p : Fin t → PrimeSpectrum T) : T →+* Fractions T p :=
  (inclusion T p).comp (componentMap T p)

/-- The split chart `R[u,v]/(uv)` from Stacks Tag 0CDD, with `u = X 0`, `v = X 1`
(blueprint: lem-sfb-split-node-normalization-conductor). -/
abbrev Node (R : Type u) [CommRing R] :=
  MvPolynomial (Fin 2) R ⧸
    Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) R) *
      MvPolynomial.X (1 : Fin 2)}

/-- The quotient map defining the split chart, Stacks Tag 0CDD
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def nodeQuotient (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →+* Node R :=
  Ideal.Quotient.mk _

/-- Evaluation on the two branches, Stacks Tag 0CDD, explicit split-chart calculation
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def branchEvaluation (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →+* Polynomial R × Polynomial R :=
  (MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ if i = 0 then Polynomial.X else 0)).prod
    (MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ if i = 1 then Polynomial.X else 0))

/-- Evaluation at the two branch origins, Stacks Tag 0CDD, conductor calculation
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def origins (R : Type u) [CommRing R] :
    Polynomial R × Polynomial R →+* R × R :=
  RingHom.prodMap (Polynomial.evalRingHom 0) (Polynomial.evalRingHom 0)

/-- The explicit pullback ring `E ×_(R × R) R`, with the diagonal map from `R`.
It is the equalizer subring in `E × R`, using Mathlib's `RingHom.eqLocus`.
Source: Stacks Tag 0CDD, agent conductor fibre-product calculation
(blueprint: lem-sfb-split-node-normalization-conductor). -/
noncomputable def conductorPullback (R : Type u) [CommRing R] :
    Subring ((Polynomial R × Polynomial R) × R) :=
  ((origins R).comp (RingHom.fst _ _)).eqLocus
    (((RingHom.id R).prod (RingHom.id R)).comp (RingHom.snd _ _))

end SplitNodeNormalization

open SplitNodeNormalization

/-- Affine componentwise normalization, its integral-closure description, and compatibility
with every principal open, including `D(0)` and `D(1)`. The localization map in the last
clause is the actual localization of the inclusion in the product of fraction fields.
The empty product is Mathlib's product over `Fin 0`, hence the zero ring.

Source: Stacks Project, Morphisms, Tags 035P and 0CDV
(blueprint: lem-sfb-split-node-normalization-conductor).

Proof:
1. Spec T is locally Noetherian (pqf-def-locnoeth), and its quasi-compact opens have
   finitely many components (lem-weil-pbc-noetherian-finitely-many-components).
   Minimal primes identify the generic points
   (lem-weil-pbc-spec-irreducible-components-minimal-primes). Apply
   lem-sfb-normalization-generic-residue-affine-charts to obtain the integral-closure
   spectrum, with structural map the quotient-and-inclusion diagonal.
2. Project a monic equation to each quotient fraction field. Conversely lift the
   coefficients of a monic equation for each coordinate to T and multiply the finitely
   many lifted monic polynomials. At each coordinate one factor vanishes. This gives
   exactly the product of the individual integral closures (def-weil-pbc-integral-closure).
   For no factors the ambient ring is zero and the polynomial Z suffices.
3. On D(s), factors on which s is zero disappear and all other fraction fields stay
   unchanged. Apply lem-weil-pbc-integral-closure-commutes-localization to identify the
   closure with the localization of the product closure, with restriction b ↦ b/1.
   The affine-chart restriction in lem-sfb-normalization-generic-residue-affine-charts
   gives the commuting square of spectra. No finiteness of normalization is assumed.
-/
theorem splitNode_affine_normalization
    (T : Type u) [CommRing T] [_root_.IsReduced T] [IsNoetherianRing T]
    (t : ℕ) (p : Fin t → PrimeSpectrum T)
    (_hp : Function.Injective p)
    (_hmin : Set.range (fun i ↦ (p i).asIdeal) = minimalPrimes T) :
    (∀ x : Fractions T p,
      (fractionMap T p).IsIntegralElem x ↔
        ∀ i, x i ∈ integralClosure (T ⧸ (p i).asIdeal)
          (FractionRing (T ⧸ (p i).asIdeal))) ∧
    ∃ e : (Spec (.of T)).reducedNormalization ≅ Spec (.of (Components T p)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (componentMap T p)) =
        (Spec (.of T)).fromReducedNormalization ∧
      ∀ s : T,
        (∃ es : ((Spec (.of T)).fromReducedNormalization ⁻¹ᵁ
              PrimeSpectrum.basicOpen s).toScheme ≅
            Spec (.of (Localization.Away (componentMap T p s))),
          es.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (Components T p)
              (Localization.Away (componentMap T p s)))) =
            ((Spec (.of T)).fromReducedNormalization ⁻¹ᵁ
              PrimeSpectrum.basicOpen s).ι ≫ e.hom) ∧
        Function.Injective (Localization.awayMap (inclusion T p) (componentMap T p s)) ∧
        (∀ z : Localization.Away (fractionMap T p s),
          (Localization.awayMap (fractionMap T p) s).IsIntegralElem z ↔
            z ∈ Set.range (Localization.awayMap (inclusion T p) (componentMap T p s))) := by
  sorry

/-- For a normal domain the structural normalization map is the identity under its
canonical identification with the original affine scheme.
Source: Stacks Project, Morphisms, Tag 035P and the normal-domain case of Tag 0CDV
(blueprint: lem-sfb-split-node-normalization-conductor).
Proof: the unique minimal prime is zero and the integral closure of T in its fraction
field is T. The affine description in the first three steps of this node therefore
identifies the structural map with the identity. -/
theorem splitNode_normal_domain_identity
    (T : Type u) [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T] :
    ∃ e : (Spec (.of T)).reducedNormalization ≅ Spec (.of T),
      e.hom = (Spec (.of T)).fromReducedNormalization := by
  sorry

/-- All assertions for the explicit split node, with every canonical map characterized
on the polynomial presentation. Both branches are copies of `Spec R[X]`; their origins
are the two copies of the zero section `Spec R → Spec R[X]`. Smoothness of an origin
means smoothness over R, not smoothness of its closed immersion into its branch.

Source: Stacks Project, Models, Tag 0CDD, explicit split model; the conductor and pullback
formulas are the agent polynomial calculation recorded in the DAG
(blueprint: lem-sfb-split-node-normalization-conductor).

Proof:
4. Evaluate h at (u,0) and (0,v). The kernel consists of mixed monomials, hence is (uv).
   The image consists of equal-constant pairs: the inverse sends (f,g) to f(u)+g(v)-c.
5. Set e=(1,0). For b=(f,g), put d=f(0)-g(0) and q=(f-d,g). Then b=q+de, so 1,e
   generate the module and E=Q[e]. The equation (Z-q)^2-d(Z-q) proves integrality.
6. Fields and DVRs are PIDs (def-sc-discrete-valuation-ring), hence normal Noetherian
   domains (lem-weil-pbc-pid-noetherian-normal). Their polynomial rings are normal
   (lem-weil-pbc-polynomial-ring-normal-domain). The two minimal primes of Q are (u)
   and (v), since every prime contains one of u,v and both quotients are domains.
   Apply the component description (lem-weil-pbc-spec-irreducible-components-minimal-primes),
   def-sc-normalization, def-weil-pbc-reduced-normalization and
   lem-weil-pbc-finite-affine-coproduct-spectrum to identify Spec E as the normalization.
7. Multiplication by e forces the common constant of a conductor element to vanish.
   Conversely zero constants stay zero after multiplication by any element of E.
   Thus I=uR[u]×vR[v]=(u,v); write (uf,vg)=u(f,f(0))+v(g(0),g). This is already an
   E-ideal, so IE=I. Evaluation gives Q/I=R and E/IE=R×R, with diagonal induced map.
8. A pullback element ((f,g),r) has f(0)=r=g(0). The inverse is f(u)+g(v)-r modulo uv.
   Evaluation and the kernel computation show both composites are identities.
9. The branches and origins are affine spaces of dimensions one and zero
   (def-sbc-affine-space). Apply sbc-lem-affine-space-smooth to each.
-/
theorem splitNode_normalization_conductor
    (R : Type u) [CommRing R] [IsDomain R]
    (_hR : IsField R ∨ IsDiscreteValuationRing R) :
    ∃ (j : Node R →+* Polynomial R × Polynomial R) (ε : Node R →+* R),
      j.comp (nodeQuotient R) = branchEvaluation R ∧
      ε.comp (nodeQuotient R) = MvPolynomial.eval₂Hom (RingHom.id R) (fun _ ↦ 0) ∧
      Function.Injective j ∧
      (∀ b : Polynomial R × Polynomial R,
        b ∈ j.range ↔ (origins R b).1 = (origins R b).2) ∧
      (∃ e : (Spec (.of (Node R))).reducedNormalization ≅
          Spec (.of (Polynomial R × Polynomial R)),
        e.hom ≫ Spec.map (CommRingCat.ofHom j) = (Spec (.of (Node R))).fromReducedNormalization) ∧
      j.Finite ∧
      (∀ b : Polynomial R × Polynomial R,
        ∃ f : Polynomial (Node R), Polynomial.eval₂ j (1, 0) f = b) ∧
      ∃ I : Ideal (Node R),
        (∀ a : Node R, a ∈ I ↔
          ∀ b : Polynomial R × Polynomial R, j a * b ∈ j.range) ∧
        I = Ideal.span {nodeQuotient R (MvPolynomial.X 0),
          nodeQuotient R (MvPolynomial.X 1)} ∧
        Set.image j (I : Set (Node R)) =
          (((Ideal.span {(Polynomial.X : Polynomial R)}).prod
            (Ideal.span {(Polynomial.X : Polynomial R)}) : Ideal (Polynomial R × Polynomial R)) :
              Set (Polynomial R × Polynomial R)) ∧
        I.map j = (Ideal.span {Polynomial.X}).prod (Ideal.span {Polynomial.X}) ∧
        (∃ q : (Node R ⧸ I) ≃+* R,
          ∀ a : Node R, q (Ideal.Quotient.mk I a) = ε a) ∧
        (∃ q : ((Polynomial R × Polynomial R) ⧸ I.map j) ≃+* R × R,
          ∀ b : Polynomial R × Polynomial R, q (Ideal.Quotient.mk (I.map j) b) = origins R b) ∧
        (∃ q : Node R ≃+* conductorPullback R,
          ∀ a : Node R, (q a).val = (j a, ε a)) ∧
        Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
        Smooth (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0 : Polynomial R →+* R)) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
  sorry

end AlgebraicGeometry
