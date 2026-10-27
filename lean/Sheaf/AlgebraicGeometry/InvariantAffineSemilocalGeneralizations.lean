/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.Topology.Inseparable
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Invariant affine semilocal generalizations

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1, reduction 6,
printed p. 5-21, and Lemma 4.3, printed p. 5-17; Stacks Tags 00E3 and 00DS.
(blueprint: lem-sfb-finite-datum-semilocal-generalizations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite invariant set contained in a quasi-affine open has an invariant affine
semilocal generalization subscheme. Equality of the two pullbacks as subfunctors is
expressed by the equivalence of their factorization conditions on every test scheme.
The transport map is the canonical `D.toHom` of the given descent datum.

Source: Raynaud, Theorem 4.1, reduction 6 (p. 5-21), and Lemma 4.3 (p. 5-17);
Stacks Tags 00E3 and 00DS.
(blueprint: lem-sfb-finite-datum-semilocal-generalizations).

Proof:
1. For empty E take Spec of the zero ring: the image and both pullbacks are empty,
   the morphism is quasi-compact, flat and monic, and there are no maximal ideals.
   This uses def-weil-affine-spectrum, def-weil-flat-morphism and def-pc-fibre-product.
2. Embed the given quasi-affine open in an affine scheme Spec C. Prime avoidance,
   lem-weil-pbc-prime-avoidance, finds an element of the ideal of its complement
   outside every prime of E. Its principal open is affine by clause (0) of
   lem-weil-pbc-affine-ideals-closed-subscheme, giving an affine open U = Spec A
   of Z containing E.
3. Localize A at the complement of the union of the primes representing E. By
   lem-weil-pbc-localization-spectrum-embedding its spectrum has image the primes
   disjoint from this multiplicative set. By lem-weil-pbc-prime-avoidance these
   are exactly the primes contained in one of the chosen primes, namely the
   generalizations of E. All such generalizations lie in U. Reflexivity and
   transitivity of specialization give containment of E and generalization stability.
4. Under the localization spectrum embedding, maximal ideals correspond to the
   inclusion-maximal members of the finite family of primes representing E.
   Thus the localized ring has finitely many maximal ideals; comparable or
   nonclosed points cause no problem.
5. The localization map is flat and monic by
   lem-sfb-localization-spectrum-flat-monomorphism. Composing with the open immersion
   U into Z preserves both properties (def-weil-open-immersion, def-weil-flat-morphism).
   Its source is quasi-compact by lem-weil-pbc-affine-scheme-qcqs, and Z is
   quasi-separated by lem-weil-pbc-locally-noetherian-quasi-separated. Hence the
   map is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence(1).
6. Both relation maps are finite: the first by
   lem-weil-pbc-finite-morphism-permanence(a), the second by the isomorphism of the
   two pullbacks encoded by def-pd-descent-datum. They are closed by
   lem-weil-pbc-finite-closed-map-finite-fibres. Continuity and specialization lifting
   (lem-trf-closed-map-specializing) identify the preimage of Gen(E) under either
   map with the generalizations of its preimage of E. Invariance of E therefore
   gives equality of these images. This uses closedness, without flatness of q.
7. Pulling j back along either relation map gives a quasi-compact flat monomorphism
   (def-pc-fibre-product, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence(3)). Its image is the corresponding preimage
   by lem-weil-pbc-base-change-image. The two images agree by step 6. By
   lem-sfb-qc-flat-monomorphism-ringed-image the two pullbacks represent the same
   subfunctor: a test map factors through either precisely when its image lies
   in this common image. The fibre-product universal property gives the displayed
   equivalence of factorizations through j.
-/
theorem exists_invariant_affine_semilocal_generalizations
    {Q S Z : Scheme.{u}} [IsAffine Q] [IsAffine S]
    (q : Q ⟶ S) [IsFinite q] [Surjective q] (z : Z ⟶ Q)
    [IsNoetherian Z]
    (D : Over.DescentDatum q (Over.mk z)) (E : Set Z) (hE : E.Finite)
    (hInvariant : (pullback.fst (z ≫ q) q) ⁻¹' E = D.toHom ⁻¹' E)
    (hQuasiAffine : ∃ W : Z.Opens, E ⊆ (W : Set Z) ∧
      ∃ (A : Scheme.{u}) (i : W.toScheme ⟶ A),
        IsAffine A ∧ IsOpenImmersion i ∧ QuasiCompact i) :
    ∃ (L : Scheme.{u}) (j : L ⟶ Z),
      IsAffine L ∧ QuasiCompact j ∧ Flat j ∧ Mono j ∧
      Set.range j = {x : Z | ∃ e ∈ E, x ⤳ e} ∧
      (∀ (T : Scheme.{u}) (a : T ⟶ pullback (z ≫ q) q),
        (∃ b : T ⟶ L, b ≫ j = a ≫ pullback.fst (z ≫ q) q) ↔
        (∃ b : T ⟶ L, b ≫ j = a ≫ D.toHom)) ∧
      E ⊆ Set.range j ∧ StableUnderGeneralization (Set.range j) ∧
      Finite (MaximalSpectrum Γ(L, ⊤)) := by
  sorry

end AlgebraicGeometry
