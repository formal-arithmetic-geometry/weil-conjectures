module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Topology.Sets.Closeds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.FiniteIntersectionEtaleStalkModel
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange

/-! # Regular component primes in an étale stalk

Source: Stacks Project, Algebra, Tags 07NF, 00NP and 05CK; Schemes, Tags 01J3,
00ES, 00E3 and 01I4; Morphisms, Tag 02GO; More on Algebra, Tag 0AH0
(blueprint: lem-trf-regular-component-etale-stalk-primes).

The component ideals are the actual kernel ideal sheaves evaluated at the stalk,
using the existing `HilbertSamuel.stalkIdeal` construction. Quotient and pullback
identifications commute with their structural maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Regular reduced components give distinct prime ideals in every étale stalk.
Source: Stacks Project, Tags 07NF, 0AH0, 00NP, 01J3, 00ES, 00E3, 01I4, 02GO and 05CK
(blueprint: lem-trf-regular-component-etale-stalk-primes).

Proof:
1. Choose a Noetherian affine neighbourhood of x. The open-subspace irreducible-closed
   order correspondence (lem-weil-pbc-open-subspace-irreducible-closed-correspondence)
   identifies the components meeting it. Apply lem-sfb-closed-component-stalk-calculus
   there: the component stalk ideals through x are exactly the distinct minimal primes
   over I, their quotients are the component stalks, and their intersection is I.
   A component missing x has unit stalk ideal; the empty intersection is the unit ideal.
2. Apply lem-trf-finite-intersection-etale-stalk-model to the singleton component.
   It identifies its pullback to Spec R with Spec(R/q_a), including the projection,
   and identifies R/q_a with the stalk of the component's étale pullback over w.
3. This pullback is étale over the component by lem-weil-pbc-etale-scheme-base-change.
   Its quotient stalk is regular local and its stalk map is faithfully flat by
   lem-sfb-etale-stalk-invariants and def-weil-regular-scheme. Apply
   lem-sc-regular-local-domain: R/q_a is a nonzero domain, so q_a is proper and prime.
4. Apply lem-weil-pbc-faithfully-flat-universally-injective to the module A/p_a over
   itself. Under its tensor identification with R/q_a, this is injectivity of
   A/p_a → R/q_a. Thus the contraction of q_a is p_a. Equal extended primes have
   equal contractions, and Step 1 then gives equal component indices.
5. For a prime Q of R containing IR, its contraction contains I. The finite product
   of the p_a is contained in their intersection I. Primality forces one p_a into
   the contraction of Q, equivalently q_a into Q. The converse follows from I ≤ p_a.
   With no components through x, I is the unit ideal, so both closed sets are empty.
6. A component missing x has unit stalk ideal. By the singleton affine tensor
   base-change formula (lem-sbc-finite-affine-tensor-base-change), its pullback ring
   is R modulo the extended unit ideal. Its spectrum is empty. The calculation on
   an affine neighbourhood computes the original pullback because Spec R factors
   through that neighbourhood.
-/
theorem regular_component_etale_stalk_primes
    {X D : Scheme.{u}} [IsLocallyNoetherian X] (d : D ⟶ X)
    [IsClosedImmersion d] [IsReduced D]
    {F : Type v} [Finite F] (C : F → Scheme.{u}) (k : (a : F) → C a ⟶ D)
    [∀ a : F, IsClosedImmersion (k a)] [∀ a : F, IsReduced (C a)]
    (hcomponents : Set.range (fun a : F ↦ Set.range (k a)) = irreducibleComponents D)
    (hdistinct : Function.Injective (fun a : F ↦ Set.range (k a)))
    (hregular : ∀ a : F, IsRegularScheme (C a))
    {W : Scheme.{u}} (f : W ⟶ X) [Etale f] (w : W)
    (I : Ideal (X.presheaf.stalk (f w))) (hI : I = HilbertSamuel.stalkIdeal d.ker (f w))
    (Fx : Set F) (hFx : Fx = {a : F | f w ∈ Set.range (k a ≫ d)})
    (p : F → Ideal (X.presheaf.stalk (f w)))
    (hp : ∀ a : F, p a = HilbertSamuel.stalkIdeal (k a ≫ d).ker (f w))
    (q : F → Ideal (W.presheaf.stalk w))
    (hq : ∀ a : F, q a = (p a).map (f.stalkMap w).hom) :
    Set.BijOn p Fx I.minimalPrimes ∧
    (∀ a ∈ Fx,
      (∀ (z : C a) (hz : (k a ≫ d) z = f w),
        ∃ e : (X.presheaf.stalk (f w) ⧸ p a) ≃+* (C a).presheaf.stalk z,
          ∀ b : X.presheaf.stalk (f w),
            e (Ideal.Quotient.mk (p a) b) = ((k a ≫ d).stalkMap z).hom
              ((X.presheaf.stalkCongr (.of_eq hz)).inv.hom b)) ∧
      (∃ e : pullback (k a ≫ d) (W.fromSpecStalk w ≫ f) ≅
          Spec (.of (W.presheaf.stalk w ⧸ q a)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (q a))) =
          pullback.snd (k a ≫ d) (W.fromSpecStalk w ≫ f)) ∧
      Nontrivial (W.presheaf.stalk w ⧸ q a) ∧
      IsRegularLocalRing (W.presheaf.stalk w ⧸ q a) ∧
      IsDomain (W.presheaf.stalk w ⧸ q a) ∧
      (q a).IsPrime ∧ q a ≠ ⊤ ∧
      (q a).comap (f.stalkMap w).hom = p a) ∧
    Set.InjOn q Fx ∧
    PrimeSpectrum.zeroLocus (I.map (f.stalkMap w).hom : Set (W.presheaf.stalk w)) =
      ⋃ a ∈ Fx, PrimeSpectrum.zeroLocus (q a : Set (W.presheaf.stalk w)) ∧
    (∀ a ∉ Fx, IsEmpty (pullback (k a ≫ d) (W.fromSpecStalk w ≫ f) : Scheme.{u})) := by
  sorry

end AlgebraicGeometry
