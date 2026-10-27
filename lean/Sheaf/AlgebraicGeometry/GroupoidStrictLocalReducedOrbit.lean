/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations

/-! # Reduced closed orbits over strictly henselian invariants

Source: Stacks Project, Groupoids, Tag 0DT9, first part of the strictly henselian claim;
Tags 03BJ, 03BL, 00GA and 00DT
(blueprint: lem-sfb-groupoid-strict-local-reduced-orbit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The selected closed orbits correspond, including residue fields and reduced rings.
Source: Stacks Project, `groupoids.tex`, Tag 0DT9, proof of the strictly henselian claim,
first part; finite Chinese remainder, Algebra Tag 00DT
(blueprint: lem-sfb-groupoid-strict-local-reduced-orbit).

`C,C'` are the specified equalizer subrings, and `φ` is their canonical map, determined
by its composite with the inclusion. `Z,Z'` are the indicated fibres on ordinary points.
These equality binders name constructions without choosing any extra structure.
The stabilizer square is its Yoneda universal property: a loop in `R` at `x ≫ a`
has a unique loop lift in `R'` at `x`, for every test scheme, including nonreduced ones.
This is the cartesian square of scheme-theoretic stabilizers, not just of point sets.
The ring equivalence in the conclusion is prescribed on the quotient projections,
so it states that the induced map itself is an isomorphism.

Proof:
1. Source and target compatibility carry invariants to invariants. Apply
   lem-a1-affine-groupoid-integral-invariants to both groupoids and
   lem-a1-affine-groupoid-orbit-fibres to get nonempty single orbits `Z,Z'` and
   `a(Z') ⊆ Z`. Each orbit is the target image of a source fibre; these fibres are
   finite by lem-weil-pbc-finite-closed-map-finite-fibres and finite local freeness.
2. The residue field `k` of `C` is separably closed. By
   lem-a1-integral-residue-extension-algebraic and
   lem-sfb-algebraic-sepclosed-purely-insep, each residue field on `Z` is algebraic,
   separably closed and purely inseparable over `k`. Apply
   lem-exc-etale-lift-sepclosed-base to the canonical residue points over each `u'`:
   the resulting lift gives a two-sided inverse to the original residue field map.
3. Fix `u'` in `Z'`. For every `v` in `Z`, the orbit description supplies an arrow
   from `a(u')` to `v`. Its residue-field-valued point lifts through the cartesian
   source square, using step 2. The lifted target lies in `Z'` because source and
   target agree on `C'`. Hence the map of the selected orbits is surjective.
4. Join two primed orbit points over the same `u` by an arrow, using the orbit
   description. The two maps from the residue field of `u` to the arrow residue
   field agree on `k`, hence agree everywhere by pure inseparability (in positive
   characteristic compare suitable prime-power powers; in characteristic zero
   the extension is trivial). The arrow therefore maps to the scheme-theoretic
   stabilizer. The cartesian stabilizer square lifts it to a primed loop, and the
   cartesian source square identifies this lift with the original arrow. Its
   endpoints coincide. This proves injectivity.
5. Each quotient by an orbit prime contains `k` and embeds into an algebraic field
   extension of `k`. A nonzero element has an algebraic equation with nonzero
   constant coefficient, expressing its inverse as a polynomial. Thus these
   quotients are fields (the argument of Tag 00GA), so every orbit point is closed.
6. The primes containing `m A` are exactly `Z`, so
   lem-weil-pbc-zero-locus-eq-iff-radical-eq identifies its radical with the
   intersection of the orbit primes. Distinct maximal ideals are coprime. Apply
   lem-pc-crt-ideal-quotient-product to both finite sets, identifying the reduced
   rings with the products of their residue fields. On products the induced map
   has the residue maps as coordinates. Steps 2--4 make it an isomorphism, with
   inverse given by the inverse index bijection and inverse residue maps. -/
theorem groupoid_strictLocal_reducedOrbit
    (S : Scheme.{u}) (A B A' B' : CommRingCat.{u})
    (π : Spec A ⟶ S) (π' : Spec A' ⟶ S)
    (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
    (c : pullback s t ⟶ Spec B)
    (s' t' : Spec B' ⟶ Spec A') (e' : Spec A' ⟶ Spec B') (i' : Spec B' ⟶ Spec B')
    (c' : pullback s' t' ⟶ Spec B')
    (_hG : Scheme.IsGroupoid s t e i c) (_hG' : Scheme.IsGroupoid s' t' e' i' c')
    (_hS : s ≫ π = t ≫ π) (_hS' : s' ≫ π' = t' ≫ π')
    (a : Spec A' ⟶ Spec A) (b : Spec B' ⟶ Spec B) (_ha : a ≫ π = π')
    (_he : e' ≫ b = a ≫ e) (_hi : i' ≫ b = b ≫ i)
    (_hc : ∀ (H : Scheme.{u}) (p' : H ⟶ pullback s' t') (p : H ⟶ pullback s t),
      p' ≫ pullback.fst s' t' ≫ b = p ≫ pullback.fst s t →
      p' ≫ pullback.snd s' t' ≫ b = p ≫ pullback.snd s t → p' ≫ c' ≫ b = p ≫ c)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    [s'.IsFiniteLocallyFree] [t'.IsFiniteLocallyFree] [Etale a]
    (_hs : IsPullback b s' s a) (_ht : IsPullback b t' t a)
    (_hstab : ∀ (H : Scheme.{u}) (x : H ⟶ Spec A') (r : H ⟶ Spec B),
      r ≫ s = x ≫ a → r ≫ t = x ≫ a →
      ∃! r' : H ⟶ Spec B', r' ≫ b = r ∧ r' ≫ s' = x ∧ r' ≫ t' = x)
    (C : Subring A) (C' : Subring A')
    (_hC : C = (Spec.preimage s).hom.eqLocus (Spec.preimage t).hom)
    (_hC' : C' = (Spec.preimage s').hom.eqLocus (Spec.preimage t').hom)
    (φ : C →+* C') (_hφ : C'.subtype.comp φ = (Spec.preimage a).hom.comp C.subtype)
    [IsStrictlyHenselianLocalRing C] (p' : PrimeSpectrum C')
    (_hp' : PrimeSpectrum.comap φ p' = IsLocalRing.closedPoint C)
    (Z : Set (PrimeSpectrum A)) (Z' : Set (PrimeSpectrum A'))
    (_hZ : Z = {x | PrimeSpectrum.comap C.subtype x = IsLocalRing.closedPoint C})
    (_hZ' : Z' = {x | PrimeSpectrum.comap C'.subtype x = p'}) :
    Z.Nonempty ∧ Z.Finite ∧ (∀ x ∈ Z, IsClosed ({x} : Set (PrimeSpectrum A))) ∧
    Z'.Nonempty ∧ Z'.Finite ∧ (∀ x ∈ Z', IsClosed ({x} : Set (PrimeSpectrum A'))) ∧
    Set.BijOn a Z' Z ∧ (∀ x ∈ Z', IsIso (a.residueFieldMap x)) ∧
    ∃ ψ : (A ⧸ (Ideal.map C.subtype (IsLocalRing.maximalIdeal C)).radical) ≃+*
        (A' ⧸ ⨅ x : Z', x.val.asIdeal),
      ψ.toRingHom.comp
          (Ideal.Quotient.mk (Ideal.map C.subtype (IsLocalRing.maximalIdeal C)).radical) =
        (Ideal.Quotient.mk (⨅ x : Z', x.val.asIdeal)).comp (Spec.preimage a).hom := by
  sorry

end AlgebraicGeometry
