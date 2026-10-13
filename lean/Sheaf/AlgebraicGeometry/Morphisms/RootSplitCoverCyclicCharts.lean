/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-!
# Cyclic orbit charts for a cover split by a root extension

Source: Stacks Project, Tag 0EYG, final paragraph on intermediate root extensions,
and finite etale descent (Tags 02LA and 02VN).
(blueprint: lem-sbc-root-split-cover-cyclic-charts)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Covers split by a single root extension are locally unions of intermediate root covers.

Source: Stacks Project, Tag 0EYG, final paragraph; Tags 02LA and 02VN,
descent of finite and etale morphisms.
(blueprint: lem-sbc-root-split-cover-cyclic-charts)

Proof: The positive unit n makes the punctured n-th root cover finite etale and
faithfully flat over D(g). The factorization j and the displayed splitting descend
finiteness and etaleness to j by faithfully flat descent. Work first at a point of
V(g), after strict henselization. The divisor quotient is regular local, hence a domain;
the base is regular local, hence a normal domain, and g is a prime element. The n-th
root ring is regular local (its root quotient is the divisor ring), hence a normal
domain. Hensel's lemma lifts all n-th roots of unity from the separably closed residue
field, giving the cyclic action of order n on the punctured root cover. This cover is
connected and is a cyclic torsor. Its self-pullback is a union of n copies of this
connected cover. Under delta each descent automorphism is therefore a constant
permutation of Fin d on each copy; the cocycle identity gives a cyclic group action.
Thus the given finite etale cover is the descent of that finite cyclic set. Decompose it
set into orbits. An orbit of length e has e dividing n; the subgroup of order n/e fixes
exactly the intermediate root algebra with root t^(n/e), whose e-th power is g.
This can be checked on the fraction field and then on the normal finite etale algebras;
normality gives the equality with the integral closure. Thus the orbit cover is the
punctured e-th root cover, with e positive and a unit. Enumerate the finitely many orbits
by Fin m. The isomorphisms, their inverses, the equation and their projection identities
are finite presentation data, so descend from the strict henselization to an affine
pointed etale neighborhood using 0BSK and 05N9; shrink until all e are units.
Regularity of the base and divisor and regularity of the equation are preserved by
etale base change. Spec of a finite product is the disjoint union of the spectra;
restriction to the common basic open identifies the union of punctured root covers
with the displayed V. All isomorphisms are over the new base, giving the equality.
Off V(g), the descended cover is finite etale and splits on a pointed etale neighborhood;
use h = 1 and e = 1. The zero quotient is regular. For an empty cover use m = 0;
the finite product is the zero ring and its spectrum is empty. No torsor action on Y,
Galois hypothesis, ramification bound or ambient morphism is needed for this step. -/
theorem root_split_cover_cyclic_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    [IsRegularRing R] (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      ∃ (m : ℕ) (h : S) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S h ∧
        IsRegularRing (S ⧸ Ideal.span {h}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)) h)
        ∃ γ : pullback p ψ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p ψ := by sorry

end AlgebraicGeometry.Scheme
