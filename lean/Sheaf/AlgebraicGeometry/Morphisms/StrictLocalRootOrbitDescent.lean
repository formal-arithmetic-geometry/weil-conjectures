/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.RingTheory.Henselian

import Sheaf.RingTheory.RootAlgebraRegularAtRoot

/-! # Descent of a root-split cover to fixed subalgebras

Source: Stacks Project, Tag 0EYG, local and intermediate-field paragraphs; Tag 09EV, intermediate
subextensions.
(blueprint: lem-sbc-strict-local-root-orbit-descent)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Root-split covers descend to products of fixed subalgebras of the root algebra.

Source: Stacks Project, Tag 0EYG, strict local and normal-domain paragraphs.
(blueprint: lem-sbc-strict-local-root-orbit-descent)

Proof: Put h=iota(g), C=H[t]/(t^n-h), and U=D(h). The monic relation makes C
finite free over H. Its closed fibre has just one prime because h is in the
maximal ideal, so C is local and strictly henselian. The equation t^n=h and
regularity of h show that t is a nonzerodivisor. The quotient by t is H/(h),
which is regular local; hence C is regular local and a normal domain. Thus
D(h) in Spec C is connected. Hensel lift the n distinct residue roots of X^n-1;
they give a cyclic group mu_n(H) of order n acting by t to zeta*t. After
inverting h this is a connected finite etale torsor over U. Base change the
given splitting along iota, using associativity of pullbacks and compatibility
of the monic root algebra with base change. Its descent datum permutes the d
connected copies of the torsor. Partition Fin d into the finitely many orbits,
number them by Fin m and choose a representative in each. Let K(k) be its
stabilizer in mu_n(H). The descended component is the quotient of the torsor
by K(k). On affine rings its coordinate algebra is (C[1/h])^K(k). Localization
at the invariant element h commutes with invariants: a fixed fraction has a
fixed numerator since C is a domain and h is nonzero. Consequently this ring
is (C^K(k))[1/h]. The components together are the spectrum of the product of
these localized rings. Finite products commute with this localization, giving
exactly D(h) in Spec(product C^K(k)). The torsor descent and ring maps are over
H, so their composition satisfies the projection equation. If d=0, the orbit
set and product are empty and give the empty scheme. No claim identifying an
invariant algebra with another root algebra is made here. -/
theorem strict_local_root_orbit_descent
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    [IsStrictlyHenselianLocalRing H] [IsRegularLocalRing H]
    [IsRegularLocalRing (H ⧸ Ideal.span {ι g})]
    (hg : IsSMulRegular H (ι g)) (hgm : ι g ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j] (d : ℕ) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (m : ℕ) (K : Fin m → Subgroup (rootsOfUnity n H)),
        let B := ∀ k : Fin m, rootFixedAlgebra H (ι g) n (K k)
        let N := Spec (CommRingCat.of B)
        let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
        let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
        ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
          θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by sorry

end AlgebraicGeometry.Scheme
