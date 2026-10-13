/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Cyclic orbits on root-split strict local covers

Source: Stacks Project, Tag 0EYG, local and intermediate-field paragraphs; Tag 09EV, intermediate
subextensions.
(blueprint: lem-sbc-root-split-strict-local-orbits)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Over a fixed regular strictly henselian local base, root-split finite etale
covers of a regular principal puncture decompose into intermediate root covers.

Source: Stacks Project, Tag 0EYG, local and intermediate-field paragraphs,
and Tag 09EV for intermediate subextensions.
(blueprint: lem-sbc-root-split-strict-local-orbits)

Proof: Base change j and its supplied splitting along iota. Put h=iota(g).
The root algebra C=H[t]/(t^n-h) is finite free over H. Its closed fibre has
one prime, since h is in the maximal ideal; it is therefore local and strictly
henselian. Multiplication by t is injective because t^n=h is regular, and
C/(t)=H/(h) is regular local. Thus C is regular local and a normal domain.
The puncture C[1/t] is connected. Hensel lift the distinct residue roots of
X^n-1. They give a cyclic group of n roots of unity acting by t to zeta*t;
the punctured root cover is its connected torsor over H[1/h]. Pullback
associativity and compatibility of Spec with the root-algebra base change
transport the supplied splitting to this torsor. Descent data on its d
connected copies are a permutation action on Fin d. Decompose it into
orbits of lengths e(k). Each length is positive and divides n, so is a
unit in H. For an orbit of length e the stabilizer fixes t^(n/e). Eisenstein
at the prime (h) and the cyclic intermediate-field calculation identify
its fraction field with the extension defined by s^e=h. The latter root
algebra is again regular local, and its localization at h is normal.
It and the orbit cover are the same integral closure of H[1/h] in that
field. Their isomorphism respects H[1/h]. Assemble the finitely many
components using the product of root algebras, and restrict to D(h).
The resulting isomorphism over H gives the stated projection equation.
Edge cases: d=0 has no orbits and m=0, so both schemes are empty. For n=1
all nonempty orbits have length one. The regular local hypotheses make
H and H/(h) nonzero domains, so the puncture is nonempty. -/
theorem root_split_strict_local_orbits
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
    ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ e k ∣ n) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap H (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap H (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))) (ι g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by sorry

end AlgebraicGeometry.Scheme
