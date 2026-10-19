/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootDomainEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootTorsorUnique
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # The connected torsor properties of a strict local root cover

Source: Stacks Project, Tag 0EYG, the strictly local root-algebra paragraph;
Tag 09EV, the roots of unity calculation.
(blueprint: lem-sbc-strict-local-root-torsor-properties)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The puncture of the regular root algebra is a connected etale rotation torsor.

Source: Stacks Project, Tag 0EYG, the paragraph forming A[x]/(x^e-f), and
Tag 09EV, roots of unity and the Kummer subextension calculation.
(blueprint: lem-sbc-strict-local-root-torsor-properties)

Proof: The positive exponent makes X^n-h monic. Its quotient is finite free,
and its closed fibre is k[X]/(X^n), which has exactly one prime. Finiteness
over the henselian local H therefore makes C local and strictly henselian.
The root t satisfies t^n=h; freeness and regularity of h show that t is a
nonzerodivisor. The root-quotient is H/(h). Apply the regularity-at-root lemma
to the maximal ideal, which contains t, and identify the localization of C
at this maximal ideal with C. Hence C is regular local, so is a domain.
On D(h) the root is a unit. The derivative n*t^(n-1) is a unit too, so the
monic presentation is etale there; the open immersion D(h) into Spec H is
also etale. Hensel lifting the n simple roots of X^n-1 in the separably closed
residue field gives n roots in H. Their pairwise differences are units:
their residues are distinct. Their reductions, and hence their images under
any map H to a field, exhaust the n roots of unity. Given a,b as in the
statement, their root images are nonzero and their ratio is an n-th root of
unity. It is the image of exactly one root zeta in H. Polynomial evaluation
then gives a composed with rootRotation(zeta) equal to b; equality is checked
on H and the root. Conversely that equality determines the ratio and zeta,
proving uniqueness. The case n=1 is C=H and the identity rotation; h=0 and
h a unit are excluded by regularity and maximal-ideal membership. This lemma
has no finite etale cover Y and performs no orbit descent. -/
theorem strict_local_root_torsor_properties
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [IsRegularLocalRing H] (h : H)
    [IsRegularLocalRing (H ⧸ Ideal.span {h})]
    (hh : IsSMulRegular H h) (hhm : h ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen (algebraMap H C h)
    IsDomain C ∧ Etale (V.ι ≫ q) ∧
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
        a.comp (algebraMap H C) = b.comp (algebraMap H C) →
        a (algebraMap H C h) ≠ 0 →
        ∃! ζ : rootsOfUnity n H, a.comp (rootRotation H h n ζ).toRingHom = b) := by
  dsimp only
  obtain ⟨hdom, het⟩ := strict_local_root_domain_etale H h hh hhm n hn
  have huniq := strict_local_root_torsor_unique H h hh hhm n hn
  exact ⟨hdom, het, huniq⟩

end AlgebraicGeometry.Scheme
