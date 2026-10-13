module

public import Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import Sheaf.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The root algebra is a domain and its puncture is etale.

Source: Stacks Project, Tags 0EYG and 09EV.
Proof: apply the regularity-at-root lemma at the unique prime over the root,
then use the standard etale criterion for the monic polynomial on the basic open.
(blueprint: lem-sbc-strict-local-root-domain-etale) -/
theorem strict_local_root_domain_etale
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [IsRegularLocalRing H] (h : H)
    [IsRegularLocalRing (H ⧸ Ideal.span {h})]
    (hh : IsSMulRegular H h) (hhm : h ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen (algebraMap H C h)
    IsDomain C ∧ Etale (V.ι ≫ q) := by sorry

end AlgebraicGeometry.Scheme
