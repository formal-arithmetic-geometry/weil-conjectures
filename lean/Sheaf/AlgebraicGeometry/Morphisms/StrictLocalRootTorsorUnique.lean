module

public import Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

@[expose] public section
universe u
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- Field valued points of the punctured root algebra differ by a unique rotation.

Source: Stacks Project, Tags 0EYG and 09EV.
Proof: lift all simple roots of X^n-1 by strict henselianity; compare the
images of the root under the two maps and use the unique lifted ratio.
(blueprint: lem-sbc-strict-local-root-torsor-unique) -/
theorem strict_local_root_torsor_unique
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [IsRegularLocalRing H] (h : H)
    [IsRegularLocalRing (H ⧸ Ideal.span {h})]
    (hh : IsSMulRegular H h) (hhm : h ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
    ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C h) ≠ 0 →
      ∃! ζ : rootsOfUnity n H,
        a.comp (rootRotation H h n ζ).toRingHom = b := by sorry

end AlgebraicGeometry.Scheme
