/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicUniverseLift

/-!
# Adic formal smoothness along a ring isomorphism of the base

If `S` is formally smooth over `R` for the `n`-adic topology and `R' ≃+* R`, then `S` is
formally smooth over `R'` for the induced algebra structure.

## Implementation details

A test algebra `D` over `R'` is regarded as an `R`-algebra through the inverse isomorphism, and
the lift is obtained from `Algebra.formallySmoothAdic_lift_universe`, so the test algebra may
live in any universe.

## References

* [Stacks, Tag 07NR]
* [Stacks, Tag 07NS]
-/

@[expose] public section

universe u u' v

namespace Algebra

/-- Adic formal smoothness is invariant under a ring isomorphism of the base: if `S` is
formally smooth over `R` for the `n`-adic topology and `e : R' ≃+* R`, then `S` is formally
smooth over `R'`, with the algebra structure induced by `e`. -/
theorem FormallySmoothAdic.of_ringEquiv
    {R : Type u} {R' : Type u'} {S : Type v}
    [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R S] (e : R' ≃+* R) (n : Ideal S)
    (h : FormallySmoothAdic R S n) :
    letI : Algebra R' S := ((algebraMap R S).comp e.toRingHom).toAlgebra
    FormallySmoothAdic R' S n := by
  let : Algebra R' S := ((algebraMap R S).comp e.toRingHom).toAlgebra
  intro D _ _ J hJ g hg
  let : Algebra R D := ((algebraMap R' D).comp e.symm.toRingHom).toAlgebra
  let gR : S →ₐ[R] D ⧸ J :=
    { toRingHom := g.toRingHom
      commutes' := by
        intro r
        have hr := g.commutes (e.symm r)
        change g ((algebraMap R S) (e (e.symm r))) =
          Ideal.Quotient.mk J ((algebraMap R' D) (e.symm r)) at hr
        change g ((algebraMap R S) r) =
          Ideal.Quotient.mk J ((algebraMap R' D) (e.symm r))
        simpa only [RingEquiv.apply_symm_apply] using hr }
  obtain ⟨f, hf⟩ := formallySmoothAdic_lift_universe R S n h D J hJ gR hg
  let f' : S →ₐ[R'] D :=
    { toRingHom := f.toRingHom
      commutes' := by
        intro r'
        have hr := f.commutes (e r')
        change f ((algebraMap R S) (e r')) =
          (algebraMap R' D) (e.symm (e r')) at hr
        change f ((algebraMap R S) (e r')) = (algebraMap R' D) r'
        simpa only [RingEquiv.symm_apply_apply] using hr }
  refine ⟨f', ?_⟩
  ext x
  exact DFunLike.congr_fun hf x

end Algebra
