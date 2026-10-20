module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Noetherianity of the canonical strict henselization over a regular affine ring.
Source: Stacks Project, Tag 06LJ, applied to the local ring at the geometric point.
The proof identifies the coordinate-ring colimit with the ring strict henselization.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-noetherian)
-/
theorem strictHenselizationRing_noetherian_of_regular
    (R : CommRingCat.{u}) [IsRegularRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    IsNoetherianRing (strictHenselizationRing barY) := by
  let e : (R ⧸ Ideal.span ({0} : Set R)) ≃+* R := by
    rw [Ideal.span_singleton_zero]
    exact RingEquiv.quotientBot R
  letI : IsRegularRing (R ⧸ Ideal.span ({0} : Set R)) :=
    IsRegularRing.of_ringEquiv e.symm
  obtain ⟨hlocal, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  letI : IsLocalRing (strictHenselizationRing barY) := hlocal
  have h := strictHenselizationRing_regular_divisor_quotient R 0 barY b hb (by
    intro hz
    have hz' : (0 : strictHenselizationRing barY) = 1 := by simpa using hz
    exact zero_ne_one hz')
  letI : IsRegularRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) := h.1
  have hn : IsNoetherianRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) := inferInstance
  have ez : (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) ≃+*
      strictHenselizationRing barY := by
    rw [show Ideal.span ({b.hom 0} : Set (strictHenselizationRing barY)) = ⊥ by
      simp]
    exact RingEquiv.quotientBot _
  exact isNoetherianRing_of_ringEquiv _ ez
end AlgebraicGeometry.Scheme
