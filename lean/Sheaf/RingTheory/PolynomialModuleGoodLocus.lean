module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The good locus of a polynomial module

Source: Stacks Project, Algebra, equation (equation-good-locus), and Tag 051Z,
polynomial-algebra case (blueprint: def-sfb-polynomial-module-good-locus).

The fraction module uses the image of the powers of `f` in the polynomial ring.
Its fractions are `m / C(f)^a`, with the same equality relation as `m / f^a`
in the localization of the underlying base module. The polynomial localization
instance supplies the canonical action; restriction to constant polynomials
supplies the base action. No choice of module structure is made.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPolynomial

/-- The canonical localized polynomial action, from Mathlib's polynomial localization instance.
On fractions it sends `p / C(f)^a` acting on `m / C(f)^b` to `p • m / C(f)^(a+b)`.
In particular, `X i` sends `m / f^a` to `(X i • m) / f^a`.

Source: Stacks Project, Algebra, equation (equation-good-locus), Tag 051Z, polynomial case
(blueprint: def-sfb-polynomial-module-good-locus). -/
noncomputable abbrev localizedPolynomialModule
    (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] (f : R) :
    Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule ((Submonoid.powers f).map (C (σ := Fin n))) M) :=
  @LocalizedModule.moduleOfIsLocalization (MvPolynomial (Fin n) R) _
    ((Submonoid.powers f).map (C (σ := Fin n))) M _ _
    (MvPolynomial (Fin n) (Localization.Away f)) _
    (algebraMvPolynomial (σ := Fin n) (R := R) (S := Localization.Away f))
    (isLocalization (σ := Fin n) (Submonoid.powers f) (Localization.Away f))

/-- The localized base action is restriction of the canonical polynomial action along constants.

Source: Stacks Project, Algebra, equation (equation-good-locus), Tag 051Z, polynomial case
(blueprint: def-sfb-polynomial-module-good-locus). -/
noncomputable abbrev localizedPolynomialBaseModule
    (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] (f : R) :
    Module (Localization.Away f)
      (LocalizedModule ((Submonoid.powers f).map (C (σ := Fin n))) M) :=
  letI := localizedPolynomialModule R n M f
  Module.compHom _
    (algebraMap (Localization.Away f) (MvPolynomial (Fin n) (Localization.Away f)))

/-- The union of the principal opens where the localized module is free over the base
and finitely presented over the localized polynomial ring. No finiteness or reducedness
assumption is needed to define the locus. Freeness permits an arbitrary or empty basis.

Source: Stacks Project, Algebra, equation (equation-good-locus), Tag 051Z, polynomial case
(blueprint: def-sfb-polynomial-module-good-locus). -/
noncomputable def polynomialModuleGoodLocus
    (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] : Set (PrimeSpectrum R) :=
  {p | ∃ f : R, f ∉ p.asIdeal ∧
    @Module.Free (Localization.Away f)
      (LocalizedModule ((Submonoid.powers f).map (C (σ := Fin n))) M) _ _
      (localizedPolynomialBaseModule R n M f) ∧
    @Module.FinitePresentation (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule ((Submonoid.powers f).map (C (σ := Fin n))) M) _ _
      (localizedPolynomialModule R n M f)}

end MvPolynomial
