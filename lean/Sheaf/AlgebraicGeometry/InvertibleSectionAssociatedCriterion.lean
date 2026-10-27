module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.AssociatedPoints
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Sheaf.RingTheory.AssociatedLocalizationFg
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Associated-point criterion for a regular section of an invertible sheaf

Source: Stacks Project, Divisors, Tag 0AYL, lemma-regular-section-associated-points,
and Tag 01WZ, lemma-regular-section-structure-sheaf
(blueprint: lem-sfb-invertible-section-associated-criterion).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A section of an invertible module on a locally Noetherian scheme is nonzero in the
fibres at all associated points if and only if multiplication by its coefficient in
any affine frame is injective. Here `e` is a trivialization over `U`, and
`sectionsLinearEquivOfOverIsoUnit e le_rfl` takes the coefficient relative to the frame
`e⁻¹(1)`. Nonvanishing means precisely that the germ is outside `𝔪ₓ Lₓ`, or equivalently
that its image in `Lₓ / 𝔪ₓ Lₓ` is nonzero. The right side is the regular-section condition.

Source: Stacks Project, Divisors, Tags 0AYL and 01WZ
(blueprint: lem-sfb-invertible-section-associated-criterion).

Proof:
1. On an affine frame `U = Spec A`, write `s = a e`. Local Noetherianity makes `A`
   Noetherian (pqf-lem-affine-open-locnoeth). The affine stalk-localization theorem
   (lem-weil-pbc-affine-open-stalk-localization) identifies the germ with `a/1` in `Aₚ`;
   its maximal ideal is `p Aₚ` (def-weil-pbc-localization-at-prime).
2. The point is associated exactly when `p = Ann(z)` for some `z : A`.
   For descent from the stalk use lem-sc-associated-localization-fg, since `p` is
   finitely generated (def-weil-pbc-noetherian-ring). Conversely, localize `z`:
   `(r/t)(z/1) = 0` iff some `v ∉ p` has `vrz = 0`, iff `r ∈ p`.
   Thus its annihilator is the maximal ideal, as in def-sc-associated-points.
3. The frame identifies the fibre with `(Aₚ / p Aₚ)eₓ`, using
   def-sc-invertible-module and def-weil-residue-field. Its section value is nonzero
   exactly when `a ∉ p`: then `a/1` is a unit, while `a ∈ p` gives zero.
4. If the section is nonvanishing at associated points, `a` avoids every associated
   prime. By lem-weil-pbc-noetherian-zerodivisors-union-associated-primes it is a
   nonzerodivisor. Applying this to `a(b-c) = 0` proves multiplication injective.
5. Conversely choose an affine frame around an associated point, using local
   invertibility and lem-weil-pbc-affine-opens-basis. Injectivity and the same
   zerodivisor criterion give `a ∉ p`, so the fibre value is nonzero.
6. Multiplication in every affine frame is equivalent to injectivity of the sheaf
   map `𝒪_X → L`, `b ↦ bs`: kernels are sectionwise
   (def-weil-sheaf-of-modules-category), and a kernel section vanishes on an affine
   trivializing cover, hence vanishes by sheaf uniqueness. For the empty scheme
   there are no associated points and the only section ring is zero, so both
   conditions hold. No finite cover or global frame is needed. -/
theorem nonvanishing_associatedPoints_iff_affine_mul_injective
    {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤)) :
    (∀ x : X, x ∈ AlgebraicGeometry.associatedPoints X → x ∈ nonvanishingLocus L s) ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)),
          Function.Injective (fun b : Γ(X, U) ↦
            sectionsLinearEquivOfOverIsoUnit e le_rfl
              (L.presheaf.map (homOfLE le_top).op s) * b) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
