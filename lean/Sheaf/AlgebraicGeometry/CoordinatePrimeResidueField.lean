module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The residue field of a coordinate prime of localized affine space

Source: Stacks Project, Algebra, Tag 0520, and More on Morphisms, Tag 052E,
first proof paragraph.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

/-- The residue field of the coordinate prime with its first `r` coordinates free.
Source: Stacks Project, Algebra, Tag 0520, and More on Morphisms, Tag 052E,
first proof paragraph (blueprint: lem-trf-coordinate-prime-rational-residue-field).

Proof:
Write `C = R_f[x_1,...,x_n]`, `p` for the image of `t` in `Spec R`, and
`K = kappa_R(p)`. The localization map takes `f` to a unit, hence `f` is outside
`p`. The residue map `R -> K` therefore extends uniquely to `R_f -> K`.
Its kernel is `p R_f`: a fraction maps to zero precisely when its numerator
lies in `p`, since its denominator is nonzero in `K`.
Evaluate `C` into `L = Frac(K[u_1,...,u_r])`, taking `x_i` to `u_i` for
`i < r` and to zero otherwise. This is valid also for `r = 0` and `r = n`.
Its kernel is the displayed coordinate ideal. Indeed, quotient first by the
last variables, obtaining the polynomial ring in the first `r` variables,
then reduce its coefficients modulo `p R_f`. Equality in this polynomial ring
is coefficientwise, and its map into `L` is injective.
Every element outside the coordinate prime maps to a nonzero element of `L`,
so the residue-field universal property extends evaluation to a field map
`kappa_C(P) -> L`, which is injective. Its image is a subfield containing the
image of `R/p`, hence its fraction field `K`, and each `u_i`. Thus it contains
all polynomials and their nonzero inverses, and equals `L`. This gives an
isomorphism commuting with the map from `K`; uniqueness follows by checking
on `R` and the residue-field universal property. Finally use `AffineSpace.SpecIso`
and the affine residue-field identifications. Naturality identifies the
structural map on residue fields with the constants map used above, so the
isomorphism commutes with the actual scheme residue-field map in the conclusion.
-/
theorem coordinatePrimeAffineSpace_residueField
    {R : Type u} [CommRing R] (f : R) (n r : ℕ) (hrn : r ≤ n)
    (t : AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f)))) :
    let π :=
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))) ↘
        Spec (.of (Localization.Away f))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
    ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of (Localization.Away f))).hom t).asIdeal =
        (π t).asIdeal.map (MvPolynomial.C.comp (algebraMap R (Localization.Away f))) ⊔
          Ideal.span {x | ∃ i : ULift.{u} (Fin n), r ≤ i.down.val ∧ x = MvPolynomial.X i} →
      ∃ e : (AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f)))).residueField t ≃+*
          FractionRing (MvPolynomial (Fin r) ((Spec (.of R)).residueField (π t))),
        ∀ a : (Spec (.of R)).residueField (π t),
          e ((π.residueFieldMap t).hom a) = algebraMap _ _ a := by sorry

end AlgebraicGeometry
