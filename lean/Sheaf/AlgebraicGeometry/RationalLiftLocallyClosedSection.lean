module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Rational lifts and sections on locally closed subschemes

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé II, Proposition 2.2.3,
printed p. 27 (blueprint: lem-per-rational-lift-locally-closed-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point has a lift with unchanged residue field if and only if the morphism has a
section on a locally closed subscheme containing that point.

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé II, Proposition 2.2.3,
printed p. 27 (blueprint: lem-per-rational-lift-locally-closed-section).

Proof:
1. Suppose `y` lies above `x` with residue-field isomorphism `r`. Compose the canonical
   point `Spec κ(y) → Y` with `Spec (r⁻¹)` to obtain `t : Spec κ(x) → Y` over `X`.
   This uses `lem-weil-pbc-morphism-from-spec-field` and
   `lem-weil-pbc-residue-field-point-naturality`. Choose affine neighborhoods
   `U = Spec A` of `x` and `V = Spec B` of `y`, mapping into `U`, with `B` a finite type
   `A`-algebra, by `def-weil-finite-type-morphism`. The point `t` factors through `V`
   by `def-weil-open-immersion`. By `def-weil-affine-spectrum` this gives maps
   `α : A → B` and `ψ : B → κ(x)` with `ψα` the residue map. Here the affine residue
   identification is `lem-weil-pbc-spec-residue-field-identification`.
2. Write `p` for the prime corresponding to `x` and put `R = A/p`. By
   `lem-weil-pbc-prime-residue-field-algebra`, `κ(x)` is the fraction field of the
   domain `R`. Write the images of finitely many algebra generators of `B` as fractions
   `uᵢ/vᵢ`, and let `d` be the product of their nonzero denominators, or `1` if there
   are no generators. Put `D = R[1/d]` using `def-weil-ring-localization-away`.
   The canonical map `ι : D → κ(x)` is injective, and its image contains every `ψ(bᵢ)`
   and the image of `A`. Hence it contains all of `ψ(B)`. Taking the inverse on this
   image gives a ring map `β : B → D` with `βα = λ`, the canonical map `A → D`.
   Injectivity of `ι` verifies both the ring laws and this equality.
3. Lift `d` to `a ∈ A`, so `a ∉ p`. The canonical map `A → D` factors through the
   surjection `q : A[1/a] → D`, sending `c/aᵉ` to its residue class divided by `dᵉ`.
   Factor `q` through the isomorphism `A[1/a]/ker q ≅ D`; then
   `lem-weil-pbc-spec-quotient-closed-immersion` gives a closed immersion
   `Spec D → Spec A[1/a]`. By `lem-weil-pbc-principal-localization-open-immersion`,
   `Spec A[1/a] → U → X` is an open immersion. Thus their composite
   `j : Z = Spec D → X` is an immersion by `def-weil-closed-immersion`.
4. Define `s : Z → Y` by `Spec β` followed by `V → Y`. Contravariant functoriality
   in `def-weil-affine-spectrum` and `βα = λ` give `s ≫ f = j`. Since `ιλ` is the
   residue map at `x`, `lem-weil-pbc-spec-residue-field-identification` identifies
   `Spec κ(x) → Z → X` with the canonical point of `x`. By
   `lem-weil-pbc-morphism-from-spec-field`, its image is `x`, so `x ∈ range j`.
5. Conversely choose `z` with `j(z) = x` and set `y = s(z)`. Then `f(y) = x`.
   Factor the immersion `j` as a closed immersion followed by an open immersion.
   By `lem-weil-pbc-closed-immersion-residue-field-iso` and
   `lem-weil-pbc-residue-field-point-naturality`, the induced map
   `c : κ(x) → κ(z)` is an isomorphism. The residue maps `a : κ(x) → κ(y)` and
   `b : κ(y) → κ(z)` satisfy `ba = c`. Thus `b' = c⁻¹b` is a left inverse to `a`.
   A unital field homomorphism is injective. Applying injectivity of `b'` to
   `b'(a(b'(v))) = b'(v)` shows `ab' = 1` as well. Hence `a` is an isomorphism.
   Neither direction uses quasi-compactness or separatedness of `Y` or `f`. -/
theorem rationalLift_iff_locallyClosed_section {X Y : Scheme.{u}} [IsNoetherian X]
    (f : Y ⟶ X) [LocallyOfFiniteType f] (x : X) :
    (∃ y : Y, f y = x ∧ IsIso (f.residueFieldMap y)) ↔
      ∃ (Z : Scheme.{u}) (j : Z ⟶ X),
        IsImmersion j ∧ x ∈ Set.range j ∧ ∃ s : Z ⟶ Y, s ≫ f = j := by
  sorry

end AlgebraicGeometry
