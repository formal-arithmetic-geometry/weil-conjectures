/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Rational lifts and sections on locally closed subschemes

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Proposition 2.2.3,
printed p. 27 (blueprint: lem-per-rational-lift-locally-closed-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point has a lift inducing a residue-field isomorphism through a locally finite type
morphism to a Noetherian scheme exactly when the morphism has a section over a locally
closed subscheme containing the point. No quasi-compactness or separation of the source
or morphism is required.
Source: ILO, Travaux de Gabber, Exposé II, Proposition 2.2.3, printed p. 27
(blueprint: lem-per-rational-lift-locally-closed-section).

Proof:
1. Given a lift `y` of `x` with residue-field isomorphism `r`, put `K = κ(x)`.
   Compose the canonical point `Spec κ(y) → Y` with `Spec(r⁻¹)` to obtain
   `t : Spec K → Y` over the canonical point of `x`
   (`lem-weil-pbc-morphism-from-spec-field`, `lem-weil-pbc-residue-field-point-naturality`).
   Choose affine opens `U = Spec A` about `x` and `V = Spec B` about `y` over `U`,
   with `B` finitely generated over `A` (`def-weil-finite-type-morphism`). The map `t`
   factors through `V` because its one-point source maps into that open
   (`def-weil-open-immersion`). For the prime `p` of `x`, this gives ring maps
   `α : A → B` and `ψ : B → κ(p)` with `ψα` the canonical residue map
   (`def-weil-affine-spectrum`, `lem-weil-pbc-spec-residue-field-identification`).
2. Put `R = A/p`. Its fraction field is `κ(p)`
   (`lem-weil-pbc-prime-residue-field-algebra`). Choose finitely many algebra generators
   of `B` and a common nonzero denominator `d` for their images in `κ(p)`; for no
   generators take `d = 1`. The injection `R[1/d] → κ(p)` identifies every generator
   image, and hence all of `ψ(B)`, with an element of `R[1/d]`
   (`def-weil-ring-localization-away`). Thus `ψ` factors through a ring map
   `β : B → R[1/d]`, with `βα = λ`, the canonical map `A → R[1/d]`.
3. Lift `d` to `a ∈ A`, with `a ∉ p`, and set `Z = Spec R[1/d]`.
   The map `A[1/a] → R[1/d]` is surjective: lift each numerator to `A`.
   Factoring this map through the quotient by its kernel gives a closed immersion
   `Z → Spec A[1/a]` (`lem-weil-pbc-spec-quotient-closed-immersion`,
   `def-weil-closed-immersion`). Compose it with the principal open immersion into `U`
   (`lem-weil-pbc-principal-localization-open-immersion`) and `U → X`
   (`def-weil-open-immersion`). The resulting `j : Z → X` is an immersion.
4. The map `Spec β` followed by `V → Y` defines `s`. The equality `βα = λ` gives
   `s ≫ f = j` (`def-weil-affine-spectrum`). The injection `R[1/d] → κ(p)` gives
   a point of `Z` over `x` (`lem-weil-pbc-spec-residue-field-identification`,
   `lem-weil-pbc-morphism-from-spec-field`), so `x` belongs to the image of `j`.
5. Conversely, choose `z` over `x` in such a `Z` and put `y = s(z)`.
   Factoring `j` into a closed and an open immersion shows that its residue-field
   map `c : κ(x) → κ(z)` is an isomorphism
   (`def-weil-closed-immersion`, `lem-weil-pbc-closed-immersion-residue-field-iso`,
   `lem-weil-pbc-residue-field-point-naturality`). The equality `s ≫ f = j` gives
   `ba = c`, where `a : κ(x) → κ(y)` and `b : κ(y) → κ(z)`
   (`def-weil-residue-field`). Then `b' = c⁻¹b` satisfies `b'a = 1`.
   A unital field homomorphism is injective. Applying this to `b'` shows `ab' = 1`,
   hence `a` is an isomorphism. Also `f(y) = x`, as required. -/
theorem rationalLift_iff_locallyClosed_section
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [LocallyOfFiniteType f] (x : X) :
    (∃ y : Y, f y = x ∧ IsIso (f.residueFieldMap y)) ↔
      ∃ (Z : Scheme.{u}) (j : Z ⟶ X),
        IsImmersion j ∧ x ∈ Set.range j ∧ ∃ s : Z ⟶ Y, s ≫ f = j := by
  sorry

end AlgebraicGeometry
