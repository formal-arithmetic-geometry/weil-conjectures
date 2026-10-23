/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso

/-!
# The Kummer class of a divisor

For a closed immersion `i : D ⟶ T` of codimension one, regular, into a scheme `T` smooth over a
perfect field, the *Kummer class of the divisor* `cl(D) ∈ H²_D(T, Λ(1))` is the class of a frame
of the ideal of `D`, glued over all frames (`lem-pur-divisor-class`): the fundamental class
of `i` in codimension one (`AlgebraicGeometry.Etale.fundamentalClass`). On every frame, that
is on every étale `U ⟶ T` on which `D` is cut out by one function `f`, it restricts to the
class of the frame, the Kummer boundary `∂κ(f)`.

## Implementation notes

The blueprint works with a divisor `D ⊂ T` in a smooth family `T ⟶ B`; here `T` itself is smooth
over the base field, the setting of the fundamental classes of
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`. The additivity
`cl(D₁ + D₂) = cl(D₁) + cl(D₂)` and the comparison with the first Chern class `c₁(𝒪_T(D))`
(clause (b)) are not stated: the library has no first Chern classes of line bundles.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {T D : Scheme.{u}} [HasInvertibleExponent Λ T]
  {k : Type u} [Field k] [PerfectField k] (i : D ⟶ T) [IsRegularImmersion 1 i]

/-- Blueprint `lem-pur-divisor-class`: The Kummer class of a divisor

The *Kummer class* `cl(D) ∈ H²_D(T, Λ(1))` of a regular divisor `i : D ⟶ T`, `T` smooth over a
perfect field: the class `Λ_T ⟶ Ri_! Ri^! (Λ_T(1)[2])` restricting on every frame to the class
of the frame (`AlgebraicGeometry.Etale.divisorClass_frameRestriction`). It is the fundamental
class of `i` in codimension one, well defined by frame independence
(`lem-pur-frame-independence`). -/
noncomputable def divisorClass (aT : T ⟶ Spec (.of k)) [Smooth aT]
    (hD : ∀ z : D, IsRegularLocalRing (D.presheaf.stalk z)) :
    constantComplex Λ T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ T 1)⟦2 * ((1 : ℕ) : ℤ)⟧)) :=
  fundamentalClass Λ 1 i aT hD

/-- Blueprint `lem-pur-divisor-class`: The Kummer class of a divisor

**(a)** For a local equation `f` of `D` on an étale `U ⟶ T` (a frame of length one), the
restriction of `cl(D)` to `U` is the class of the frame, the Kummer boundary `∂κ(f)`. -/
theorem divisorClass_frameRestriction (aT : T ⟶ Spec (.of k)) [Smooth aT]
    (hD : ∀ z : D, IsRegularLocalRing (D.presheaf.stalk z)) (F : i.EtaleFrame 1) :
    frameRestriction Λ F (divisorClass Λ i aT hD) = frameClass Λ F :=
  frameRestriction_fundamentalClass Λ 1 i aT hD F

/-- Blueprint `lem-pur-divisor-class`: The Kummer class of a divisor

The Kummer class of a divisor is a Thom class: its adjoint `Λ_D ⟶ Ri^! (Λ_T(1)[2])` is an
isomorphism. -/
theorem isIso_supportedClassMap_divisorClass (aT : T ⟶ Spec (.of k)) [Smooth aT]
    (hD : ∀ z : D, IsRegularLocalRing (D.presheaf.stalk z)) :
    IsIso (supportedClassMap Λ i (divisorClass Λ i aT hD)) :=
  isIso_fundamentalClassMap Λ 1 i aT hD

end AlgebraicGeometry.Etale
