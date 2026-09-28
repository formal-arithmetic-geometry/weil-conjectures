/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf `Ω¹_{X/S}` of relative Kähler differentials is
the sheafification of the presheaf of `𝒪_X`-modules `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`
(Stacks, Tag 08RL and Tag 01UR). Here `f⁻¹𝒪_S` is taken to be the presheaf inverse image of
`𝒪_S`; replacing it by its sheafification does not change the result after sheafifying.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.invImage`: the presheaf of commutative rings `f⁻¹𝒪_S` on `X`.
- `AlgebraicGeometry.Scheme.Hom.invImageToStructure`: the map `f⁻¹𝒪_S ⟶ 𝒪_X` adjoint to `f♯`.
- `AlgebraicGeometry.Scheme.Hom.cotangent`: the sheaf `Ω¹_{X/S}` of relative differentials.
- `AlgebraicGeometry.Scheme.Hom.cotangentDerivation`: the universal derivation
  `d : 𝒪_X → Ω¹_{X/S}`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.nonempty_cotangent_Spec_map`: for a ring map `A → B`, the global
  sections of `Ω¹_{Spec B / Spec A}` are `Ω[B⁄A]`.
- `AlgebraicGeometry.Scheme.Hom.isZero_cotangent_id`: `Ω¹_{X/X} = 0`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The presheaf inverse image `f⁻¹𝒪_S` of the structure sheaf of `S`, a presheaf of
commutative rings on `X`. -/
noncomputable def invImage (f : X ⟶ S) : TopCat.Presheaf CommRingCat.{u} X :=
  (TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf

/-- The morphism `f⁻¹𝒪_S ⟶ 𝒪_X` of presheaves of commutative rings on `X`, adjoint to
`f♯ : 𝒪_S ⟶ f_*𝒪_X`. -/
noncomputable def invImageToStructure (f : X ⟶ S) : f.invImage ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm f.c

/-- The sheaf of relative Kähler differentials `Ω¹_{X/S}` of a morphism of schemes `f : X ⟶ S`:
the sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`. -/
noncomputable def cotangent (f : X ⟶ S) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' f.invImageToStructure)

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/S}`, relative to `f⁻¹𝒪_S ⟶ 𝒪_X`: the universal
derivation into the presheaf of differentials, composed with the sheafification unit. -/
noncomputable def cotangentDerivation (f : X ⟶ S) :
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      f.cotangent).Derivation' f.invImageToStructure :=
  (PresheafOfModules.DifferentialsConstruction.derivation' f.invImageToStructure).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _)

/-- For a ring map `A → B`, the global sections of `Ω¹_{Spec B / Spec A}` are the module of
Kähler differentials `Ω[B⁄A]`. -/
theorem nonempty_cotangent_Spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    letI := φ.hom.toAlgebra
    Nonempty (Γ((Spec.map φ).cotangent, ⊤) ≃ Ω[B⁄A]) := by
  sorry

/-- The sheaf of relative differentials of the identity morphism vanishes: `Ω¹_{X/X} = 0`. -/
theorem isZero_cotangent_id (X : Scheme.{u}) : Limits.IsZero (𝟙 X : X ⟶ X).cotangent := by
  sorry

end AlgebraicGeometry.Scheme.Hom
