/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Properness of morphisms of schemes over a base

Cancellation for properness, packaged for the category `Over S` of schemes over a base scheme
`S`: a morphism of `S`-schemes with proper source and separated target is proper. Properness —
and, separately, universal closedness — of the structure morphism of a scheme-theoretic fibre,
which is the corresponding property base changed along `Spec κ(y) ⟶ Y`. Together with the global
sections of a proper integral scheme over an algebraically closed field, which Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` gives outright.

Finally, a proper affine scheme over an Artinian ring — over a field, in particular — is an
Artinian scheme, hence a finite discrete space of Krull dimension at most zero.

## Main results

- `AlgebraicGeometry.isProper_left`: a morphism `f : X ⟶ Y` in `Over S` with `X` proper over `S`
  and `Y` separated over `S` is proper.
- `AlgebraicGeometry.isProper_fiberToSpecResidueField` and
  `AlgebraicGeometry.universallyClosed_fiberToSpecResidueField`: the structure morphism
  `X_y ⟶ Spec κ(y)` of the scheme-theoretic fibre of a proper, respectively universally closed,
  morphism is proper, respectively universally closed.
- `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop` (blueprint `lem:cube-global-sections`): for
  `X` proper and integral over an algebraically closed field `K`, the structure map
  `K ⟶ Γ(X, 𝒪_X)` is an isomorphism.
- `AlgebraicGeometry.isArtinianScheme_of_isProper` and
  `AlgebraicGeometry.topologicalKrullDim_le_zero_of_isProper` (blueprint
  `lem:deg-proper-affine-finite`): a proper affine scheme over an Artinian ring is an Artinian
  scheme, and has dimension at most zero.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ Y` of schemes over `S` with `X` proper over `S` and `Y` separated over
`S` is proper.

```
             f.left
    X.left ─────────→ Y.left
         ╲           ╱
   X.hom  ╲         ╱  Y.hom
           ↘       ↙
               S
```
-/
instance (priority := low) isProper_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  exact IsProper.of_comp _ Y.hom

/-- The structure morphism `X_y ⟶ Spec κ(y)` of the scheme-theoretic fibre of a proper morphism
`f : X ⟶ Y` over `y : Y` is proper, being the base change of `f` along `Spec κ(y) ⟶ Y`.

```
    X_y ─────→ X
     │         │
     │         │ f
     ↓         ↓
 Spec κ(y) ──→ Y
```
-/
instance isProper_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) :
    IsProper (f.fiberToSpecResidueField y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The structure morphism `X_y ⟶ Spec κ(y)` of the scheme-theoretic fibre of a universally
closed morphism `f : X ⟶ Y` over `y : Y` is universally closed, being the base change of `f`
along `Spec κ(y) ⟶ Y`. -/
instance universallyClosed_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] (y : Y) : UniversallyClosed (f.fiberToSpecResidueField y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- **The global sections of a proper integral scheme over an algebraically closed field.**

For `X` proper and integral over an algebraically closed field `K`, the structure morphism
induces an isomorphism `K ≅ Γ(X, 𝒪_X)`. This is `lem:cube-global-sections` of the blueprint.

Mathlib's `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` makes `Γ(X, 𝒪_X)` an
integral extension of `K`, and it is a domain because `X` is integral; over an algebraically
closed `K` an integral domain extension is trivial. -/
theorem isIso_ΓSpecIso_inv_comp_appTop {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π] :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
  apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed π

section ProperAffine

variable {R : Type u} [CommRing R] [IsArtinianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- **A proper affine scheme over an Artinian ring is an Artinian scheme.**

In particular it is a finite discrete space, all of whose points are closed. Over a field this
is the blueprint's `lem:deg-proper-affine-finite`. -/
theorem isArtinianScheme_of_isProper [IsAffine X] [IsProper f] : IsArtinianScheme X := by
  -- a proper affine morphism is finite, so `Γ(X, 𝒪_X)` is a finite `R`-algebra, hence Artinian
  have : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have := IsFinite.finite_ΓSpecIso_inv_comp_appTop f
  algebraize [((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom]
  have : IsArtinianRing Γ(X, ⊤) := .of_finite R _
  have : IsLocallyArtinian (Spec Γ(X, ⊤)) := Scheme.isLocallyArtinianScheme_Spec.mpr ‹_›
  have : IsLocallyArtinian X := .of_isImmersion X.isoSpec.hom
  constructor

/-- **A proper affine scheme over an Artinian ring has dimension at most zero.**

Over a field this is the last assertion of the blueprint's `lem:deg-proper-affine-finite`. -/
theorem topologicalKrullDim_le_zero_of_isProper [IsAffine X] [IsProper f] :
    topologicalKrullDim X ≤ 0 :=
  have := isArtinianScheme_of_isProper f
  topologicalKrullDim_zero_of_discreteTopology X

end ProperAffine

end AlgebraicGeometry
