/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Stability of `Dctf`: the exceptional inverse image

For torsion coefficients `Λ` with invertible exponent and schemes of finite type over a field,
this file proves that the exceptional inverse image `Rf^!` preserves `Dctf`, with the shifts
of `sk-prop-sf-rf-shriek-preservation`, and constructs the descended functors `Rf_*`, `Rf_!`
and `Rf^!`.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-! #### The exceptional inverse image -/

omit [Finite Λ] in
/-- A locally constant sheaf of free rank-one `Λ`-modules, for a finite `Λ`, is constructible and
flat. -/
lemma isConstructibleSheaf_and_flat_of_sheafFiber_iso {X : Scheme.{u}}
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    IsConstructibleSheaf L ∧ ObjectProperty.flat L := by
  have : IsFiniteSheaf L := ⟨fun Ω _ _ s ↦
    (ConcreteCategory.isFinitelyGenerated_iff_of_iso (hL Ω s).some).2
      ((ModuleCat.isFinitelyGenerated_iff _).2 inferInstance)⟩
  have : IsFiniteLocallyConstantSheaf L := {}
  refine ⟨IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›,
    (flat_iff_forall_flat_sheafFiber_obj L).2 fun {Ω} _ _ s ↦ ?_⟩
  exact ObjectProperty.prop_of_iso _ ((GrothendieckTopology.Point.uliftSheafFiberIso _ _).app L ≪≫
    (hL Ω s).some).symm (ObjectProperty.prop_unit (ObjectProperty.flat (A := ModuleCat.{u + 1} Λ)))

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (iii): for `f` smooth of pure relative dimension `d` and a finite `Λ` whose exponent is
invertible on `Y`, the exceptional inverse image shifts both intervals by `-2d`,
`D_c^[a, b] ↦ D_c^[a - 2d, b - 2d]`, by purity `Rf^! ≅ Lf^*(-)(d)[2d]`. Without choosing an
orientation, `Rf^! K ≅ Lf^* K ⊗ᴸ L[2d]` for a locally constant sheaf `L` of free rank-one
`Λ`-modules (`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`,
`thm-asd-smooth-tensor`), and tensoring with the flat constructible `L` changes neither the
constructible interval nor the Tor amplitude. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
      ((R(f)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ X := .of_hom f
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  obtain ⟨et⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d K
  obtain ⟨_, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  obtain ⟨⟨hbc, -⟩, hta⟩ := hK
  have hL₀ := torAmplitudeIn_singleFunctor_zero_of_flat _ L hLf
  have hMbc := boundedConstructible_tensor Λ X (boundedConstructible_leftDerivedUpperStar _ f hbc)
    (DerivedCategory.boundedConstructible_singleFunctor_obj L 0) ⟨0, 0, hL₀⟩
  exact constructibleTorAmplitudeIn_of_iso_tensor_shift _ et.symm eω
    (torAmplitudeIn_leftDerivedUpperStar _ f a b hta) hL₀
    ((boundedConstructible _ X).le_shift _ _ hMbc)

/-! #### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

end Functors

end Torsion

end Etale

end AlgebraicGeometry
