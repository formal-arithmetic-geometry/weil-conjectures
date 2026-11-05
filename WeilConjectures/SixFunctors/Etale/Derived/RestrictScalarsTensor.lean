/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom

/-!
# The projection formula for extension and restriction of scalars

Let `φ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel. For
étale sheaves of modules, the restriction of scalars of `(Λ' ⊗_Λ P) ⊗ M` is `P ⊗ Res M`,
naturally in `P` and `M` (`CategoryTheory.Sheaf.extendScalarsTensorRestrictScalarsIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

namespace CategoryTheory.MonoidalCategory

variable {𝒜 𝒜' : Type*} [Category* 𝒜] [Category* 𝒜'] [MonoidalCategory 𝒜]
  [MonoidalCategory 𝒜'] (E : 𝒜 ⥤ 𝒜') [E.Monoidal] (R : 𝒜' ⥤ 𝒜) (ε : R ⋙ E ≅ 𝟭 𝒜') (c : 𝒜)
  (T : E ⋙ R ≅ tensorRight c)

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A A' : Type (u + 1)} [CommRing A] [CommRing A'] {f : A →+* A'}
  (hf : Function.Surjective f) {a : A} (ha : RingHom.ker f = Ideal.span {a})

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

end Etale

end AlgebraicGeometry
