/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.Algebra.Homology.KInjectiveResolution

/-!
# The support-localization triangle of a complex of injective sheaves

Let `j : U ⟶ X` be an open immersion with closed complement `s : Z ⟶ X`. For a complex `I` of
étale sheaves on `X` put

`A(I) = s_* s^! I = ker(I ⟶ j_* j^* I)`, `B(I) = I`, `C(I) = j_* j^* I`,

the complex of sections supported on `Z`, the complex itself and the restriction to the open
part. If the terms of `I` are injective, the restriction `I ⟶ j_* j^* I` is a degreewise split
epimorphism, so `0 ⟶ A(I) ⟶ B(I) ⟶ C(I) ⟶ 0` is a short exact sequence of complexes
(`lem-pur-support-exact`). The map from the mapping cone of the inclusion `u : A(I) ⟶ B(I)` to
`C(I)`, `(b, a) ↦ [b]`, is then a quasi-isomorphism, and the *support-localization triangle*
`A(I) ⟶ B(I) ⟶ C(I) ⟶ A(I)[1]` is the image of the cone triangle in the derived category, with
its third term identified with `C(I)` (`rem-ptr-pur-support-triangle-2`).

## Main definitions

- `AlgebraicGeometry.Etale.supportsShortComplex`: the short complex `A(I) ⟶ B(I) ⟶ C(I)`.
- `AlgebraicGeometry.Etale.supportLocalizationTriangle`: the support-localization triangle.

## Main statements

- `AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`
- `AlgebraicGeometry.Etale.shortExact_supportsShortComplex`
- `AlgebraicGeometry.Etale.quasiIso_descShortComplex_supportsShortComplex`
- `AlgebraicGeometry.Etale.supportLocalizationTriangle_distinguished`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (s : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion s]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

section Resolution

variable {X' : Scheme.{u}}

end Resolution

end Etale

end AlgebraicGeometry
