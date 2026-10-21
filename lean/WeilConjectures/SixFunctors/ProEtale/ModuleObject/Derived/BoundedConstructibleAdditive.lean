/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Additivity of the six functors on bounded constructible complexes

The derived pushforward `Rf_*`, the extension by zero `j_!` along an open immersion and the
derived lower shriek `Rf_!` on bounded constructible complexes `Dᵇc(-)⟦Λ⟧` are additive
functors: they are restrictions (`ObjectProperty.lift`) of additive functors on the ambient
derived categories, the right derived functor `R((f)_*⟦Λ⟧)` of an additive functor and the
functor `D((j)_!open⟦Λ⟧)` induced by an exact functor.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pushforward on bounded constructible complexes is additive. -/
instance additive_boundedConstructibleLowerStar [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) :
    (boundedConstructibleLowerStar Λ ℓ f).Additive := by
  unfold boundedConstructibleLowerStar
  infer_instance

/-- The extension by zero along an open immersion on bounded constructible complexes is
additive. -/
instance additive_boundedConstructibleOpenImmersionLowerShriek (j : X ⟶ Y)
    [IsOpenImmersion j.left] : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Additive := by
  unfold boundedConstructibleOpenImmersionLowerShriek
  infer_instance

/-- The lower shriek `Rf_!^c` attached to a compactification is additive. -/
instance additive_boundedConstructibleLowerShriekOfCompactification
    [IsFinitenessCoefficient ℓ Λ] {f : X ⟶ Y}
    (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).Additive := by
  unfold boundedConstructibleLowerShriekOfCompactification
  infer_instance

/-- The derived lower shriek on bounded constructible complexes is additive. -/
instance additive_boundedConstructibleLowerShriek [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) :
    (boundedConstructibleLowerShriek Λ ℓ f).Additive := by
  unfold boundedConstructibleLowerShriek
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
