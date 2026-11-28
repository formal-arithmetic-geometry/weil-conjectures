/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.ConstructibleIndExtBoundOfContinuity
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityAlgCl
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityFinite

/-!
# Extending a specified constructible Ext bound to ind-constructible sheaves
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The specified bound extends to ind-constructible targets on a Noetherian scheme,
for either of the canonical field coefficient sheaves. -/
theorem constructibleInd_extBound_noetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    (d : ℕ)
    (hbound : ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X),
      IsConstantModelConstructible (coefficientHeartRingObj R) X N → ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hB : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (coefficientHeartRingObj R) X) B)
    (r : ℕ) (hr : d < r) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
  apply constructibleInd_extBound_of_continuity (coefficientHeartRingObj R) X C hC
    (constantModelExtContinuity_of_isLocallyNoetherian ℓ E R hR X) d hbound B hB r hr

/-- A specified bound against constructible sheaves also bounds Ext into an
ind-constructible sheaf on a locally Noetherian quasi-compact scheme. The coefficient
equality includes the multiplication, via bundled monoid objects. -/
theorem constructibleInd_extBound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (_hC : IsConstantModelConstructible Λ X C)
    (d : ℕ)
    (hbound : ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      IsConstantModelConstructible Λ X N → ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hB : ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B)
    (r : ℕ) (hr : d < r) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by
  rcases _hΛ with hΛ | hΛ
  · obtain ⟨rfl, h⟩ := Mon.mk.inj hΛ
    cases eq_of_heq h
    exact constructibleInd_extBound_of_continuity _ X C _hC
      (continuousMap_ext_continuity ℓ E X) d hbound B hB r hr
  · obtain ⟨rfl, h⟩ := Mon.mk.inj hΛ
    cases eq_of_heq h
    exact constructibleInd_extBound_of_continuity _ X C _hC
      (padicAlgCl_ext_continuity ℓ X) d hbound B hB r hr

end AlgebraicGeometry.ProEtale
