/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperUpperShriekExistence

/-!
# The adjunction `Rf_! ⊣ f^!` on bounded constructible complexes

Let `Λ` be a commutative condensed ring and `c` a compactification of `f : X ⟶ Y` with the
properties `LowerShriekLocalizingHypotheses` of blueprint `det-sf-comp-coherence-single`, so that
`Rf_!(c)` restricts to functors `Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` and
`Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧`. If `G` is a right adjoint of the former which maps `Dᵇc(Y)⟦Λ⟧` into
`Dᵇc(X)⟦Λ⟧`, its restriction `Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekBoundedConstructible`) is right adjoint to
the latter (`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleAdjunction`): the
inclusions `Dᵇc ⊆ Loc(Dᵇc)` are fully faithful.

For the `ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ`, every right adjoint `f^!` maps `Dᵇc(Y)⟦Λ⟧`
into `Dᵇc(X)⟦Λ⟧` (blueprints `sk-thm-restriction` and `sk-thm-int-restriction`), and this gives
blueprint `theorem-f-shriek-ell-adic-coefficients--4`: the restriction of `f^!` is right adjoint
to `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧`.

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.upperShriekBoundedConstructible`
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleAdjunction`
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleAdjunction_continuousMapRingObj`,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleAdjunction_padicIntegersRingObj`,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleAdjunction_padicAlgClRingObj`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The restriction `Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` of a functor `G : Loc(Dᵇc(Y)⟦Λ⟧) ⥤ Loc(Dᵇc(X)⟦Λ⟧)`
mapping `Dᵇc(Y)⟦Λ⟧` into `Dᵇc(X)⟦Λ⟧`. -/
noncomputable abbrev upperShriekBoundedConstructible
    {G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X}
    (hG : ∀ L : LocalizingBoundedConstructible Λ Y,
      boundedConstructible (condensedRingObj Λ Y) L.obj →
        boundedConstructible (condensedRingObj Λ X) (G.obj L).obj) :
    (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory ⥤
      (boundedConstructible (condensedRingObj Λ X)).FullSubcategory :=
  (boundedConstructible (condensedRingObj Λ X)).lift
    (ObjectProperty.ιOfLE (ObjectProperty.le_localizingClosure _) ⋙ G ⋙
      (localizingBoundedConstructible Λ X).ι) fun L ↦ hG _ L.2

/-- If a right adjoint `G` of `Rf_!(c) : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` maps `Dᵇc(Y)⟦Λ⟧` into
`Dᵇc(X)⟦Λ⟧`, then its restriction to `Dᵇc` is right adjoint to the restriction
`Rf_!(c) : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧`: the inclusions `Dᵇc ⊆ Loc(Dᵇc)` are fully faithful and
intertwine both functors with their restrictions. -/
noncomputable def boundedConstructibleAdjunction (hc : LowerShriekLocalizingHypotheses Λ c)
    {G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X}
    (adj : rightDerivedLowerShriekLocalizing hc ⊣ G)
    (hG : ∀ L : LocalizingBoundedConstructible Λ Y,
      boundedConstructible (condensedRingObj Λ Y) L.obj →
        boundedConstructible (condensedRingObj Λ X) (G.obj L).obj) :
    rightDerivedLowerShriekBoundedConstructible hc ⊣ upperShriekBoundedConstructible hG :=
  adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (ObjectProperty.le_localizingClosure _))
    (ObjectProperty.fullyFaithfulιOfLE (ObjectProperty.le_localizingClosure _))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
      ext; simp [rightDerivedLowerShriekLocalizing, ObjectProperty.localizingClosureLift]))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; simp))

end General

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)

/-- Blueprint `theorem-f-shriek-ell-adic-coefficients--4` (for `Λ = E`): for the coefficient
ring `E̲` of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a separated finite-type `k`-morphism
`f : X ⟶ Y` with compactification `c`, and a right adjoint `f^!` of
`Rf_! : Loc(Dᵇc(X)⟦E⟧) ⥤ Loc(Dᵇc(Y)⟦E⟧)`, the restriction of `f^!` to `Dᵇc(Y)⟦E⟧`
(which lands in `Dᵇc(X)⟦E⟧`,
`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj`) is
right adjoint to `Rf_! : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(Y)⟦E⟧`. -/
noncomputable def boundedConstructibleAdjunction_continuousMapRingObj
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (hf : f ≫ aY = aX)
    {G : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
      LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X}
    (adj : rightDerivedLowerShriekLocalizing
      (lowerShriek_continuousMapRingObj ℓ E aY c) ⊣ G) :
    rightDerivedLowerShriekBoundedConstructible (lowerShriek_continuousMapRingObj ℓ E aY c) ⊣
      upperShriekBoundedConstructible
        (boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj
          ℓ aX aY c E hf adj) :=
  boundedConstructibleAdjunction _ adj _

/-- Blueprint `theorem-f-shriek-ell-adic-coefficients--4` (for `Λ = 𝒪_E`): for the coefficient
ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a separated finite-type `k`-morphism
`f : X ⟶ Y` with compactification `c`, and a right adjoint `f^!` of
`Rf_! : Loc(Dᵇc(X)⟦𝒪_E⟧) ⥤ Loc(Dᵇc(Y)⟦𝒪_E⟧)`, the restriction of `f^!` to `Dᵇc(Y)⟦𝒪_E⟧`
(which lands in `Dᵇc(X)⟦𝒪_E⟧`,
`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj`) is
right adjoint to `Rf_! : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(Y)⟦𝒪_E⟧`. -/
noncomputable def boundedConstructibleAdjunction_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (hf : f ≫ aY = aX)
    {G : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
      LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X}
    (adj : rightDerivedLowerShriekLocalizing
      (lowerShriek_padicIntegersRingObj ℓ E aY c) ⊣ G) :
    rightDerivedLowerShriekBoundedConstructible (lowerShriek_padicIntegersRingObj ℓ E aY c) ⊣
      upperShriekBoundedConstructible
        (boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj
          ℓ aX aY c E hf adj) :=
  boundedConstructibleAdjunction _ adj _

/-- Blueprint `theorem-f-shriek-ell-adic-coefficients--4` (for `Λ = ℚ̄_ℓ`): for a separated
finite-type `k`-morphism `f : X ⟶ Y` with compactification `c` and a right adjoint `f^!` of
`Rf_! : Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧) ⥤ Loc(Dᵇc(Y)⟦ℚ̄_ℓ⟧)`, the restriction of `f^!` to `Dᵇc(Y)⟦ℚ̄_ℓ⟧`
(which lands in `Dᵇc(X)⟦ℚ̄_ℓ⟧`,
`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj`) is right
adjoint to `Rf_! : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧`. -/
noncomputable def boundedConstructibleAdjunction_padicAlgClRingObj (hf : f ≫ aY = aX)
    {G : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
      LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X}
    (adj : rightDerivedLowerShriekLocalizing
      (lowerShriek_padicAlgClRingObj ℓ aY c) ⊣ G) :
    rightDerivedLowerShriekBoundedConstructible (lowerShriek_padicAlgClRingObj ℓ aY c) ⊣
      upperShriekBoundedConstructible
        (boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj
          ℓ aX aY c hf adj) :=
  boundedConstructibleAdjunction _ adj _

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
