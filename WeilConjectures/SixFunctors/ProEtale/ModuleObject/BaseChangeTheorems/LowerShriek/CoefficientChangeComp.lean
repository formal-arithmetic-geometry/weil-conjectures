/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComposition

/-!
# Coefficient changes and the composition isomorphisms of the lower shriek

Let `P` be a pushforward datum for the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`). For composable `f : X ⟶ Y` and
`g : Y ⟶ S`, the composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the chosen
compactifications (`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekComp`)
is `BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications` for the chosen
compactifications of `f` and `g` and a chosen compactification of their composite with cartesian
square. It is defined whenever the exchange morphisms `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` are
isomorphisms (`BoundedConstructiblePushforwardData.IsIsoExchange`).
This is the construction of `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` and
`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`, for a general pushforward
datum.

For a coefficient change `C` (`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`),
the composition isomorphism is compatible with the coefficient comparisons
(`...squareCompatible_lowerShriekComp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {ℓ : ℕ} [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace BoundedConstructiblePushforwardData

variable (P : BoundedConstructiblePushforwardData Λ ℓ k)

/-- The exchange morphisms `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of cartesian squares with `p'` proper are
isomorphisms. -/
def IsIsoExchange : Prop :=
  ∀ {X Z X' Z' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion j.left]
    [IsOpenImmersion i'.left] [IsProper p'.left] (sq : IsPullback p i' j p'),
    IsIso (P.lowerStarOpenImmersionLowerShriekExchange sq)

variable {P} (hP : P.IsIsoRefinementPushforward) (hE : P.IsIsoExchange)
  {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the lower shrieks of the chosen
compactifications: `lowerShriekCompOfCompactifications` for the chosen compactifications of `f`
and `g` and a chosen compactification of their composite with cartesian square
(`Compactification.exists_isPullback_overG_overI`). -/
noncomputable def lowerShriekComp (f : X ⟶ Y) (g : Y ⟶ S) :
    P.lowerShriekOfCompactification (compactificationOverField (f ≫ g)) ≅
      P.lowerShriekOfCompactification (compactificationOverField f) ⋙
        P.lowerShriekOfCompactification (compactificationOverField g) :=
  have hd := Compactification.exists_isPullback_overG_overI (compactificationOverField f)
    (compactificationOverField g)
  have := hE hd.choose_spec
  lowerShriekCompOfCompactifications hP _ _ hd.choose hd.choose_spec

end BoundedConstructiblePushforwardData

namespace BoundedConstructibleCoefficientChange

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  {P : BoundedConstructiblePushforwardData Λ ℓ k} {P' : BoundedConstructiblePushforwardData Λ' ℓ k}
  {T : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom], Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧}
  {pull : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T X ≅ T Y ⋙ boundedConstructibleUpperStar Λ' ℓ f}
  (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)

variable (hP : P.IsIsoRefinementPushforward) (hE : P.IsIsoExchange)
  (hP' : P'.IsIsoRefinementPushforward) (hE' : P'.IsIsoExchange)
  {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The coefficient comparison
for `Rf_!` is compatible with the composition of morphisms.** For a coefficient change `C`, the
comparison `R(f ≫ g)_! ⋙ T ≅ T ⋙ R(f ≫ g)_!` (along the chosen compactifications) corresponds,
under the composition isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` over `Λ` and over `Λ'`, to the
comparison pasted from those for `f` and for `g`. -/
theorem squareCompatible_lowerShriekComp :
    NatTrans.SquareCompatible
      (C.shriekOfCompactification (compactificationOverField (f ≫ g)))
      (Functor.pasteSquareIso (C.shriekOfCompactification (compactificationOverField f))
        (C.shriekOfCompactification (compactificationOverField g)))
      (BoundedConstructiblePushforwardData.lowerShriekComp hP hE f g).hom
      (BoundedConstructiblePushforwardData.lowerShriekComp hP' hE' f g).hom := by
  have hd := Compactification.exists_isPullback_overG_overI (compactificationOverField f)
    (compactificationOverField g)
  have := hE hd.choose_spec
  have := hE' hd.choose_spec
  exact C.squareCompatible_lowerShriekCompOfCompactifications hP hP' _ _ hd.choose hd.choose_spec

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
