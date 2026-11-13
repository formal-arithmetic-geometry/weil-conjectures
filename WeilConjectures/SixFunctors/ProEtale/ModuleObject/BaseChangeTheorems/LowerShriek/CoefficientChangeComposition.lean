/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!
# Coefficient changes, identities and composition of extensions by zero

Let `C` be a coefficient change `Λ ⟶ Λ'` of the bounded constructible six functors
(`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`). This file shows that the
following isomorphisms are compatible with the coefficient comparisons of `C`:

* the identity isomorphisms `L(𝟙 X)^* ≅ 𝟭` of the pullbacks
  (`...BoundedConstructibleCoefficientChange.squareCompatible_upperStarId`), a formal
  consequence of the compatibility of (Pull) with the composition isomorphisms and the unit law;
* the composition isomorphisms `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero along open
  immersions (`...squareCompatible_openImmersionLowerShriekComp`), conjugate to the composition
  isomorphisms of the pullbacks;
* the identifications `Rf_!^c = Rf'_!^{c'}` of the lower shrieks along the chosen
  compactifications of equal morphisms `f = f'`
  (`...squareCompatible_shriekOfCompactification_eqToHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleCoefficientChange

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {ℓ : ℕ} [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {P : BoundedConstructiblePushforwardData Λ ℓ k}
  {P' : BoundedConstructiblePushforwardData Λ' ℓ k}
  {T : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom], Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧}
  {pull : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T X ≅ T Y ⋙ boundedConstructibleUpperStar Λ' ℓ f}
  (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)
  {X Y V : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom]

/-- (Pull) is compatible with the identity isomorphisms `L(𝟙 X)^* ≅ 𝟭`. -/
lemma squareCompatible_upperStarId (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] :
    NatTrans.SquareCompatible (pull (𝟙 X)) (Functor.idSquareIso (T X))
      (boundedConstructibleUpperStarId Λ ℓ X).hom (boundedConstructibleUpperStarId Λ' ℓ X).hom := by
  have h₁ : boundedConstructibleUpperStar Λ ℓ (𝟙 X) =
      boundedConstructibleUpperStar Λ ℓ (𝟙 X ≫ 𝟙 X) := by
    rw [Category.id_comp]
  have h₂ : boundedConstructibleUpperStar Λ' ℓ (𝟙 X) =
      boundedConstructibleUpperStar Λ' ℓ (𝟙 X ≫ 𝟙 X) := by
    rw [Category.id_comp]
  refine NatTrans.SquareCompatible.of_comp_unit _ _
    (d := eqToHom h₁ ≫ (boundedConstructibleUpperStarComp Λ ℓ (𝟙 X) (𝟙 X)).hom)
    (d' := eqToHom h₂ ≫ (boundedConstructibleUpperStarComp Λ' ℓ (𝟙 X) (𝟙 X)).hom)
    (fun K ↦ ?_) (fun K ↦ ?_)
    ((squareCompatible_eqToHom pull (Category.id_comp (𝟙 X)).symm h₁ h₂).comp
      (C.pull_comp (𝟙 X) (𝟙 X)))
  · rw [NatTrans.comp_app, Category.assoc, boundedConstructibleUpperStarComp_id_left_app,
      eqToHom_app, eqToHom_trans, eqToHom_refl]
  · rw [NatTrans.comp_app, Category.assoc, boundedConstructibleUpperStarComp_id_left_app,
      eqToHom_app, eqToHom_trans, eqToHom_refl]

/-- The composition isomorphisms `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero along open
immersions are compatible with the coefficient comparisons (Shriek). -/
lemma squareCompatible_openImmersionLowerShriekComp (j : X ⟶ Y) (j' : Y ⟶ V)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left] :
    NatTrans.SquareCompatible (C.shriek (j ≫ j'))
      (Functor.pasteSquareIso (C.shriek j) (C.shriek j'))
      (boundedConstructibleOpenImmersionLowerShriekComp Λ ℓ j j').hom
      (boundedConstructibleOpenImmersionLowerShriekComp Λ' ℓ j j').hom := by
  have h := NatTrans.SquareCompatible.conjugateEquiv_symm (C.isMateSquare_shriek_pull (j ≫ j'))
    ((C.isMateSquare_shriek_pull j).comp (C.isMateSquare_shriek_pull j')) (C.pull_comp j j')
  exact NatTrans.SquareCompatible.inv
    (e := (conjugateIsoEquiv
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (j ≫ j'))
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).comp
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j'))).symm
      (boundedConstructibleUpperStarComp Λ ℓ j j'))
    (e' := (conjugateIsoEquiv
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ (j ≫ j'))
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ j).comp
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ j'))).symm
      (boundedConstructibleUpperStarComp Λ' ℓ j j')) h

/-- The identifications `Rf_!^c = Rf'_!^{c'}` of the lower shrieks along the chosen
compactifications of equal morphisms are compatible with the coefficient comparisons. -/
lemma squareCompatible_shriekOfCompactification_eqToHom {f f' : X ⟶ Y} (hf : f = f')
    (h₁ : P.lowerShriekOfCompactification (compactificationOverField f) =
      P.lowerShriekOfCompactification (compactificationOverField f'))
    (h₂ : P'.lowerShriekOfCompactification (compactificationOverField f) =
      P'.lowerShriekOfCompactification (compactificationOverField f')) :
    NatTrans.SquareCompatible (C.shriekOfCompactification (compactificationOverField f))
      (C.shriekOfCompactification (compactificationOverField f')) (eqToHom h₁) (eqToHom h₂) := by
  subst hf
  simpa only [eqToHom_refl] using NatTrans.SquareCompatible.id _

end AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleCoefficientChange
