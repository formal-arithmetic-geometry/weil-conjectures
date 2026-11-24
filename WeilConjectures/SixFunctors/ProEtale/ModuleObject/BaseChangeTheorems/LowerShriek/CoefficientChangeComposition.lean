/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeRefinement

/-!
# Coefficient changes and the composition isomorphisms of `Rf_!`

Let `P` be a pushforward datum for a coefficient ring `Λ`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`). For morphisms `f : X ⟶ Y` and
`g : Y ⟶ S`, compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`,
and a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of `p ≫ j` with cartesian square, this file
defines the composition isomorphism
`R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}` of `P`
(`BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications`), assembled as the
composition isomorphisms of the coefficient rings `𝒪_E` and `ℚ̄_ℓ`
(`boundedConstructibleLowerShriekComp_padicIntegers`,
`boundedConstructibleLowerShriekComp_padicAlgCl`):
the independence of the compactification for the composite compactification
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, the composition isomorphisms of `j_!` and `Rf_*`, and the inverse of
the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`.

It proves that this composition isomorphism is compatible with the coefficient comparisons of a
coefficient change `C : Λ ⟶ Λ'`
(`BoundedConstructibleCoefficientChange.squareCompatible_lowerShriekCompOfCompactifications`):
each of its pieces is.
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
  {X Y S : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  {f : X ⟶ Y} {g : Y ⟶ S}

namespace BoundedConstructiblePushforwardData

variable (P : BoundedConstructiblePushforwardData Λ ℓ k)

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of `P` for a cartesian square: the exchange
morphism of the extension-by-zero base-change isomorphism under the adjunctions `Lp^* ⊣ Rp_*` and
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def lowerStarOpenImmersionLowerShriekExchange {X' Z Z' : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion j.left]
    [IsOpenImmersion i'.left] (sq : IsPullback p i' j p') :
    P.lowerStar p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙ P.lowerStar p' :=
  Adjunction.exchangeRight (P.adj p) (P.adj p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq)

variable {P} in
/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}` of `P` attached to
compactifications `c` of `f` and `c'` of `g` and a compactification `d` of `p ≫ j` with cartesian
square `hd`, for which the exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` is invertible. -/
noncomputable def lowerShriekCompOfCompactifications (hP : P.IsIsoRefinementPushforward)
    (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left)
    (hd : IsPullback c.overG d.overI c'.overI d.overG)
    [IsIso (P.lowerStarOpenImmersionLowerShriekExchange hd)] :
    P.lowerShriekOfCompactification (compactificationOverField (f ≫ g)) ≅
      P.lowerShriekOfCompactification c ⋙ P.lowerShriekOfCompactification c' :=
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (Compactification.overCompObjIso c c' d).hom.left := by
    simp only [Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI)
      (Compactification.overCompObjIso c c' d).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := hP sqe
  lowerShriekOfCompactificationIso hP _ (c.overComp c' d) ≪≫
    (P.lowerShriekRefinementIso sqe (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekComp Λ ℓ c.overI d.overI)
      _ ≪≫
    Functor.isoWhiskerLeft _ (P.lowerStarComp d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (P.lowerStarOpenImmersionLowerShriekExchange hd)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

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

/-- (Shriek) is compatible with the composition isomorphisms `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the
extensions by zero, the conjugates of the composition isomorphisms of the pullbacks. -/
lemma squareCompatible_openImmersionLowerShriekComp {U V W : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (j : U ⟶ V) (j' : V ⟶ W) [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    [IsOpenImmersion (j ≫ j').left] :
    NatTrans.SquareCompatible (C.shriek (j ≫ j'))
      (Functor.pasteSquareIso (C.shriek j) (C.shriek j'))
      (boundedConstructibleOpenImmersionLowerShriekComp Λ ℓ j j').hom
      (boundedConstructibleOpenImmersionLowerShriekComp Λ' ℓ j j').hom := by
  have h := NatTrans.SquareCompatible.conjugateEquiv_symm
    (C.isMateSquare_shriek_pull (j ≫ j'))
    ((C.isMateSquare_shriek_pull j).comp (C.isMateSquare_shriek_pull j')) (C.pull_comp j j')
  exact NatTrans.SquareCompatible.inv
    (e := (conjugateIsoEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
      (j ≫ j')) ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).comp
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j'))).symm
          (boundedConstructibleUpperStarComp Λ ℓ j j'))
    (e' := (conjugateIsoEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ
      (j ≫ j')) ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ j).comp
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ j'))).symm
          (boundedConstructibleUpperStarComp Λ' ℓ j j')) h

/-- **The composition isomorphisms of `Rf_!` are compatible with the coefficient comparisons**:
under (Shriek) along the compactifications, the composition isomorphism
`R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}`
(`BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications`) over `Λ` corresponds
to the one over `Λ'`. -/
lemma squareCompatible_lowerShriekCompOfCompactifications (hP : P.IsIsoRefinementPushforward)
    (hP' : P'.IsIsoRefinementPushforward) (c : Compactification f.left)
    (c' : Compactification g.left) (d : Compactification (c.overG ≫ c'.overI).left)
    (hd : IsPullback c.overG d.overI c'.overI d.overG)
    [IsIso (P.lowerStarOpenImmersionLowerShriekExchange hd)]
    [IsIso (P'.lowerStarOpenImmersionLowerShriekExchange hd)] :
    NatTrans.SquareCompatible (C.shriekOfCompactification (compactificationOverField (f ≫ g)))
      (Functor.pasteSquareIso (C.shriekOfCompactification c) (C.shriekOfCompactification c'))
      (BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications hP c c' d hd).hom
      (BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications hP' c c' d
        hd).hom := by
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (Compactification.overCompObjIso c c' d).hom.left := by
    simp only [Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have : IsProper (d.overG ≫ c'.overG).left := by
    rw [Over.comp_left]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI)
      (Compactification.overCompObjIso c c' d).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := hP sqe
  have := hP' sqe
  have h₁ := C.squareCompatible_lowerShriekOfCompactificationIso hP hP'
    (compactificationOverField (f ≫ g)) (c.overComp c' d)
  have h₂ := (C.squareCompatible_lowerShriekRefinementIso sqe
    (Compactification.overCompObjIso_hom_overG c c' d)).inv
  have h₃ := NatTrans.SquareCompatible.whiskerRight (C.push (d.overG ≫ c'.overG))
    (C.squareCompatible_openImmersionLowerShriekComp c.overI d.overI)
  have h₄ := NatTrans.SquareCompatible.whiskerLeft
    (Functor.pasteSquareIso (C.shriek c.overI) (C.shriek d.overI))
    (C.squareCompatible_lowerStarComp (h := d.overG) (p := c'.overG)).inv
  have h₅ := NatTrans.SquareCompatible.associator_hom (C.shriek c.overI) (C.shriek d.overI)
    (Functor.pasteSquareIso (C.push d.overG) (C.push c'.overG))
  have : IsIso ((P.adj c.overG).exchangeRight (P.adj d.overG)
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ hd)) :=
    inferInstanceAs (IsIso (P.lowerStarOpenImmersionLowerShriekExchange hd))
  have : IsIso ((P'.adj c.overG).exchangeRight (P'.adj d.overG)
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ' ℓ hd)) :=
    inferInstanceAs (IsIso (P'.lowerStarOpenImmersionLowerShriekExchange hd))
  have hx := (NatTrans.SquareCompatible.exchangeRight (C.isMateSquare_pull_push c.overG)
    (C.isMateSquare_pull_push d.overG)
    (C.squareCompatible_openImmersionLowerShriekBaseChangeIso hd)).isIso_inv
  have h₆ := NatTrans.SquareCompatible.whiskerLeft (C.shriek c.overI)
    ((NatTrans.SquareCompatible.associator_inv (C.shriek d.overI) (C.push d.overG)
      (C.push c'.overG)).comp ((NatTrans.SquareCompatible.whiskerRight (C.push c'.overG) hx).comp
        (NatTrans.SquareCompatible.associator_hom (C.push c.overG) (C.shriek c'.overI)
          (C.push c'.overG))))
  have h₇ := NatTrans.SquareCompatible.associator_inv (C.shriek c.overI) (C.push c.overG)
    (Functor.pasteSquareIso (C.shriek c'.overI) (C.push c'.overG))
  have h := h₁.comp (h₂.comp (h₃.comp (h₄.comp (h₅.comp (h₆.comp h₇)))))
  have h' : NatTrans.SquareCompatible
      (C.shriekOfCompactification (compactificationOverField (f ≫ g)))
      (Functor.pasteSquareIso (C.shriekOfCompactification c) (C.shriekOfCompactification c'))
      _ _ := h
  refine h'.of_eq_natTrans ?_ ?_
  · simp only [BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications,
      BoundedConstructiblePushforwardData.lowerStarOpenImmersionLowerShriekExchange,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      asIso_inv, Functor.whiskerLeft_comp, Category.assoc]
  · simp only [BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications,
      BoundedConstructiblePushforwardData.lowerStarOpenImmersionLowerShriekExchange,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      asIso_inv, Functor.whiskerLeft_comp, Category.assoc]

/-- The identifications `Rf_!^c = Rf'_!^{c'}` of the lower shrieks along the chosen
compactifications of equal morphisms are compatible with the coefficient comparisons. -/
lemma squareCompatible_shriekOfCompactification_eqToHom {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {f f' : X ⟶ Y} (hf : f = f')
    (h₁ : P.lowerShriekOfCompactification (compactificationOverField f) =
      P.lowerShriekOfCompactification (compactificationOverField f'))
    (h₂ : P'.lowerShriekOfCompactification (compactificationOverField f) =
      P'.lowerShriekOfCompactification (compactificationOverField f')) :
    NatTrans.SquareCompatible (C.shriekOfCompactification (compactificationOverField f))
      (C.shriekOfCompactification (compactificationOverField f')) (eqToHom h₁) (eqToHom h₂) := by
  subst hf
  simpa only [eqToHom_refl] using NatTrans.SquareCompatible.id _

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
