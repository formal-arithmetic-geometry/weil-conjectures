/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeRefinement

/-!
# Coefficient changes and the composition isomorphisms of the lower shriek

Let `P` be a pushforward datum for the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`). For composable `f : X ⟶ Y` and
`g : Y ⟶ S`, with chosen compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f` and
`c' = (Y ⟶[j] Z' ⟶[q] S)` of `g` and a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of `p ≫ j`
with cartesian square, the composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekComp`) is the composite
of the independence of the compactification for the composite compactification
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of the extensions by zero and of
the pushforwards, and of the inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`
(`BoundedConstructiblePushforwardData.lowerStarOpenImmersionLowerShriekExchange`).
This is the construction of `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` and
`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`, for a general pushforward
datum.

For a coefficient change `C` (`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`),
every map in this construction is compatible with the coefficient comparisons:

* the composition isomorphisms `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero
  (`...squareCompatible_openImmersionLowerShriekComp`), as conjugates of the composition
  isomorphisms of the pullbacks;
* the exchange `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` (`...squareCompatible_exchange`), the exchange
  morphism of the base change isomorphism of the extension by zero;

hence so is the composition isomorphism (`...squareCompatible_lowerShriekComp`): this is
blueprint `proposition-six-operations-change-coefficients--16`.
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

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with open immersions
`j` and `i'`: the exchange morphism, under the adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`, of
the base change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!` of the extension by zero. -/
noncomputable def lowerStarOpenImmersionLowerShriekExchange (sq : IsPullback p i' j p') :
    P.lowerStar p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙ P.lowerStar p' :=
  Adjunction.exchangeRight (P.adj p) (P.adj p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq)

end Exchange

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
compactifications: for the chosen compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f` and
`c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of `p ≫ j`
with cartesian square (`Compactification.exists_isPullback_overG_overI`), the composite of the
independence of the compactification for the composite compactification
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of `j_!` and `Rf_*`, and of the
inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
noncomputable def lowerShriekComp (f : X ⟶ Y) (g : Y ⟶ S) :
    P.lowerShriekOfCompactification (compactificationOverField (f ≫ g)) ≅
      P.lowerShriekOfCompactification (compactificationOverField f) ⋙
        P.lowerShriekOfCompactification (compactificationOverField g) :=
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := hP sqe
  have := hE hd.choose_spec
  lowerShriekOfCompactificationIso hP _ (c.overComp c' d) ≪≫
    (P.lowerShriekRefinementIso sqe (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (P.lowerStarComp d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (P.lowerStarOpenImmersionLowerShriekExchange hd.choose_spec)).symm _ ≪≫
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

section OpenImmersion

variable {X Y V : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom] (j : X ⟶ Y) (j' : Y ⟶ V) [IsOpenImmersion j.left]
  [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left]

/-- The composition isomorphisms `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero are
compatible with the coefficient comparisons (Shriek): they are the conjugates of the composition
isomorphisms of the pullbacks, with which (Pull) is compatible. -/
lemma squareCompatible_openImmersionLowerShriekComp :
    NatTrans.SquareCompatible (C.shriek (j ≫ j'))
      (Functor.pasteSquareIso (C.shriek j) (C.shriek j'))
      (boundedConstructibleOpenImmersionLowerShriekComp Λ ℓ j j').hom
      (boundedConstructibleOpenImmersionLowerShriekComp Λ' ℓ j j').hom :=
  NatTrans.SquareCompatible.conjugateEquiv_symm
    ((C.isMateSquare_shriek_pull j).comp (C.isMateSquare_shriek_pull j'))
    (C.isMateSquare_shriek_pull (j ≫ j')) (C.pull_comp j j').inv

end OpenImmersion

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p.left] [IsProper p'.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` is compatible with the coefficient
comparisons. -/
lemma squareCompatible_exchange (sq : IsPullback p i' j p') :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.push p) (C.shriek j))
      (Functor.pasteSquareIso (C.shriek i') (C.push p'))
      (P.lowerStarOpenImmersionLowerShriekExchange sq)
      (P'.lowerStarOpenImmersionLowerShriekExchange sq) :=
  NatTrans.SquareCompatible.exchangeRight (C.isMateSquare_pull_push p)
    (C.isMateSquare_pull_push p') (C.squareCompatible_openImmersionLowerShriekBaseChangeIso sq)

end Exchange

variable (hP : P.IsIsoRefinementPushforward) (hE : P.IsIsoExchange)
  (hP' : P'.IsIsoRefinementPushforward) (hE' : P'.IsIsoExchange)
  {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (f : X ⟶ Y) (g : Y ⟶ S)

/-- Blueprint `proposition-six-operations-change-coefficients--16`: **the coefficient comparison
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
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have : IsProper (d.overG ≫ c'.overG).left := by
    rw [Over.comp_left]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := hP sqe
  have := hP' sqe
  have := hE hd.choose_spec
  have := hE' hd.choose_spec
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
  have h₆ := NatTrans.SquareCompatible.whiskerLeft (C.shriek c.overI)
    ((NatTrans.SquareCompatible.associator_inv (C.shriek d.overI) (C.push d.overG)
      (C.push c'.overG)).comp
    ((NatTrans.SquareCompatible.whiskerRight (C.push c'.overG)
      (C.squareCompatible_exchange hd.choose_spec).isIso_inv).comp
    (NatTrans.SquareCompatible.associator_hom (C.push c.overG) (C.shriek c'.overI)
      (C.push c'.overG))))
  have h₇ := NatTrans.SquareCompatible.associator_inv (C.shriek c.overI) (C.push c.overG)
    (Functor.pasteSquareIso (C.shriek c'.overI) (C.push c'.overG))
  exact h₁.comp (h₂.comp (h₃.comp (h₄.comp (h₅.comp (h₆.comp h₇)))))

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
