/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePasting

/-!
# Coefficient changes and the independence of the lower shriek from the compactification

Let `C` be a coefficient change `Λ ⟶ Λ'` of the bounded constructible six functors
(`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`). For a refinement `h : Z ⟶ Z₁`
of compactifications `X ⟶[i] Z ⟶[p] Y` and `X ⟶[i₁] Z₁ ⟶[p₁] Y`, the comparisons along the
refinement of `CompactificationIndependence` are compatible with the coefficient comparisons of
`C`:

* the restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*`, an exchange morphism for the adjunctions
  `i_! ⊣ Li^*` and `i₁_! ⊣ Li₁^*`
  (`...squareCompatible_openImmersionLowerShriekRefinement`);
* the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*`
  (`...squareCompatible_openImmersionLowerShriekRefinementPushforward`);
* the isomorphism `Rf_!^{c₁} ≅ Rf_!^c` (`...squareCompatible_lowerShriekRefinementIso`) and the
  isomorphisms `Rf_!^{c₁} ≅ Rf_!^{c₂}` through a common refinement
  (`...squareCompatible_lowerShriekRefinementIso_trans_symm`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {ℓ : ℕ} [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` along a refinement is the exchange morphism of
the triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` for the adjunctions `i₁_! ⊣ Li₁^*` and
`i_! ⊣ Li^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft (w : i ≫ h = i₁) :
    boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w =
      Adjunction.exchangeLeft (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
        (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ ℓ w) := by
  unfold boundedConstructibleOpenImmersionLowerShriekRefinement
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep
    boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep Adjunction.exchangeLeft
  rfl

namespace BoundedConstructibleCoefficientChange

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  [IsFinitenessCoefficient ℓ Λ] [IsFinitenessCoefficient ℓ Λ']
  (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ k)

/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` along a refinement is compatible with the
coefficient comparisons. -/
lemma squareCompatible_openImmersionLowerShriekRefinement (w : i ≫ h = i₁) :
    NatTrans.SquareCompatible (C.shriek i) (Functor.pasteSquareIso (C.shriek i₁) (C.pull h))
      (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w)
      (boundedConstructibleOpenImmersionLowerShriekRefinement Λ' ℓ w) := by
  have hθ := (NatTrans.SquareCompatible.rightUnitor_hom (C.pull i₁)).comp
    ((C.squareCompatible_eqToHom w.symm (by rw [w]) (by rw [w])).comp (C.pull_comp i h))
  have hθ' : NatTrans.SquareCompatible
      (Functor.pasteSquareIso (C.pull i₁) (Functor.idSquareIso (C.T X)))
      (Functor.pasteSquareIso (C.pull h) (C.pull i))
      (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom
      (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ' ℓ w).hom := by
    simpa only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso.hom]
      using hθ
  have h := NatTrans.SquareCompatible.exchangeLeft (ιH := Functor.idSquareIso (C.T X))
    (C.isMateSquare_shriek_pull i₁) (C.isMateSquare_shriek_pull i) hθ'
  rw [boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft,
    boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft]
  exact NatTrans.SquareCompatible.of_pasteSquareIso_idSquareIso h

/-- The pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` along a refinement with cartesian square is
compatible with the coefficient comparisons. -/
lemma squareCompatible_openImmersionLowerShriekRefinementPushforward [IsProper h.left]
    (sq : IsPullback (𝟙 X) i i₁ h) :
    NatTrans.SquareCompatible (C.shriek i₁) (Functor.pasteSquareIso (C.shriek i) (C.push h))
      (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)
      (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ' ℓ sq) := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ' ℓ sq
  exact (NatTrans.SquareCompatible.rightUnitor_inv _).comp
    ((NatTrans.SquareCompatible.whiskerLeft _
      (NatTrans.SquareCompatible.unit (C.isMateSquare_pull_push h))).comp
    ((NatTrans.SquareCompatible.associator_inv _ _ _).comp
    (NatTrans.SquareCompatible.whiskerRight _
      (C.squareCompatible_openImmersionLowerShriekRefinement
        sq.toCommSq.snd_comp_eq_of_fst_eq_id).isIso_inv)))

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- (Push) is compatible with the identifications `Rp_* = Rp'_*` for equal proper morphisms. -/
lemma squareCompatible_push_eqToHom {p p' : Z ⟶ Y} [IsProper p.left] [IsProper p'.left]
    (hp : p = p')
    (h₁ : boundedConstructibleLowerStar Λ ℓ p = boundedConstructibleLowerStar Λ ℓ p')
    (h₂ : boundedConstructibleLowerStar Λ' ℓ p = boundedConstructibleLowerStar Λ' ℓ p') :
    NatTrans.SquareCompatible (C.push p) (C.push p') (eqToHom h₁) (eqToHom h₂) := by
  subst hp
  simpa only [eqToHom_refl] using NatTrans.SquareCompatible.id (C.push p)

/-- (Push) is compatible with the composition isomorphisms `Rh_* ⋙ Rp_* ≅ R(h ≫ p)_*`, the
conjugates of the composition isomorphisms of the pullbacks. -/
lemma squareCompatible_lowerStarComp {p : Z₁ ⟶ Y} [IsProper h.left] [IsProper p.left]
    [IsProper (h ≫ p).left] :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.push h) (C.push p)) (C.push (h ≫ p))
      (boundedConstructibleLowerStarComp Λ ℓ h p).hom
      (boundedConstructibleLowerStarComp Λ' ℓ h p).hom :=
  NatTrans.SquareCompatible.conjugateEquiv
    ((C.isMateSquare_pull_push p).comp (C.isMateSquare_pull_push h))
    (C.isMateSquare_pull_push (h ≫ p)) (C.pull_comp h p)

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement is compatible with the
coefficient comparisons. -/
lemma squareCompatible_lowerShriekRefinementIso [IsProper h.left] (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} [IsProper p₁.left] [IsProper p.left] (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ' ℓ sq)] :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.shriek i₁) (C.push p₁))
      (Functor.pasteSquareIso (C.shriek i) (C.push p))
      (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp).hom
      (boundedConstructibleLowerShriekRefinementIso Λ' ℓ sq wp).hom := by
  have : IsProper (h ≫ p₁).left := by
    rw [Over.comp_left]
    infer_instance
  have h₁ := (NatTrans.SquareCompatible.whiskerRight (C.push p₁)
      (C.squareCompatible_openImmersionLowerShriekRefinementPushforward sq)).comp
    ((NatTrans.SquareCompatible.associator_hom _ _ _).comp
    (NatTrans.SquareCompatible.whiskerLeft (C.shriek i)
      ((C.squareCompatible_lowerStarComp (h := h) (p := p₁)).comp
      (C.squareCompatible_push_eqToHom wp (by rw [wp]) (by rw [wp])))))
  simpa only [boundedConstructibleLowerShriekRefinementIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, asIso_hom, eqToIso.hom,
    Functor.whiskerLeft_comp] using h₁

section Independence

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The isomorphism `Rf_!^{c₁} ≅ Rf_!^{c₂}` through a common refinement `c` of `c₁` and `c₂` is
compatible with the coefficient comparisons. -/
lemma squareCompatible_lowerShriekRefinementIso_trans_symm {c c₁ c₂ : Compactification f.left}
    (r₁ : c.OverRefinement c₁) (r₂ : c.OverRefinement c₂)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ r₁.isPullback)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ' ℓ r₁.isPullback)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ r₂.isPullback)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ' ℓ
      r₂.isPullback)] :
    NatTrans.SquareCompatible (C.shriekOfCompactification c₁) (C.shriekOfCompactification c₂)
      (boundedConstructibleLowerShriekRefinementIso Λ ℓ r₁.isPullback r₁.hom_overG ≪≫
        (boundedConstructibleLowerShriekRefinementIso Λ ℓ r₂.isPullback r₂.hom_overG).symm).hom
      (boundedConstructibleLowerShriekRefinementIso Λ' ℓ r₁.isPullback r₁.hom_overG ≪≫
        (boundedConstructibleLowerShriekRefinementIso Λ' ℓ r₂.isPullback r₂.hom_overG).symm).hom := by
  have := r₁.isProper
  have := r₂.isProper
  exact (C.squareCompatible_lowerShriekRefinementIso r₁.isPullback r₁.hom_overG).comp
    (C.squareCompatible_lowerShriekRefinementIso r₂.isPullback r₂.hom_overG).inv

end Independence

section BaseChange

variable {Y X' Y' : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The compact-support base change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c₂}`, the pasting
for a compactification `c` of `f` followed by the identification of the lower shriek of the base
change of `c` with that of a compactification `c₂` of `f'` through a common refinement, is
compatible with the coefficient comparisons. -/
lemma squareCompatible_lowerShriekBaseChange (sq : IsPullback g' f' f g)
    (c : Compactification f.left) {c₀ c₂ : Compactification f'.left}
    (r₁ : c₀.OverRefinement (c.ofIsPullback sq.overLeft)) (r₂ : c₀.OverRefinement c₂)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ r₁.isPullback)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ' ℓ r₁.isPullback)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ r₂.isPullback)]
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ' ℓ
      r₂.isPullback)] :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.shriekOfCompactification c) (C.pull g))
      (Functor.pasteSquareIso (C.pull g') (C.shriekOfCompactification c₂))
      (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting Λ ℓ c sq ≫
        Functor.whiskerLeft _
          (boundedConstructibleLowerShriekRefinementIso Λ ℓ r₁.isPullback r₁.hom_overG ≪≫
            (boundedConstructibleLowerShriekRefinementIso Λ ℓ r₂.isPullback r₂.hom_overG).symm).hom)
      (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting Λ' ℓ c sq ≫
        Functor.whiskerLeft _
          (boundedConstructibleLowerShriekRefinementIso Λ' ℓ r₁.isPullback r₁.hom_overG ≪≫
            (boundedConstructibleLowerShriekRefinementIso Λ' ℓ r₂.isPullback
              r₂.hom_overG).symm).hom) :=
  (C.squareCompatible_lowerShriekOfCompactificationBaseChangePasting c sq).comp
    (NatTrans.SquareCompatible.whiskerLeft (C.pull g')
      (C.squareCompatible_lowerShriekRefinementIso_trans_symm r₁ r₂))

end BaseChange

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
