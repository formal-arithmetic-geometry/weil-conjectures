/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.OpenSquare
public import WeilConjectures.TraceFormula.ProperPushforward
public import WeilConjectures.TraceFormula.Stalk

/-!

# The curve pieces of a Weil object at a fixed point

Let `(K, φ)` be a Weil object on `X` for `Φ`, let `m ≥ 1` and let `x : s ⟶ X` be a rational
point fixed by `Φ_m`, with complement `j : U ⟶ X` (an open immersion with
`Φ_{m,U} ≫ j = j ≫ Φ_m` cartesian). The *curve pieces* of `K` at `x` (blueprint
`d-curve-pieces`, `sk-d-curve-pieces`) are
```
K^Z = Rx_* Lx^* K,        K^U = j_! Lj^* K,
```
the outer terms of the open–closed triangle `K^U ⟶ K ⟶ K^Z ⟶`. They carry coefficient maps for
the graph correspondence `(𝟙, Φ_m)`:

* `u^Z = [x, x]_! F_{x,m}`, the proper pushforward along the diagram `(x, x)` of the point
  correspondence `(s, 𝟙, 𝟙)` with coefficient the local Frobenius `F_{x,m}`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.closedPieceCoeff`);
* `u^U : LΦ_m^* j_! Lj^* K ≅ j_! LΦ_{m,U}^* Lj^* K ≅ j_! Lj^* LΦ_m^* K ⟶ j_! Lj^* K`,
  open base change followed by `φ_m`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.openPieceCoeff`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- The mate of a natural transformation `G ⋙ L₂ ⟶ L₁ ⋙ G` which is the identity up to
identifications `e₁ : L₁ ≅ 𝟭` and `e₂ : L₂ ≅ 𝟭` is the identity up to the conjugate
identifications `R₁ ≅ 𝟭` and `R₂ ≅ 𝟭`. -/
lemma mateEquiv_app_eq_of_iso_id {C D : Type*} [Category* C] [Category* D] {L₁ R₁ : C ⥤ C}
    {L₂ R₂ : D ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ 𝟭 C) (e₂ : L₂ ≅ 𝟭 D)
    (G : C ⥤ D) (α : TwoSquare G L₁ L₂ G)
    (hα : ∀ X, α.natTrans.app X = e₂.hom.app (G.obj X) ≫ G.map (e₁.inv.app X)) (X : C) :
    (mateEquiv adj₁ adj₂ α).natTrans.app X =
      G.map ((conjugateIsoEquiv adj₁ Adjunction.id e₁.symm).hom.app X) ≫
        (conjugateIsoEquiv adj₂ Adjunction.id e₂.symm).inv.app (G.obj X) := by
  have h := ((conjugateIsoEquiv adj₂ Adjunction.id e₂.symm).inv.naturality
    (G.map (e₁.inv.app (R₁.obj X) ≫ adj₁.counit.app X)))
  simp only [conjugateIsoEquiv, conjugateEquiv, mateEquiv_apply, Adjunction.id, Iso.symm_hom,
    Iso.symm_inv, Equiv.coe_fn_mk] at h ⊢
  simpa [hα] using h.symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- A rational point `x : s ⟶ X` is a closed immersion, being a section of the structure
morphism. -/
instance isClosedImmersion_rationalPoint_left (x : RationalPoint X) : IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)

/-! ### Squares with identity exceptional legs -/

section IdSquare

variable (ℓ) {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom] (f : P ⟶ X) [IsProper f.left]

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Abstract form of the last step of `lowerStarLowerShriekCompIso_hom_app_of_id`. -/
lemma lowerStarLowerShriekCompIso_hom_app_of_id_aux {C D : Type*} [Category* C] [Category* D]
    {A : D ⥤ D} (e : A ≅ 𝟭 D) {F G : C ⥤ D} (ι : F ≅ G) {K K' : C} (b : K ⟶ K') :
    A.map (ι.inv.app K) ≫ e.hom.app (F.obj K) ≫ F.map b ≫ ι.hom.app K' =
      e.hom.app (G.obj K) ≫ G.map b := by
  simp

/-- The composition isomorphism `Ξ : R(𝟙 X)_! Rf_* ≅ Rf_* R(𝟙 P)_!` of the square
`f ≫ 𝟙 = 𝟙 ≫ f` is the identity, up to the identifications `R(𝟙)_! ≅ 𝟭`. -/
lemma lowerStarLowerShriekCompIso_hom_app_of_id (w : f ≫ 𝟙 X = 𝟙 P ≫ f)
    (K : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerStarLowerShriekCompIso ℓ w).hom.app K =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
          ((boundedConstructibleLowerStar ℓ f).obj K) ≫
        (boundedConstructibleLowerStar ℓ f).map
          ((boundedConstructibleLowerShriekId ℓ P).inv.app K) := by
  have h₁ : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 X)).inv.app K =
      (boundedConstructibleLowerShriekId ℓ X).hom.app _ ≫
        eqToHom (by rw [Category.comp_id]; rfl) := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 X)).hom.app K),
      Iso.hom_inv_id_app, boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
      ← Category.assoc,
      boundedConstructibleLowerShriekComp_padicAlgCl_id_right ℓ f K, eqToHom_trans, eqToHom_refl]
  have h₂ : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 P) f).hom.app K =
      eqToHom (by rw [Category.id_comp]; rfl) ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleLowerShriekId ℓ P).inv.app K) := by
    rw [← cancel_mono ((boundedConstructibleLowerShriek ℓ f).map
      ((boundedConstructibleLowerShriekId ℓ P).hom.app K)), Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id,
      boundedConstructibleLowerShriekId,
      Iso.trans_hom, NatTrans.comp_app]
    exact boundedConstructibleLowerShriekComp_padicAlgCl_id_left ℓ f K
  simp only [lowerStarLowerShriekCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, eqToIso.hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.comp_obj, h₁, h₂,
    Category.assoc, eqToHom_refl, Category.id_comp]
  exact lowerStarLowerShriekCompIso_hom_app_of_id_aux _ _ _

/-- The exchange map `E : Rf_* R(𝟙 P)^! ⟶ R(𝟙 X)^! Rf_*` of the square `f ≫ 𝟙 = 𝟙 ≫ f` is the
identity, up to the identifications `R(𝟙)^! ≅ 𝟭`: the exceptional half of a coefficient
pushforward with identity exceptional legs is the identity (blueprint `d-curve-pieces`). Applied
to the diagram `(x, x)` of `closedPieceDiagram` it gives `u^Z = Rx_* F_{x,m} ∘ γ`. -/
lemma lowerStarUpperShriekExchange_app_of_id (w : f ≫ 𝟙 X = 𝟙 P ≫ f)
    (K : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerStarUpperShriekExchange ℓ w).app K =
      (boundedConstructibleLowerStar ℓ f).map
          ((boundedConstructibleUpperShriekId ℓ P).hom.app K) ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app
          ((boundedConstructibleLowerStar ℓ f).obj K) :=
  mateEquiv_app_eq_of_iso_id
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 P))
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    (boundedConstructibleLowerShriekId ℓ P) (boundedConstructibleLowerShriekId ℓ X) _ _
    (lowerStarLowerShriekCompIso_hom_app_of_id ℓ f w) K

end IdSquare

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)

/-! ### The closed piece -/

/-! ### The open piece -/

variable {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
