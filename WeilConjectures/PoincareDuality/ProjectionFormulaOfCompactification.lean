/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionRestrict
public import WeilConjectures.PoincareDuality.ProjectionFormula

/-!

# The exceptional projection morphism of a compactification on bounded constructible complexes

For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, the exceptional projection morphism
`PF^c_{K,B} : Rf_!^c K ⊗ᴸ B ⟶ Rf_!^c (K ⊗ᴸ Lf^* B)` is defined on the ambient derived categories
(`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification`). This file expresses
its restriction to bounded constructible `ℚ̄_ℓ`-complexes through the adjunctions
`Lp^* ⊣ Rp_*` and `i_! ⊣ Li^*` of bounded constructible complexes: it is the projection morphism
of `Lp^* ⊣ Rp_*` at `i_! K`, followed by `Rp_*` of the inverse of the projection comparison of
`i_! ⊣ Li^*` and of the composition isomorphism `Lf^* ≅ Lp^* ⋙ Li^*`
(`ProEtale.CondensedRing.homMk_exceptionalProjectionMorphismOfCompactification_eq`).

## Implementation notes

The definition of the exceptional projection morphism is first unfolded for a general coefficient
ring (`ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_eq_adjunction`):
for the coefficient ring `ℚ̲̄_ℓ`, comparing it with re-elaborated terms is prohibitively
expensive.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The projection comparison of `Dj_! ⊣ Lj^*` is an isomorphism
(`ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`). -/
instance isIso_derivedOpenImmersionProjectionComparison {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).projectionComparison
      M N) :=
  isIso_openImmersionProjectionComparison Λ j M N

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y} (c : Compactification f.left)

/-- The identification `Lf^* ≅ Lp^* ⋙ Li^*` of a compactification `c` of a morphism `f` over
`S`, through the morphisms `c.overI` and `c.overG` over `S`. -/
noncomputable def leftDerivedUpperStarOverCompactificationIso :
    L((f.left)^*⟦Λ⟧) ≅ L((c.overG.left)^*⟦Λ⟧) ⋙ L((c.overI.left)^*⟦Λ⟧) :=
  leftDerivedUpperStarCompactificationIso Λ c

/-- The exceptional projection morphism of a compactification of a morphism over `S`, written
with the adjunctions `Lp^* ⊣ Rp_*` and `Di_! ⊣ Li^*`. -/
lemma exceptionalProjectionMorphismOfCompactification_eq_adjunction
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))) :
    exceptionalProjectionMorphismOfCompactification Λ c K B =
      (derivedUpperStarLowerStarAdjunction Λ c.overG.left).projectionMorphism
          ((D((c.overI.left)_!open⟦Λ⟧)).obj K) B ≫
        (R((c.overG.left)_*⟦Λ⟧)).map
          (inv ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
              c.overI.left).projectionComparison K ((L((c.overG.left)^*⟦Λ⟧)).obj B)) ≫
            (D((c.overI.left)_!open⟦Λ⟧)).map
              (K ◁ (leftDerivedUpperStarOverCompactificationIso Λ c).inv.app B)) := by
  unfold exceptionalProjectionMorphismOfCompactification properProjectionMorphism
    leftDerivedUpperStarOverCompactificationIso
    openImmersionProjectionComparison
  rfl

end General

section GenericIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- On the ambient derived category, the inverse of the composition isomorphism of the derived
pullbacks on bounded constructible complexes is that of `leftDerivedUpperStarComp`. -/
lemma ι_map_boundedConstructibleUpperStarComp_inv_app {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (i : X ⟶ Z) (g : Z ⟶ Y)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructible _).ι.map ((boundedConstructibleUpperStarComp Λ ℓ i g).inv.app B) =
      (leftDerivedUpperStarComp Λ i.left g.left).inv.app B.obj := by
  simp only [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso, Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp
  erw [Category.id_comp]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- The composition isomorphism `Lf^* ≅ Lg^* ⋙ Li^*` along `f = i ≫ g` on bounded constructible
complexes is that of the ambient derived categories. -/
lemma ι_map_eqToIso_trans_boundedConstructibleUpperStarComp_inv_app {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (i : X ⟶ Z) (g : Z ⟶ Y) (w : i ≫ g = f) (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructible _).ι.map
      ((eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w.symm) ≪≫
        boundedConstructibleUpperStarComp Λ ℓ i g).inv.app B) =
      (eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h.left)^*⟦Λ⟧)) w.symm) ≪≫
        leftDerivedUpperStarComp Λ i.left g.left).inv.app B.obj := by
  subst w
  simp only [eqToIso_refl, Iso.refl_trans]
  exact ι_map_boundedConstructibleUpperStarComp_inv_app Λ ℓ i g B

/-- `leftDerivedUpperStarOverCompactificationIso` as an `eqToIso` followed by the composition
isomorphism. -/
lemma leftDerivedUpperStarOverCompactificationIso_eq (c : Compactification f.left) :
    leftDerivedUpperStarOverCompactificationIso Λ c =
      eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h.left)^*⟦Λ⟧)) c.overI_overG.symm) ≪≫
        leftDerivedUpperStarComp Λ c.overI.left c.overG.left :=
  rfl


end GenericIso

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The projection comparison of `j_! ⊣ Lj^*` on bounded constructible complexes is that of the
ambient derived categories. -/
lemma boundedConstructibleOpenImmersionProjectionComparison_hom (M : Dᵇc(U.left)⟦𝐐⟧)
    (N : Dᵇc(X.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).projectionComparison
        M N) =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j.left).projectionComparison
        M.obj N.obj :=
  Adjunction.ι_map_projectionComparison_restrictFullyFaithful _ _ _ M N

/-- The projection comparison of `j_! ⊣ Lj^*` on bounded constructible `ℚ̄_ℓ`-complexes is an
isomorphism: the derived projection formula for the extension by zero. -/
instance isIso_boundedConstructibleOpenImmersionProjectionComparison (M : Dᵇc(U.left)⟦𝐐⟧)
    (N : Dᵇc(X.left)⟦𝐐⟧) :
    IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
      j).projectionComparison M N) := by
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        j).projectionComparison M N)) := by
    rw [boundedConstructibleOpenImmersionProjectionComparison_hom]
    infer_instance
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

lemma ι_map_boundedConstructibleOpenImmersionLowerShriek_map {K K' : Dᵇc(U.left)⟦𝐐⟧}
    (φ : K ⟶ K') :
    (boundedConstructible _).ι.map ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).map φ) =
      (D((j.left)_!open⟦_⟧)).map ((boundedConstructible _).ι.map φ) :=
  rfl

end OpenImmersion

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Z ⟶ Y)

/-- The projection morphism of `Lg^* ⊣ Rg_*` on bounded constructible complexes is that of the
ambient derived categories. -/
lemma boundedConstructibleProjectionMorphism_hom (A : Dᵇc(Z.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).projectionMorphism A B) =
      (derivedUpperStarLowerStarAdjunction _ g.left).projectionMorphism A.obj B.obj :=
  Adjunction.ι_map_projectionMorphism_restrictFullyFaithful _ _ _ A B

lemma ι_map_boundedConstructibleLowerStar_map {A A' : Dᵇc(Z.left)⟦𝐐⟧} (φ : A ⟶ A') :
    (boundedConstructible _).ι.map ((boundedConstructibleLowerStar ℓ g).map φ) =
      (R((g.left)_*⟦_⟧)).map ((boundedConstructible _).ι.map φ) :=
  rfl

end LowerStar

lemma ι_map_whiskerLeft {W : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsSeparated W.hom] (A : Dᵇc(W.left)⟦𝐐⟧) {M N : Dᵇc(W.left)⟦𝐐⟧} (φ : M ⟶ N) :
    (boundedConstructible _).ι.map (A ◁ φ) = A.obj ◁ (boundedConstructible _).ι.map φ :=
  rfl

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

set_option profiler true in
/-- **The exceptional projection morphism of a compactification on bounded constructible
complexes**: for a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, `PF^c_{K,B}` is the
projection morphism of `Lp^* ⊣ Rp_*` at `i_! K`, followed by `Rp_*` of the inverse of the
projection comparison of `i_! ⊣ Li^*` and of `Li^* Lp^* ≅ Lf^*`. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_eq (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧)
    (ε : (boundedConstructibleUpperStar _ ℓ c.overI).obj
      ((boundedConstructibleUpperStar _ ℓ c.overG).obj B) ⟶ (boundedConstructibleUpperStar _ ℓ f).obj B)
    (hε : (boundedConstructible _).ι.map ε =
      (leftDerivedUpperStarOverCompactificationIso _ c).inv.app B.obj) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ c.overG).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).obj K) B ≫
        (boundedConstructibleLowerStar ℓ c.overG).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              c.overI).projectionComparison K
              ((boundedConstructibleUpperStar _ ℓ c.overG).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).map
              (K ◁ ε)) := by
  refine (ObjectProperty.fullyFaithfulι (boundedConstructible _)).map_injective ?_
  conv_lhs => rw [ObjectProperty.ι_map, ObjectProperty.homMk_hom,
    exceptionalProjectionMorphismOfCompactification_eq_adjunction]
  conv_rhs =>
    rw [Functor.map_comp, boundedConstructibleProjectionMorphism_hom,
      ι_map_boundedConstructibleLowerStar_map, Functor.map_comp, Functor.map_inv]
    simp only [boundedConstructibleOpenImmersionProjectionComparison_hom]
    rw [ι_map_boundedConstructibleOpenImmersionLowerShriek_map]
    simp only [ι_map_whiskerLeft, hε]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
