/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!

# Compatibility of `Rf^!` with the extension of scalars `E ⟶ ℚ̄_ℓ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `k` a field of characteristic
`p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
for the extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleToPadicAlgCl`, the functor
`ProEtale.constructibleToPadicAlgCl` typed on the categories `Dᵇc(X)⟦Λ⟧`). This file treats the
clause on `f^!` of blueprint `sk-prop-scalar-six` for the coefficient change `E ⟶ ℚ̄_ℓ`.

* **(Pull)** on bounded constructible complexes:
  `Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPullIso`.
* **(Push)** for a proper `g`: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPushHom`, an isomorphism at bounded below complexes.
* **(Shriek)** for an open immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso`), and for
  every `f`: `Rf_!^E ⋙ T_Y ≅ T_X ⋙ Rf_!^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekToPadicAlgClIso`), composed from the
  two along the chosen compactification.
* **The exchange for `f^!`**: the mate `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}` of the inverse of
  (Shriek) under the adjunctions `Rf_! ⊣ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekToPadicAlgCl`). For an open immersion
  `j` the exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_{ℚ̄_ℓ}` is an isomorphism
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl`), `j_!`
  being fully faithful and `j^*` commuting with `T` by (Pull). The exchange for `f^!` is the
  horizontal composite of the exchanges for the open and the proper part of the compactification
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl_eq`), so
  it is an isomorphism as soon as the exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_{ℚ̄_ℓ}` for the proper
  part `g` is one
  (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso`).

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` along adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` with fully faithful left adjoints is an isomorphism, provided the right
adjoints commute with `G` and `H` up to some natural isomorphism `e : H ⋙ R₂ ≅ R₁ ⋙ G`. Indeed,
at `d`, the mate is the unit of `L₂ ⊣ R₂`, then `R₂` of the isomorphism, then `R₂ H` of the
counit `ε_d` of `L₁ ⊣ R₁`; and `R₂ H ε_d ≅ G R₁ ε_d` (by `e`) is an isomorphism, `R₁ ε_d` being
the inverse of a unit. -/
theorem isIso_mateEquiv_of_isIso_unit [IsIso adj₁.unit] [IsIso adj₂.unit]
    (α : TwoSquare G L₁ L₂ H) [IsIso α.natTrans] (e : H ⋙ R₂ ≅ R₁ ⋙ G) :
    IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  have (d : B) : IsIso ((mateEquiv adj₁ adj₂ α).natTrans.app d) := by
    have : IsIso (R₁.map (adj₁.counit.app d)) := by
      have : IsIso (adj₁.unit.app (R₁.obj d) ≫ R₁.map (adj₁.counit.app d)) := by
        rw [adj₁.right_triangle_components]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adj₁.unit.app (R₁.obj d)) _
    have : IsIso ((H ⋙ R₂).map (adj₁.counit.app d)) :=
      (NatIso.isIso_map_iff e _).mpr (inferInstanceAs (IsIso (G.map (R₁.map _))))
    have : IsIso (R₂.map (H.map (adj₁.counit.app d))) := this
    simp only [mateEquiv_apply, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, rightUnitor_inv_app, leftUnitor_hom_app,
      Functor.comp_map]
    dsimp only [Functor.comp_obj]
    simp only [Category.id_comp]
    have : IsIso (α.natTrans.app (R₁.obj d)) := inferInstance
    have : IsIso (𝟙 (R₂.obj (H.obj d))) := inferInstance
    exact IsIso.comp_isIso
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section ToPadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The extension of scalars `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded constructible complexes:
the functor `ProEtale.constructibleToPadicAlgCl`, typed on the categories `Dᵇc(X)⟦Λ⟧` of the six
operations rather than on `ProEtale.PadicSubfieldConstructible` and
`ProEtale.PadicAlgClConstructible`. The two category structures agree only after unfolding their
instances, so the coefficient comparisons below are stated with this functor. -/
noncomputable def boundedConstructibleToPadicAlgCl :
    Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  constructibleToPadicAlgCl X ℓ E

lemma boundedConstructibleToPadicAlgCl_eq :
    boundedConstructibleToPadicAlgCl X ℓ E = constructibleToPadicAlgCl X ℓ E :=
  rfl

/-- The extension of scalars `T_X` on bounded constructible complexes is compatible with the
inclusions. -/
noncomputable def boundedConstructibleToPadicAlgClCompatibility :
    boundedConstructibleToPadicAlgCl X ℓ E ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived extension of scalars is a left adjoint, hence preserves zero morphisms. -/
instance : (derivedExtendScalarsToPadicAlgCl X ℓ E).PreservesZeroMorphisms :=
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)).isLeftAdjoint
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- The extension of scalars `T_X` preserves zero morphisms, as the derived extension of scalars
does. -/
instance : (boundedConstructibleToPadicAlgCl X ℓ E).PreservesZeroMorphisms where
  map_zero A B := (boundedConstructible _).ι.map_injective (by
    have h := (boundedConstructibleToPadicAlgClCompatibility X ℓ E).hom.naturality (0 : A ⟶ B)
    simp only [Functor.comp_map, Functor.map_zero, Limits.comp_zero] at h
    rw [(boundedConstructible _).ι.map_zero]
    exact (cancel_mono _).1 (h.trans (Limits.zero_comp).symm))

end ToPadicAlgCl

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### (Pull) -/

section UpperStar

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **(Pull)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`, the restriction of `ProEtale.CondensedRing.derivedPullIso`
along the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarToPadicAlgClIso :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ≅
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility Y.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end UpperStar

/-! ### (Push) for a proper morphism -/

/-- **(Push)** for the inclusion `E ⟶ ℚ̄_ℓ` is an isomorphism at bounded constructible complexes,
for a quasi-compact quasi-separated `g`: these are bounded below
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`). -/
instance isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g] :
    IsIso (Functor.whiskerLeft
      (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z)).ι
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨n, _⟩ := K.property.1.1
  exact isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E g K.obj n

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- **(Push)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and a proper
morphism `g`: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedPushHom`, which is an isomorphism at bounded below complexes
(`ProEtale.CondensedRing.isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl`). -/
noncomputable def boundedConstructibleLowerStarToPadicAlgClIso :
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl Z.left ℓ E ⋙
        boundedConstructibleLowerStar ℓ g :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility Y.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility ℓ E g) _ ≪≫
      Functor.associator _ _ _ ≪≫
      asIso (Functor.whiskerLeft _
        (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility Z.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ g).symm ≪≫
      (Functor.associator _ _ _).symm)

end LowerStar

/-! ### (Shriek) for an open immersion -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and an open
immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ≅
      boundedConstructibleToPadicAlgCl U.left ℓ E ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility U.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_{ℚ̄_ℓ}` for an open immersion `j`: the mate of the
inverse of (Shriek) under the adjunctions `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleOpenImmersionUpperStarToPadicAlgCl :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleToPadicAlgCl U.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).inv

/-- The exchange for an open immersion `j` is an isomorphism: `j_!` is fully faithful on both
sides, and `j^*` commutes with the extension of scalars by (Pull)
(`boundedConstructibleUpperStarToPadicAlgClIso`). -/
instance isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl :
    IsIso (boundedConstructibleOpenImmersionUpperStarToPadicAlgCl ℓ E j) :=
  isIso_mateEquiv_of_isIso_unit _ _ _ (boundedConstructibleUpperStarToPadicAlgClIso ℓ E j).symm

end OpenImmersion

/-! ### (Shriek) and the exchange for `f^!` -/

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- **(Shriek)** on bounded constructible complexes along a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Rf_!(c)^E ⋙ T_Y ≅ T_X ⋙ Rf_!(c)^{ℚ̄_ℓ}`, composed of (Shriek) for the open immersion `i` and
(Push) for the proper `g`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso :
    ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI) _ ≪≫
    Functor.associator _ _ _

/-- The exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_{ℚ̄_ℓ}` for the proper part `g` of a compactification:
the mate of the inverse of (Push) under the adjunctions `Rg_* ⊣ Rg^!`. -/
noncomputable def boundedConstructibleProperUpperShriekToPadicAlgCl :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
        boundedConstructibleToPadicAlgCl c.overObj.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        (boundedConstructibleLowerStar ℓ c.overG).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
    (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv

/-- The exchange `Rf^!(c)_E ⋙ T_X ⟶ T_Y ⋙ Rf^!(c)_{ℚ̄_ℓ}` along a compactification `c`: the mate
of the inverse of (Shriek) under the adjunctions `Rf_!(c) ⊣ Rf^!(c)`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl :
    ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactification ℓ E c ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperShriekOfCompactification ℓ c :=
  mateEquiv
    (ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c)
    (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E c).inv

set_option maxHeartbeats 400000 in
-- `mateEquiv_hcomp` is matched against the unfolded adjunction `Rf_!(c) ⊣ Rf^!(c)`.
/-- The exchange for `f^!` along a compactification `c = (X ⟶[i] Z ⟶[g] Y)` is the horizontal
composite of the exchange for the proper part `g` and of the exchange for the open immersion `i`:
the mates of a vertical composite of squares are the horizontal composite of the mates
(`CategoryTheory.mateEquiv_hcomp`). -/
lemma boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl_eq :
    boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E c =
      TwoSquare.hComp (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E c)
        (boundedConstructibleOpenImmersionUpperStarToPadicAlgCl ℓ E c.overI) := by
  have h : (boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E c).inv =
      TwoSquare.vComp (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI).inv
        (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv := by
    ext K
    simp [boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso, TwoSquare.vComp]
  unfold boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl
  rw [h]
  exact mateEquiv_hcomp
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj E) ℓ c.overI)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
    (Adjunction.ofIsLeftAdjoint
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG))
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar ℓ c.overG))
    (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI).inv
    (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv

/-- The exchange for `f^!` along a compactification `c` is an isomorphism as soon as the exchange
for its proper part is one, the exchange for the open immersion being an isomorphism. -/
lemma isIso_boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl
    [IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E c)] :
    IsIso (boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E c) := by
  rw [boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl_eq]
  unfold TwoSquare.hComp
  infer_instance

end OfCompactification

variable (f : X ⟶ Y)

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Rf_!^E ⋙ T_Y ≅ T_X ⋙ Rf_!^{ℚ̄_ℓ}`, along the chosen compactification. -/
noncomputable def boundedConstructibleLowerShriekToPadicAlgClIso :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleLowerShriek ℓ f :=
  boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E (compactificationOverField f)

/-- **The exchange for `f^!`**, for the inclusion `E ⟶ ℚ̄_ℓ`: the canonical natural transformation
`Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekToPadicAlgClIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekToPadicAlgCl :
    ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperShriek ℓ f :=
  mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv

/-- The exchange for `f^!` as the mate of a two-square. -/
lemma boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv :
    boundedConstructibleUpperShriekToPadicAlgCl ℓ E f =
      (mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
        (boundedConstructibleUpperShriekAdjunction ℓ f)
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv)).natTrans :=
  rfl

/-- The exchange for `f^!` is an isomorphism as soon as the exchange for the proper part of the
chosen compactification is one. -/
lemma isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso
    [IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E (compactificationOverField f))] :
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) :=
  isIso_boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E _

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-exceptional` (`sk-prop-scalar-six`), the clause on `f^!` for the coefficient
change `E ⟶ ℚ̄_ℓ`. The canonical comparison `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}` (the mate of
the lower-shriek comparison) is an isomorphism on bounded constructible complexes. Its open
half is proved (`isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl`); the proper
half is the content of the node. -/
theorem isIso_boundedConstructibleUpperShriekToPadicAlgCl :
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) :=
  sorry

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
