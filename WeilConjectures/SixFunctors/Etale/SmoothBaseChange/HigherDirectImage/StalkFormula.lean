/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Stalks of higher direct images at geometric points

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `F` an étale sheaf of `Λ`-modules on `X`
and `s : Spec Ω ⟶ S` a geometric point. Then the geometric stalk of `R^q f_* F` at `s` is the
étale cohomology `H^q(S_(s) ×_S X, F|)` of the base change of `X` to the strict localization
`S_(s)` of `S` at `s` ([Stacks, Tag 03Q9], blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`).

The proof follows the blueprint: `R^q f_* F` is the sheafification of the presheaf
`V ↦ H^q(V ×_S X, F|)`, so its stalk is the colimit of `H^q(V ×_S X, F|)` over the pointed étale
neighbourhoods `V` of `s`. The affine neighbourhoods are cofinal, `S_(s) ×_S X` is the limit of
the `V ×_S X` (`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConePullback`) and the
continuity of étale cohomology
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`)
identifies the colimit of the cohomology groups with the cohomology of the limit.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_geometricStalk_higherDirectImage_addEquiv`: the stalk
  formula `(R^q f_* F)_s ≅ H^q(S_(s) ×_S X, F|)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]


section GlobalSections

variable {T : Scheme.{u}}

/-- Maps out of the constant sheaf `Λ` on `T_ét` are global sections. -/
noncomputable def constSheafHomEquiv (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) ≃
      G.obj.obj (op (Etale.finalObject T)) :=
  ((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv
    _ _).trans (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv)

lemma constSheafHomEquiv_comp {G G' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) (ψ : G ⟶ G') :
    constSheafHomEquiv Λ G' (φ ≫ ψ) = ψ.hom.app _ (constSheafHomEquiv Λ G φ) := by
  simp only [constSheafHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

end GlobalSections

section Restrict

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The generating section of the free sheaf `Λ[V]` over `V`. -/
noncomputable def freeSheafGenerator (V : S.Etale) : ((Etale.freeSheaf Λ S).obj V).obj.obj (op V) :=
  Etale.freeSheafHomEquiv Λ V _ (𝟙 _)

/-- For `t : T ⟶ X` and a `T`-point `b : T ⟶ V` of an étale `S`-scheme `V` over `f`, the
section map `T ⟶ (V ×_S X) ×_X T` over `T`. -/
noncomputable def pullbackPullbackSectionHom {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    Etale.finalObject T ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.lift b t hb) (𝟙 T)
    ((pullback.lift_snd b t hb).trans (Category.id_comp t).symm)) (pullback.lift_snd _ _ _)

/-- The canonical global section of `t^* f^* Λ[V]` attached to a `T`-point `b` of `V` over `f`:
the generator of `Λ[V]`, pulled back along `f` and `t`, and restricted along the section
`T ⟶ (V ×_S X) ×_X T`. -/
noncomputable def freeSheafPullbackSection {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    ((t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.freeSheaf Λ S).obj V))).obj.obj (op (Etale.finalObject T)) :=
  ((t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.freeSheaf Λ S).obj V))).obj.map (pullbackPullbackSectionHom f t V b hb).op
    (Etale.pullbackSection Λ t _ _ (Etale.pullbackSection Λ f _ V (freeSheafGenerator Λ V)))

variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)

/-- The restriction of a section `Hᵠ(V ×_S X, F|)` of the cohomology presheaf to a `T`-point
`b` of `V` over `f`: a class `f^* Λ[V] ⟶ F[q]` is pulled back along `t : T ⟶ X` and evaluated
at the canonical section of `t^* f^* Λ[V]`. -/
noncomputable def cohomologyPresheafRestrict {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    (Etale.higherDirectImagePresheaf Λ f q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V) →+
      Ext (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)
        ((t)^*[ModuleCat.{u + 1} Λ].obj F) q :=
  ((Ext.mk₀ ((constSheafHomEquiv Λ _).symm (freeSheafPullbackSection Λ f t V b hb))).precomp
      _ (zero_add q)).comp
    (((t)^*[ModuleCat.{u + 1} Λ].mapExtAddHom _ _ q).comp
      (DerivedCategory.Plus.shiftedHomAddEquivExt _ _ q).toAddMonoidHom)

end Restrict

/-- **Strict-henselization stalk formula** (blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`): for a quasi-compact quasi-separated
`f : X ⟶ S`, a sheaf `F` of `Λ`-modules on `X_ét` and a geometric point `s : Spec Ω ⟶ S`, the
geometric stalk of `R^q f_* F` at `s` is the étale cohomology `H^q(S_(s) ×_S X, F|)` of the base
change of `X` to the strict localization `S_(s)`. -/
@[stacks 03Q9]
theorem nonempty_geometricStalk_higherDirectImage_addEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty ((Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} Λ)).obj
        (Etale.higherDirectImage Λ f q F) ≃+
      Ext (SemiSimplicialObject.constSheaf
          (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj F) q) :=
  sorry

end AlgebraicGeometry.Etale
