/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
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

/-- The generator is natural: `Λ[a]` maps the generator of `Λ[V']` to the restriction of the
generator of `Λ[V]` along `a : V' ⟶ V`. -/
lemma freeSheaf_map_freeSheafGenerator {V V' : S.Etale} (a : V' ⟶ V) :
    ((Etale.freeSheaf Λ S).map a).hom.app (op V') (freeSheafGenerator Λ V') =
      ((Etale.freeSheaf Λ S).obj V).obj.map a.op (freeSheafGenerator Λ V) := by
  rw [freeSheafGenerator, freeSheafGenerator, ← Etale.freeSheafHomEquiv_comp,
    ← Etale.freeSheafHomEquiv_map, Category.id_comp, Category.comp_id]

/-- The canonical global section of `t^* f^* Λ[V]` attached to a `T`-point `b` of `V` over `f`
(with `t : T ⟶ X`): the generator of `Λ[V]`, pulled back along `f`, and then pulled back along
the morphism `T ⟶ X ×_S V` given by `b` and `t`. -/
noncomputable def freeSheafPullbackSection {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    ((t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.freeSheaf Λ S).obj V))).obj.obj (op (Etale.finalObject T)) :=
  ModuleSheaf.pullSection t ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V))
    (V := Etale.finalObject T) (U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
    (pullback.lift b t hb) ((pullback.lift_snd _ _ _).trans (Category.id_comp t).symm)
    (Etale.pullbackSection Λ f _ V (freeSheafGenerator Λ V))

/-- The morphism `Λ ⟶ t^* f^* Λ[V]` corresponding to `freeSheafPullbackSection`. -/
noncomputable def freeSheafPullbackMap {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶
      (t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
        ((Etale.freeSheaf Λ S).obj V)) :=
  (constSheafHomEquiv Λ _).symm (freeSheafPullbackSection Λ f t V b hb)

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
  ((t)^*[ModuleCat.{u + 1} Λ].mapExtPrecomp (freeSheafPullbackMap Λ f t V b hb) F q).comp
    (DerivedCategory.Plus.shiftedHomAddEquivExt _ _ q).toAddMonoidHom

/-- **Naturality in `V`** of `cohomologyPresheafRestrict`. -/
lemma cohomologyPresheafRestrict_map {T : Scheme.{u}} (t : T ⟶ X) {V V' : S.Etale} (a : V' ⟶ V)
    (b : T ⟶ V'.left) (hb : b ≫ V'.hom = t ≫ f)
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    cohomologyPresheafRestrict Λ f F q t V' b hb
        ((Etale.higherDirectImagePresheaf Λ f q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).map a.op p) =
      cohomologyPresheafRestrict Λ f F q t V (b ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hb]) p := by
  have hsec : ((t)^*[ModuleCat.{u + 1} Λ].map ((f)^*[ModuleCat.{u + 1} Λ].map
      ((Etale.freeSheaf Λ S).map a))).hom.app _ (freeSheafPullbackSection Λ f t V' b hb) =
      freeSheafPullbackSection Λ f t V (b ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hb]) := by
    simp only [freeSheafPullbackSection]
    rw [ModuleSheaf.pullSection_naturality, Etale.pullbackSection_naturality,
      freeSheaf_map_freeSheafGenerator, ← Etale.pullbackSection_map,
      ← ModuleSheaf.pullSection_comp]
    exact ModuleSheaf.pullSection_congr _ _ _ (by apply pullback.hom_ext <;> simp) _
  have hσ : freeSheafPullbackMap Λ f t V' b hb ≫ (t)^*[ModuleCat.{u + 1} Λ].map
      ((f)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ S).map a)) =
      freeSheafPullbackMap Λ f t V (b ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hb]) := by
    apply (constSheafHomEquiv Λ _).injective
    rw [constSheafHomEquiv_comp, freeSheafPullbackMap, freeSheafPullbackMap,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hsec]
  simp only [cohomologyPresheafRestrict, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, Functor.mapExtPrecomp_apply]
  erw [DerivedCategory.Plus.shiftedHomAddEquivExt_precomp]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  exact congrArg (fun φ ↦ (Ext.mk₀ φ).comp _ (zero_add q)) hσ

end Restrict

section Stalk

variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The geometric stalk of `Hᵠ(Rf_* K)` at `s` is the fibre at `s` of the hypercohomology presheaf
`V ↦ Hᵠ(V ×_S X, K|)`, of which it is the sheafification. -/
noncomputable def presheafFiberHigherDirectImagePresheafAddEquiv (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((Scheme.pointSmallEtale s).presheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (Etale.higherDirectImagePresheaf Λ f q K) ≃+
      (Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} Λ)).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          (R+((f)_*[ModuleCat.{u + 1} Λ]).obj K)) :=
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : LocallySmall.{u} S.Etale := locallySmall_self _
  have h := Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ f q K
  have := h.1
  have := h.2
  (AddEquiv.ofBijective ((Scheme.pointSmallEtale s).presheafFiber.map
      (Etale.higherDirectImagePresheafToSheaf Λ f q K)).hom
    ((Scheme.pointSmallEtale s).toPresheafFiber_map_bijective _)).trans
    (((Scheme.pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app _).addCommGroupIsoToAddEquiv

end Stalk

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
