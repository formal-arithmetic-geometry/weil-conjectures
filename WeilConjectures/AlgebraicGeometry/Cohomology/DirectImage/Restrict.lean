/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-!
# Higher direct images and restriction to an open subscheme of the base

Let `f : X ⟶ T` be a morphism of schemes and `g : T' ⟶ T` an open immersion, with base change
`f' : X' ⟶ T'` and `g' : X' ⟶ X`. Then `R^q f'_* (ℱ|_{X'}) ≅ (R^q f_* ℱ)|_{T'}`.

* Flasque `𝒪_X`-modules are acyclic for the pushforward
  (`AlgebraicGeometry.Scheme.Modules.rightAcyclic_pushforward_of_isFlasque`): on a short exact
  sequence with flasque kernel, sections are surjective over every open.
* Restriction to an open subscheme sends injective modules to flasque ones.
* Pushforward commutes with restriction to opens of the base
  (`AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso`).

Hence restriction to `X'` is an exact functor sending injectives to `f'_*`-acyclic objects, and
`R^q (f'_* ∘ (-)|_{X'}) = R^q f'_* ∘ (-)|_{X'}`, while `R^q ((-)|_{T'} ∘ f_*) = (-)|_{T'} ∘ R^q f_*`
since restriction is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules which is surjective on sections over every open is an
epimorphism. -/
lemma epi_of_forall_surjective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U, Function.Surjective (φ.app U)) : Epi φ where
  left_cancellation a b hab := by
    refine hom_ext _ _ fun U ↦ ?_
    ext x
    obtain ⟨y, rfl⟩ := h U x
    have := congrArg (fun ψ ↦ ψ.app U y) hab
    simpa using this

/-- The restriction of a flasque `𝒪_Y`-module along an open immersion is flasque. -/
lemma isFlasque_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    [TopCat.Presheaf.IsFlasque ((toAb Y).obj M).obj] :
    TopCat.Presheaf.IsFlasque ((toAb X).obj (M.restrict f)).obj :=
  ⟨fun i ↦ inferInstanceAs
    (Epi (((toAb Y).obj M).obj.map (f.opensFunctor.op.map i)))⟩

variable [HasInjectiveResolutions X.Modules]

/-- **Flasque modules are acyclic for the pushforward.** If the underlying abelian sheaf of an
`𝒪_X`-module `M` is flasque, then `R^q f_* M = 0` for all `q > 0`. Flasque modules contain the
injective ones and are stable under cokernels of monomorphisms, and the pushforward of a short
exact sequence with flasque kernel is exact on the right, its sections over every open being
surjective. -/
theorem rightAcyclic_pushforward_of_isFlasque (f : X ⟶ T) (M : X.Modules)
    [hM : TopCat.Presheaf.IsFlasque ((toAb X).obj M).obj] : (pushforward f).rightAcyclic M := by
  refine Functor.rightAcyclic_of_epi_map_g (pushforward f)
    (fun M ↦ TopCat.Presheaf.IsFlasque ((toAb X).obj M).obj)
    (fun I _ ↦ isFlasque_of_injective I) (fun S hS h₁ h₂ ↦ ?_) (fun S hS h₁ ↦ ?_) hM
  · have hS' := hS.map_of_exact (toAb X)
    have : TopCat.Presheaf.IsFlasque (S.map (toAb X)).X₁.obj := h₁
    have : TopCat.Presheaf.IsFlasque (S.map (toAb X)).X₂.obj := h₂
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS'
  · have hS' := hS.map_of_exact (toAb X)
    have : TopCat.Presheaf.IsFlasque (S.map (toAb X)).X₁.obj := h₁
    refine epi_of_forall_surjective_app _ fun V ↦ ?_
    have := TopCat.Sheaf.IsFlasque.epi_of_shortExact hS' (U := f ⁻¹ᵁ V)
    exact (AddCommGrpCat.epi_iff_surjective _).mp this

section BaseChange

variable {T' X' : Scheme.{u}} {f : X ⟶ T} {g : T' ⟶ T} {g' : X' ⟶ X} {f' : X' ⟶ T'}

omit [HasInjectiveResolutions X.Modules] in
/-- In a cartesian square whose bottom arrow `g` is an open immersion, the top arrow `g'` is an
open immersion. -/
lemma isOpenImmersion_of_isPullback [IsOpenImmersion g] (sq : IsPullback g' f' f g) :
    IsOpenImmersion g' := by
  rw [← sq.isoPullback_hom_fst]
  infer_instance

omit [HasInjectiveResolutions X.Modules] in
/-- In a cartesian square whose bottom arrow `g` is an open immersion, the range of the top arrow
`g'` is the preimage of the range of `g`. -/
lemma range_of_isPullback [IsOpenImmersion g] (sq : IsPullback g' f' f g) :
    Set.range g'.base = f.base ⁻¹' Set.range g.base := by
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ,
    IsOpenImmersion.range_pullbackFst]
  rfl

variable [IsOpenImmersion g] [IsOpenImmersion g'] (sq : IsPullback g' f' f g)

/-- The morphism of `𝒪_{T'}`-modules `(f_* M)|_{T'} ⟶ f'_* (M|_{X'})` attached to a cartesian
square whose bottom arrow `g` is an open immersion: it is induced by the unit
`M ⟶ g'_* (M|_{X'})`, the equality `g' ≫ f = f' ≫ g` and the counit `(g_* N)|_{T'} ≅ N`. -/
noncomputable def pushforwardRestrictHom :
    pushforward f ⋙ restrictFunctor g ⟶ restrictFunctor g' ⋙ pushforward f' :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (restrictAdjunction g').unit (pushforward f ⋙ restrictFunctor g) ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (restrictFunctor g')
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((pushforwardComp g' f).hom ≫ (pushforwardCongr sq.w).hom ≫
          (pushforwardComp f' g).inv) (restrictFunctor g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (pushforward f') (restrictAdjunction g).counit ≫
        (Functor.rightUnitor _).hom)

omit [HasInjectiveResolutions X.Modules] in
/-- A restriction map of a presheaf between equal opens is an isomorphism. -/
lemma isIso_presheaf_map_of_eq {Y : Scheme.{u}} (M : Y.Modules) {W W' : Y.Opens}
    (i : W' ⟶ W) (h : W = W') : IsIso (M.presheaf.map i.op) := by
  subst h
  rw [Subsingleton.elim i (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  infer_instance

omit [HasInjectiveResolutions X.Modules] in
lemma restrictFunctor_map_app {Y Z : Scheme.{u}} (h : Y ⟶ Z) [IsOpenImmersion h] {M N : Z.Modules}
    (φ : M ⟶ N) (U : Y.Opens) : ((restrictFunctor h).map φ).app U = φ.app (h ''ᵁ U) :=
  rfl

instance isIso_pushforwardRestrictHom : IsIso (pushforwardRestrictHom sq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [Hom.isIso_iff_isIso_app]
  intro V
  dsimp [pushforwardRestrictHom]
  simp only [Category.id_comp, Category.comp_id]
  have hW : f ⁻¹ᵁ (g ''ᵁ V) = g' ''ᵁ g' ⁻¹ᵁ (f ⁻¹ᵁ (g ''ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, eq_comm, inf_eq_right]
    intro x hx
    have : f.base x ∈ Set.range g.base := (g.image_le_opensRange V) hx
    exact (range_of_isPullback sq).ge this
  rw [restrictFunctor_map_app, pushforward_map_app, restrictAdjunction_unit_app_app]
  have := isIso_presheaf_map_of_eq M (homOfLE (g'.image_preimage_le _)) hW
  refine IsIso.comp_isIso' this (IsIso.comp_isIso' ?_ ?_)
  · infer_instance
  · infer_instance

/-- **The higher direct images commute with restriction to an open subscheme of the base**: in a
cartesian square whose bottom arrow `g` is an open immersion,
`R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}`.
Restriction to `X'` is exact and sends injective modules to flasque, hence `f'_*`-acyclic, ones,
restriction to `T'` is exact, and `f'_* ((-)|_{X'}) ≅ (f_* -)|_{T'}`. -/
noncomputable def higherDirectImagePullbackIsoRestrict (ℱ : X.Modules)
    [HasInjectiveResolutions X'.Modules] (q : ℕ) :
    (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ) ≅
      ((higherDirectImage f q).obj ℱ).restrict g :=
  (higherDirectImage f' q).mapIso ((restrictFunctorIsoPullback g').app ℱ).symm ≪≫
    (Functor.compRightDerivedObjIso (restrictFunctor g') (pushforward f')
      (fun I _ ↦ have := isFlasque_of_injective I
        have := isFlasque_restrict g' I
        rightAcyclic_pushforward_of_isFlasque f' _) q ℱ).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (asIso (pushforwardRestrictHom sq)).symm q ℱ ≪≫
    Functor.rightDerivedCompObjIso (pushforward f) (restrictFunctor g) q ℱ

end BaseChange

end AlgebraicGeometry.Scheme.Modules
