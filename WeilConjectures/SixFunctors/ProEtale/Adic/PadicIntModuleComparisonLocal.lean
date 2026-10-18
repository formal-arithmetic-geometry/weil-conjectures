/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowGLLift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Local triviality of pro-étale towers of `ℤ_ℓ,X`-modules coming from free `ℤ/ℓⁿ`-sheaves

Let `F` be a sheaf of `Λ`-modules on `X_proét` and `gᵢ : Wᵢ ⟶ X` a pro-étale cover such that each
pullback `gᵢ^* F` is the constant sheaf of a `Λ`-module which is, as an abelian group, isomorphic
to `(ℤ/ℓⁿ)^r`. Then the underlying abelian sheaf of `F` is pro-étale locally isomorphic to
`(ℤ/ℓⁿ)_X^r`, in the form of the hypothesis `hloc` of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit`
(`AlgebraicGeometry.ProEtale.exists_sieve_nonempty_isoPresheaf_zmodPowAbSheafDiagramPow`).

The ingredients are:

* the slice `X_proét / W` of the small pro-étale site over `W : X_proét` maps to `W_proét`
  (`AlgebraicGeometry.Scheme.ProEt.overToLocalization`), compatibly with the localization functor,
  so that isomorphisms of the restrictions along the localization functor give isomorphisms of the
  restrictions to the slice (`AlgebraicGeometry.ProEtale.overPullbackIsoOfLocalizationRestrictionIso`);
* local isomorphisms over the members of a pro-étale cover of `X` give local isomorphisms over any
  object, by base change (`AlgebraicGeometry.ProEtale.exists_sieve_nonempty_isoPresheaf_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} (W : X.ProEt)

/-- An object `T ⟶ W` of the slice `X_proét / W` is weakly étale over `W`. -/
lemma weaklyEtale_hom_left (T : Over W) : WeaklyEtale T.hom.left :=
  MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) T.hom.left W.hom W.prop
    ((MorphismProperty.Over.w T.hom).symm ▸ T.left.prop)

/-- The functor from the slice `X_proét / W` to `W_proét`, sending `T ⟶ W` to `T` viewed as a
weakly étale `W`-scheme. -/
noncomputable def overToLocalization : Over W ⥤ W.left.ProEt where
  obj T := MorphismProperty.Over.mk ⊤ T.hom.left (weaklyEtale_hom_left W T)
  map {T T'} φ := MorphismProperty.Over.homMk φ.left.left (by
    have := congr_arg (fun ψ ↦ ψ.left) (Over.w φ)
    simpa using this)

/-- The functor `ProEt.overToLocalization W` followed by the localization functor
`W_proét ⥤ X_proét` is the forgetful functor of the slice. -/
noncomputable def overToLocalizationCompOverMapIso :
    overToLocalization W ⋙ MorphismProperty.Over.map ⊤ W.prop ≅ Over.forget W :=
  NatIso.ofComponents (fun T ↦ MorphismProperty.Over.isoMk (Iso.refl _)
    (by simpa using MorphismProperty.Over.w T.hom)) (fun φ ↦ by
      ext
      simp [overToLocalization])

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}}

/-- **Isomorphisms after localization are isomorphisms over the slice**: an isomorphism of the
restrictions of two sheaves along the localization functor `W_proét ⥤ X_proét` gives an
isomorphism of their restrictions to the slice `X_proét / W`. -/
noncomputable def overPullbackIsoOfLocalizationRestrictionIso {A : Type*} [Category.{u + 1} A]
    {W : X.ProEt} {F G : Sheaf (ProEt.topology X) A}
    (e : (ProEtale.localizationRestriction A W.hom W.prop).obj F ≅
      (ProEtale.localizationRestriction A W.hom W.prop).obj G) :
    ((ProEt.topology X).overPullback A W).obj F ≅
      ((ProEt.topology X).overPullback A W).obj G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.op (ProEt.overToLocalizationCompOverMapIso W)) F.obj ≪≫
      Functor.isoWhiskerLeft (ProEt.overToLocalization W).op ((sheafToPresheaf _ _).mapIso e) ≪≫
      (Functor.isoWhiskerRight (NatIso.op (ProEt.overToLocalizationCompOverMapIso W)) G.obj).symm)

/-- The projection `V ×_X W ⟶ W`, as a morphism of the small pro-étale site of `X`. -/
noncomputable def baseChangeToMk {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g] (V : X.ProEt) :
    ProEt.baseChange g V ⟶ ProEt.mk g :=
  MorphismProperty.Over.homMk (pullback.snd V.hom g) pullback.condition.symm

/-- **Local isomorphisms over a cover of `X` are local over every object**: if two pro-étale
sheaves are isomorphic over the members of a pro-étale cover `gᵢ : Wᵢ ⟶ X`, then over every
`V : X_proét` they are isomorphic on a covering sieve (formed by the base changes `V ×_X Wᵢ`). -/
theorem exists_sieve_nonempty_isoPresheaf_of_cover {A : Type*} [Category.{u + 1} A]
    {F G : Sheaf (ProEt.topology X) A} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, WeaklyEtale (g i)] (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    (e : ∀ i, (isoPresheaf F G).obj (op (ProEt.mk (g i)))) (V : X.ProEt) :
    ∃ S ∈ ProEt.topology X V, ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
      Nonempty ((isoPresheaf F G).obj (op Y)) := by
  refine ⟨_, ProEt.ofArrows_baseChange_mem_topology V g hg, fun Y f hf ↦ ?_⟩
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hf
  exact ⟨(isoPresheaf F G).map (h ≫ baseChangeToMk (g i) V).op (e i)⟩

end AlgebraicGeometry.ProEtale
