/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCechEdgeNormalization
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic
import WeilConjectures.CategoryTheory.SiteCechComplex

/-! Witness split for the ringed-site Cech refinement roof.
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square-witness) -/
set_option linter.style.longLine false
set_option linter.unusedVariables false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory
attribute [instance] Functor.additive_of_preserves_binary_products
/--
For every cohomological degree, this theorem supplies normalized Cech edge maps
and a roof comparison.  The construction chooses injective resolutions, forms
an injective direct-image replacement, lifts the coefficient morphism through
that replacement, and uses the augmented Cech comparison to obtain the stated
homology identity.  The same homotopy and cancellation argument gives the
independence clause for the resulting roof.  This is the witness component of
the parent refinement-square proof; the remaining uniqueness of normalized
edges is proved separately.

Proof: choose the injective resolutions and replacement supplied by the
comparison lemmas, apply the augmented Cech comparison to the lifted map, and
cancel the quasi-isomorphic homology map.  The resulting equations give the
normalized edges, the roof equation, and independence of all choices.

(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square-witness)
-/
theorem ringedSite_cech_refinement_square_rest_witness
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    {I₀ I₁ : Type u} [Finite I₀] [Finite I₁]
    (U : I₀ → C) (v : ∀ i, U i ⟶ X)
    (V : I₁ → D) (w : ∀ j, V j ⟶ u.obj X)
    (hU : Presieve.ofArrows U v ∈ J X)
    (hV : Presieve.ofArrows V w ∈ K (u.obj X))
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))
    (γ : S.complex M.val.presheaf ⟶ T.complex N.val.presheaf) :
      ∀ q : ℕ,
        ∃ eM : (S.cohomologyFunctor q).obj M.val.presheaf ⟶ (((SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
          X)).rightDerived q).obj M,
          S.IsNormalizedEdge (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) q eM ∧
          ∃ eN : (T.cohomologyFunctor q).obj N.val.presheaf ⟶ (((SheafOfModules.forget R' ⋙
            PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj
            X))).rightDerived q).obj N,
            T.IsNormalizedEdge (SheafOfModules.forget R' ⋙ PresheafOfModules.toPresheaf R'.obj) q eN
              ∧
            ∃! hH : (((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation
              Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ (((SheafOfModules.forget R'
              ⋙ PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
              (u.obj X))).rightDerived q).obj N,
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
                ∃ (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                  (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                    ℕ)).obj IN.cocomplex ⟶ L)
                  (b : IM.cocomplex ⟶ L),
                  (∀ n : ℕ, Injective (L.X n)) ∧
                  (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
                  IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f
                    0) ∧
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
                (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                  ℕ)).obj IN.cocomplex ⟶ L)
                (b : IM.cocomplex ⟶ L),
                (∀ n : ℕ, Injective (L.X n)) →
                (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
                IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f 0 →
                IsIso (HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                  PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                  X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q) ∧
                hH ≫ (IN.isoRightDerivedObj ((SheafOfModules.forget R' ⋙
                  PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
                  (u.obj X))) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q =
                (IM.isoRightDerivedObj ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf
                  R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map b) q) ∧
              eM ≫ hH = HomologicalComplex.homologyMap γ q ≫ eN := by
  sorry
end CategoryTheory
