/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Internal Hom and étale restriction

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, coefficient dual argument.
(blueprint: lem-weil-pbc-etale-pullback-internal-hom)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.EtaleInternalHomProof

universe u'

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Opposite

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]
  {V X : Scheme.{u}} (g : V ⟶ X) (h : Etale g)
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal]

private instance localization_continuous :
    (MorphismProperty.Over.map ⊤ h).IsContinuous V.smallEtaleTopology X.smallEtaleTopology :=
  inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
    (V.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale))

attribute [local instance] Sheaf.monoidalCategory

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [BraidedCategory A]
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal] in
/-- The unit of `j_g^* ⊣ g_*` restricts sections along the counit of the site adjunction.
Adapted from the pro-étale analogue in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom`. -/
private lemma localizationRestrictionLowerStarAdjunction_unit_app_hom_app
    (P : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((sheafToPresheaf _ A).map ((localizationRestrictionLowerStarAdjunction A g h).unit.app P)).app
      U =
      P.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g h trivial).counit.app
        U.unop).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

/-- The unit of `j_g^* ⊣ g_*` is compatible with the tensor comparison maps. -/
private lemma localizationRestrictionLowerStarAdjunction_unit_app_tensor
    (P Q : Sheaf X.smallEtaleTopology A) :
    (localizationRestrictionLowerStarAdjunction A g h).unit.app (P ⊗ Q) =
      ((localizationRestrictionLowerStarAdjunction A g h).unit.app P ⊗ₘ
        (localizationRestrictionLowerStarAdjunction A g h).unit.app Q) ≫
        μ (g)_*[A] _ _ ≫ (g)_*[A].map (μ ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
          A V.smallEtaleTopology X.smallEtaleTopology) P Q) := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, ← μ_natural_assoc]
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp, Monoidal.tensorHom_app,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  erw [← (μ (sheafToPresheaf X.smallEtaleTopology A) P Q).naturality]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ h)]
  rfl

/-- The unit of `j_g^* ⊣ g_*` is compatible with the unit comparison maps. -/
private lemma localizationRestrictionLowerStarAdjunction_unit_app_unit :
    (localizationRestrictionLowerStarAdjunction A g h).unit.app (𝟙_ _) =
      ε (g)_*[A] ≫ (g)_*[A].map (ε ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
          A V.smallEtaleTopology X.smallEtaleTopology)) := by
  apply Sheaf.hom_ext_of_ε_comp
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  erw [← (ε (sheafToPresheaf X.smallEtaleTopology A)).naturality]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ h)]
  erw [Monoidal.tensorUnit_map, Category.id_comp]
  rfl

section

variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

open Functor.OplaxMonoidal

/-- The identification of the pullback along an étale morphism with the restriction,
as a functor to the pushforward. -/
private noncomputable abbrev upperStarIsoSheafPushforward :
    (g)^*[A] ≅ (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
      V.smallEtaleTopology X.smallEtaleTopology :=
  upperStarIsoLocalizationRestriction A g h

/-- The identification of the pullback along an étale morphism with the restriction is a
monoidal natural isomorphism. -/
private instance : NatTrans.IsMonoidal (upperStarIsoSheafPushforward A g h).hom where
  unit := by
    rw [← cancel_epi (η (g)^*[A])]
    simp only [Functor.Monoidal.η_ε_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    dsimp only [upperStarIsoSheafPushforward, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_app_unit_comp_map_η]
    exact localizationRestrictionLowerStarAdjunction_unit_app_unit A g h
  tensor P Q := by
    rw [← cancel_epi (δ (g)^*[A] P Q)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    dsimp only [upperStarIsoSheafPushforward, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_app_tensor_comp_map_δ, Functor.map_comp, Category.assoc,
      ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      Adjunction.unit_leftAdjointUniq_hom_app]
    exact localizationRestrictionLowerStarAdjunction_unit_app_tensor A g h P Q

end

section Closed

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
  {V X : Scheme.{u}} (g : V ⟶ X) [hg : Etale g]
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal]

open scoped MonoidalClosed.FunctorCategory

omit [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal] in
/-- **Pullback along an étale morphism commutes with internal homs**: the comparison map
`g^* [P, Q] ⟶ [g^* P, g^* Q]` is an isomorphism. -/
private theorem isIso_ihomComparison_upperStar (P : Sheaf X.smallEtaleTopology A) :
    IsIso (ihomComparison (g)^*[A] P).natTrans := by
  -- The local description of internal Hom is invariant under localization of the site.
  let h : Etale g := hg
  let R := (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
    V.smallEtaleTopology X.smallEtaleTopology
  let W := (Functor.whiskeringLeft _ _ A).obj (MorphismProperty.Over.map ⊤ h).op
  have : ∀ k : V.Etaleᵒᵖ, (Under.post (MorphismProperty.Over.map ⊤ h).op (X := k)).IsEquivalence :=
    fun k ↦ MorphismProperty.Over.isEquivalence_post_map_op h k.unop
  have hW : IsIso (ihomComparison W ((sheafToPresheaf _ A).obj P)).natTrans := inferInstance
  have hι : ∀ Y : Sheaf X.smallEtaleTopology A,
      IsIso (ihomComparison (sheafToPresheaf _ A) Y).natTrans :=
    Monoidal.Reflective.isIso_ihomComparison
      (sheafificationAdjunction (_ : Scheme).smallEtaleTopology A)
  have hιV : ∀ Y : Sheaf V.smallEtaleTopology A,
      IsIso (ihomComparison (sheafToPresheaf _ A) Y).natTrans :=
    Monoidal.Reflective.isIso_ihomComparison
      (sheafificationAdjunction (_ : Scheme).smallEtaleTopology A)
  have h1 : IsIso (ihomComparison (sheafToPresheaf _ A ⋙ W) P).natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Q
    rw [ihomComparison_comp_app]
    infer_instance
  let τ := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (MorphismProperty.Over.map ⊤ h) A V.smallEtaleTopology X.smallEtaleTopology
  have : NatTrans.IsMonoidal τ.symm.hom := inferInstanceAs (NatTrans.IsMonoidal τ.inv)
  have h2 : IsIso (ihomComparison (R ⋙ sheafToPresheaf _ A) P).natTrans :=
    isIso_ihomComparison_of_iso τ.symm P
  have hR : IsIso (ihomComparison R P).natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Q
    have := NatIso.isIso_app_of_isIso (ihomComparison (R ⋙ sheafToPresheaf _ A) P).natTrans Q
    rw [ihomComparison_comp_app] at this
    have := IsIso.of_isIso_comp_right ((sheafToPresheaf _ A).map
      ((ihomComparison R P).natTrans.app Q))
      ((ihomComparison (sheafToPresheaf _ A) (R.obj P)).natTrans.app (R.obj Q))
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ A)
  exact isIso_ihomComparison_of_iso (upperStarIsoSheafPushforward A g h) P

end Closed

end AlgebraicGeometry.EtaleInternalHomProof


open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- Étale pullback commutes with internal Hom of module sheaves.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` local trivialization argument.

Proof: Identify the small étale site of Y, for an étale Y → X, with the localization
of the small étale site of X at Y. On a site, the internal Hom sheaf evaluated at U
is the module of morphisms between the two sheaves restricted to the localization at U.
This description follows from the tensor-Hom adjunction: maps from the free module sheaf
on the representable U to the internal Hom are maps from its tensor product with F to G,
which are precisely maps F|U → G|U. Localization first at Y and then at an object U → Y
is equivalent to localization at U in the original site. Thus restriction of internal Hom
and internal Hom of restrictions have naturally isomorphic sections at every U.
The section identifications commute with restriction along U' → U (both restrict the
same sheaf morphism), giving the required sheaf isomorphism. Transport it across the
localized-site equivalence to the functor Etale.upperStar.
No finite generation or noetherian hypothesis is needed.
(blueprint: lem-weil-pbc-etale-pullback-internal-hom) -/
theorem nonempty_etale_upperStar_ihom_iso (f : Y ⟶ X) [Etale f]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj ((ihom F).obj G) ≅
      (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G)) := by
  have := EtaleInternalHomProof.isIso_ihomComparison_upperStar
    (ModuleCat.{u + 1} Λ) f F
  exact ⟨asIso ((Functor.LaxMonoidal.ihomComparison
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f) F).natTrans.app G)⟩

end AlgebraicGeometry.Scheme
