/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Conservative

/-!
# Detecting isomorphisms on the pro-étale site

This file collects the criteria of blueprint `lem-cbc-proetale-stalk-conservative` for a
morphism of sheaves, or of complexes of sheaves, on the small pro-étale site `X_proét` to be
an isomorphism.

1. *Locality.* A morphism is an isomorphism as soon as its pullbacks along the members of a
   pro-étale covering family are
   (`AlgebraicGeometry.ProEtale.isIso_iff_forall_isIso_upperStar_map`); a sheaf vanishes iff its
   pullbacks do (`AlgebraicGeometry.ProEtale.isZero_iff_forall_isZero_upperStar_obj`); and
   likewise for morphisms of the derived category, through the cohomology sheaves
   (`AlgebraicGeometry.ProEtale.isIso_iff_forall_isIso_mapDerivedCategory_upperStar_map`).
2. *The affine basis.* A morphism of sheaves is an isomorphism iff it is on the sections over
   every affine weakly étale `X`-scheme
   (`AlgebraicGeometry.ProEtale.isIso_iff_forall_isIso_app_affineProEt`), and a sheaf
   vanishes iff these sections vanish
   (`AlgebraicGeometry.ProEtale.isZero_iff_forall_isZero_obj_affineProEt`).
3. *Étale origin.* For a morphism `φ` of étale sheaves, `ν^* φ` is an isomorphism iff `φ` is
   an isomorphism at every geometric point
   (`AlgebraicGeometry.ProEtale.isIso_comparisonUpperStar_map_iff`), and likewise for
   complexes, through the cohomology sheaves
   (`AlgebraicGeometry.ProEtale.isIso_mapDerivedCategory_comparisonUpperStar_map_iff`).

The warning of clause (4) of the blueprint — geometric stalks are *not* conservative on all
pro-étale sheaves — is a negative statement and is not formalised.
-/

@[expose] public section

universe u' u
open CategoryTheory Limits Opposite ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Locality

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- For a weakly étale `g`, the pullback `g^*` on pro-étale sheaves is left exact: it is
restriction along the localization functor
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`). -/
instance preservesFiniteLimits_upperStar_of_weaklyEtale {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [WeaklyEtale g] : PreservesFiniteLimits (g)^*[A] :=
  have : PreservesFiniteLimits (ProEtale.localizationRestriction A g inferInstance) :=
    inferInstanceAs (PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ (inferInstance :
      WeaklyEtale g)).sheafPushforwardContinuous A (ProEt.topology Z) (ProEt.topology Y)))
  preservesFiniteLimits_of_natIso
    (ProEtale.upperStarIsoLocalizationRestriction A g inferInstance).symm

variable {A} {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, WeaklyEtale (g i)]

variable (A) in
/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (1), locality, for sheaves.* A morphism of sheaves on `X_proét` is an isomorphism if
and only if its pullbacks along the members of a pro-étale covering family `g i : W i ⟶ X`
are. This is `AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction`, read through
the identification of `(g i)^*` with restriction along the localization functor. -/
lemma isIso_iff_forall_isIso_upperStar_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {G G' : Sheaf (ProEt.topology X) A} (φ : G ⟶ G') :
    IsIso φ ↔ ∀ i, IsIso ((g i)^*[A].map φ) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  refine ProEtale.isIso_of_isIso_localizationRestriction A φ g hg fun i ↦ ?_
  exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction A (g i)
    inferInstance) φ).1 (h i)

/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (1), locality, for vanishing.* A sheaf on `X_proét` vanishes if and only if its
pullbacks along the members of a pro-étale covering family vanish. -/
lemma isZero_iff_forall_isZero_upperStar_obj
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (G : Sheaf (ProEt.topology X) A) :
    IsZero G ↔ ∀ i, IsZero ((g i)^*[A].obj G) := by
  refine ⟨fun h i ↦ (g i)^*[A].map_isZero h, fun h ↦ ?_⟩
  have : IsIso (0 : G ⟶ 0) := (isIso_iff_forall_isIso_upperStar_map A g hg _).2 fun i ↦
    isIso_of_source_target_iso_zero _ (h i).isoZero
      ((g i)^*[A].map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (1), locality, for complexes.* A morphism of the derived category of sheaves on
`X_proét` is an isomorphism if and only if its pullbacks along the members of a pro-étale
covering family are: both conditions say that the cohomology sheaves are isomorphisms, and
the pullbacks commute with cohomology sheaves, being exact. -/
lemma isIso_iff_forall_isIso_mapDerivedCategory_upperStar_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {K L : DerivedCategory (Sheaf (ProEt.topology X) A)} (ψ : K ⟶ L) :
    IsIso ψ ↔ ∀ i, IsIso (D((g i)^*[A]).map ψ) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  refine (isIso_iff_forall_isIso_upperStar_map A g hg _).2 fun i ↦ ?_
  have := h i
  exact (NatIso.isIso_map_iff ((g i)^*[A].mapDerivedCategoryHomologyFunctorIso n) ψ).2
    (Functor.map_isIso (DerivedCategory.homologyFunctor _ n) (D((g i)^*[A]).map ψ))

end Locality

section Basis

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X : Scheme.{u}}

/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (2), the affine basis, for morphisms.* A morphism of sheaves on `X_proét` is an
isomorphism if and only if it is so on the sections over every affine weakly étale
`X`-scheme. -/
lemma isIso_iff_forall_isIso_app_affineProEt {G G' : Sheaf (ProEt.topology X) A}
    (φ : G ⟶ G') :
    IsIso φ ↔ ∀ W : X.AffineProEt, IsIso (φ.hom.app (op ((AffineProEt.toProEt X).obj W))) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_isIso_app_affineProEt A φ⟩

/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (2), the affine basis, for vanishing.* A sheaf on `X_proét` vanishes if and only if
its sections over every affine weakly étale `X`-scheme vanish. -/
lemma isZero_iff_forall_isZero_obj_affineProEt (G : Sheaf (ProEt.topology X) A) :
    IsZero G ↔
      ∀ W : X.AffineProEt, IsZero (G.obj.obj (op ((AffineProEt.toProEt X).obj W))) := by
  refine ⟨fun h W ↦ (sheafToPresheaf (ProEt.topology X) A ⋙
    (evaluation X.ProEtᵒᵖ A).obj (op ((AffineProEt.toProEt X).obj W))).map_isZero h,
    fun h ↦ ?_⟩
  have : IsIso (0 : G ⟶ 0) := (isIso_iff_forall_isIso_app_affineProEt _).2 fun W ↦
    isIso_of_source_target_iso_zero _ (h W).isoZero
      ((sheafToPresheaf (ProEt.topology X) A ⋙ (evaluation X.ProEtᵒᵖ A).obj
        (op ((AffineProEt.toProEt X).obj W))).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

end Basis

section EtaleOrigin

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [hC : ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  {X : Scheme.{u}} [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hC in
/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (3), étale origin, for sheaves.* For a morphism `φ` of étale sheaves, `ν^* φ` is an
isomorphism if and only if `φ` is an isomorphism at every geometric point of `X`: the
comparison pullback `ν^*` is fully faithful, hence reflects isomorphisms, and geometric
stalks are conservative on étale sheaves
(`AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`).

Clause (4) of the blueprint, that geometric stalks are *not* conservative on arbitrary
pro-étale sheaves (Stacks Project, Tag 0991), is not formalised. -/
lemma isIso_comparisonUpperStar_map_iff {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) :
    IsIso (ν^*(X)[A].map φ) ↔
      ∀ s : X, IsIso ((X.uliftPointSmallEtale s).sheafFiber.map φ) := by
  refine ⟨fun _ s ↦ ?_, fun h ↦ ?_⟩
  · have : IsIso φ := isIso_of_reflects_iso φ ν^*(X)[A]
    infer_instance
  · have : IsIso φ := isIso_of_isIso_sheafFiber_map φ h
    infer_instance

include hC in
/-- Blueprint `lem-cbc-proetale-stalk-conservative`: Detecting isomorphisms on the pro-etale
site.

*Clause (3), étale origin, for complexes.* For a morphism `ψ` of complexes of étale sheaves,
`ν^* ψ` is an isomorphism of the derived category of pro-étale sheaves if and only if the
maps `ℋⁱ(ψ)` of cohomology sheaves are isomorphisms at every geometric point of `X`: the
comparison pullback is exact, so it commutes with cohomology sheaves. -/
lemma isIso_mapDerivedCategory_comparisonUpperStar_map_iff
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology A)} (ψ : K ⟶ L) :
    IsIso (D(ν^*(X)[A]).map ψ) ↔ ∀ (i : ℤ) (s : X), IsIso
      ((X.uliftPointSmallEtale s).sheafFiber.map
        ((DerivedCategory.homologyFunctor _ i).map ψ)) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun i ↦ ?_
  rw [← isIso_comparisonUpperStar_map_iff]
  exact (NatIso.isIso_map_iff ((ν^*(X)[A]).mapDerivedCategoryHomologyFunctorIso i) ψ).symm

end EtaleOrigin

end AlgebraicGeometry.ProEtale
