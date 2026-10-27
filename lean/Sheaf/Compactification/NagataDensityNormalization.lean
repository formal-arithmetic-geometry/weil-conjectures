/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.Compactification.NagataSketchClosure
public import Sheaf.Compactification.NagataDensityNormalizationSheaves
public import Sheaf.Paper.IdentityOpenDerivedRestriction
public import Sheaf.Paper.RootTowerCoordinateFace
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Paper.DerivedOpenRestrictionNormalization
import all Sheaf.Compactification.NagataDensityNormalizationSheaves

/-! # The unbounded schematic-closure identification

Source: blueprint latest, sec-proetale-coefficients/sk-lem-nagata-density-normalization,
canonical extension and direct-image identifications
(blueprint: sk-lem-nagata-density-normalization).

The first isomorphism is fixed by its restriction to the original open. The second
is its proper direct image followed by the specified derived-composition identification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem isoOfOpenNormalization
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {A : D ⥤ C} {L' : C ⥤ E} {A' : E ⥤ C} {R : E ⥤ D}
    (a : L ⊣ A) (a' : L' ⊣ A') [IsIso a.unit] [IsIso a'.unit]
    (e : L ≅ L' ⋙ R) (r : R ⋙ A ≅ A') :
    ∃ θ : L ≅ L' ⋙ R, ∀ K,
      a.unit.app K ≫ A.map (θ.hom.app K) ≫ r.hom.app (L'.obj K) = a'.unit.app K := by
  have := a.fullyFaithfulLOfIsIsoUnit.full
  have := a.fullyFaithfulLOfIsIsoUnit.faithful
  let t : 𝟭 C ⟶ (L' ⋙ R) ⋙ A := a'.unit ≫ Functor.whiskerLeft L' r.inv
  let α : L ⟶ L' ⋙ R :=
    { app K := (a.homEquiv K ((L' ⋙ R).obj K)).symm (t.app K)
      naturality K K' f := by
        apply (a.homEquiv K ((L' ⋙ R).obj K')).injective
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
        simp only [Equiv.apply_symm_apply]
        exact t.naturality f }
  have hα (K) : IsIso (α.app K) := by
    change IsIso ((a.homEquiv K ((L' ⋙ R).obj K)).symm (t.app K))
    rw [Adjunction.homEquiv_counit]
    have : IsIso (a.counit.app ((L' ⋙ R).obj K)) :=
      a.isIso_counit_app_of_iso (e.app K).symm
    dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have : ∀ K, IsIso (α.app K) := hα
  have : IsIso α := NatIso.isIso_of_isIso_app α
  refine ⟨asIso α, ?_⟩
  intro K
  have h := (a.homEquiv K ((L' ⋙ R).obj K)).apply_symm_apply (t.app K)
  rw [Adjunction.homEquiv_unit] at h
  change a.unit.app K ≫ A.map (α.app K) ≫ r.hom.app (L'.obj K) = _
  rw [← Category.assoc, h]
  simp only [t, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- Replacing a Noetherian compactification by its schematic closure preserves open
extension and the compact-support expression, canonically on all unbounded objects.
Source: blueprint density-normalization statement and its two proof paragraphs
(blueprint: sk-lem-nagata-density-normalization).

Proof:
1. det-nagata-density-normalization-setup identifies the schematic image, its induced
quasi-compact dense open, its closed inclusion and the complementary quasi-compact open.
2. det-sf-open-closed-pullback-limits makes closed inverse image exact. Apply the
unbounded-complex clause of det-nagata-density-normalization-sheaves. The unit followed
by open base change gives the first isomorphism. On the common open its adjunct is the
actual open-extension unit; applying the open Hom bijection gives the normalization below.
3. Apply Rp_* to this isomorphism. The normalized derived direct-image compositor
identifies Ri_* Rp_* with R(pi)_*, giving the second isomorphism with its displayed formula.
The schematic image factorization is again an open immersion followed by a proper map,
so this equates the two compact-support expressions, also over finite-type fields. -/
theorem nagata_density_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (c : Compactification f) [IsNoetherian c.Z] :
    ∃ eZ : (openImmersionLowerShriek Λ c.i).mapDerivedCategory ≅
        (openImmersionLowerShriek Λ c.i.toImage).mapDerivedCategory ⋙
          RootCoordinateFace.lower Λ c.i.imageι,
      (∀ K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).unit.app K ≫
            (upperStar Λ c.i).mapDerivedCategory.map (eZ.hom.app K) ≫
            (identityOpenDerivedRestriction Λ c.i c.i.toImage c.i.imageι
              c.i.toImage_imageι).app
              ((openImmersionLowerShriek Λ c.i.toImage).mapDerivedCategory.obj K) =
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage).unit.app K) ∧
      ∃ eS : (openImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙
            RootCoordinateFace.lower Λ c.g ≅
          (openImmersionLowerShriek Λ c.i.toImage).mapDerivedCategory ⋙
            RootCoordinateFace.lower Λ (c.i.imageι ≫ c.g),
        eS = Functor.isoWhiskerRight eZ (RootCoordinateFace.lower Λ c.g) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (RootCoordinateFace.lowerComp Λ c.i.imageι c.g).symm := by
  let j := (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι
  have hij : Set.range j = (Set.range c.i.imageι)ᶜ := Scheme.Opens.range_ι _
  obtain ⟨hclosed, _⟩ := condensed_open_closed_recollement Λ c.i.imageι j hij
  obtain ⟨_hu, β, _hβ, θ, _hθ, _hK⟩ := nagataDensityNormalizationSheaves Λ f c
  let e : (openImmersionLowerShriek Λ c.i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ c.i.toImage).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ c.i.imageι :=
    Functor.mapDerivedCategoryNatIso θ ≪≫ Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerLeft _
        (lowerStar Λ c.i.imageι).rightDerivedFunctorIsoMapDerivedCategory.symm
  have h_range : Set.range c.i = c.i.imageι '' Set.range c.i.toImage := by
    calc
      Set.range c.i = Set.range (c.i.toImage ≫ c.i.imageι) :=
        congrArg (fun t : X ⟶ c.Z ↦ Set.range t) c.i.toImage_imageι.symm
      _ = _ := Set.range_comp (fun x ↦ c.i.imageι x) (fun x ↦ c.i.toImage x)
  have hw : c.i.imageι ⁻¹' Set.range c.i = Set.range c.i.toImage := by
    rw [h_range]
    exact Set.preimage_image_eq _ c.i.imageι.isEmbedding.injective
  have sq : IsPullback c.i.toImage (𝟙 X) c.i.imageι c.i := by
    apply (IsOpenImmersion.isPullback (𝟙 X) c.i.toImage c.i c.i.imageι _ _).flip
    · simp
    · exact TopologicalSpace.Opens.ext hw
  have hr : IsIso (derivedDirectImageOpenRestriction Λ sq.toCommSq) :=
    (derivedOpenRestrictionNormalization Λ sq).1
  have : IsIso (identityOpenDerivedRestriction Λ c.i c.i.toImage c.i.imageι
      c.i.toImage_imageι) := by
    unfold identityOpenDerivedRestriction
    infer_instance
  have hu : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).unit := by
    have := openUnit Λ c.i
    exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hu' : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage).unit := by
    have := openUnit Λ c.i.toImage
    exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  obtain ⟨eZ, heZ⟩ := isoOfOpenNormalization
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage) e
    (asIso (identityOpenDerivedRestriction Λ c.i c.i.toImage c.i.imageι
      c.i.toImage_imageι))
  refine ⟨eZ, heZ, ?_⟩
  exact ⟨_, rfl⟩


end AlgebraicGeometry.ProEtale.CondensedRing
