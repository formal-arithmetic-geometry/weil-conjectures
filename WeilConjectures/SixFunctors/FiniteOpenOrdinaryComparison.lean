/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorNormalizationData
import all WeilConjectures.AlgebraicGeometry.FiniteConstantCoefficientTransport

/-! # Ordinary finite open comparisons

Source: Stacks 03D7 and 0F6Z.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace SheafOfModules.OpenTensorNormalization

/-- The inverse underlying-sheaf comparison also preserves constant scalars. -/
private theorem finite_inverse_scalar
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (M : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (a : A) (x : M.obj.obj W) :
    (e.underlying.inv.app M).hom.app W (a • x) =
      @SMul.smul
        (((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj W)
        ((e.equivalence.functor.obj M).val.obj W) inferInstance (i.app W a)
        ((e.underlying.inv.app M).hom.app W x) := by
  apply (ConcreteCategory.bijective_of_isIso ((e.underlying.hom.app M).hom.app W)).1
  have h (y : M.obj.obj W) : (e.underlying.hom.app M).hom.app W
      ((e.underlying.inv.app M).hom.app W y) = y := by
    exact ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (e.underlying.inv_hom_id_app M)) W) y
  rw [e.scalar, h, h]
  rfl

private theorem finite_open_star_exists
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (eX : FiniteRealization A X R i)
    (eU : FiniteRealization A U (restrictRing .ordinary j R)
      (Functor.whiskerLeft (openInclusion .ordinary j).op i)) :
    ∃ star : ProEtale.upperStar (ModuleCat.{u + 1} A) j ⋙ eU.equivalence.functor ≅
        eX.equivalence.functor ⋙ restrict .ordinary j R,
      ∀ (M : FiniteModules A X) (W : U.ProEtᵒᵖ)
        (x : (eU.equivalence.functor.obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj M)).val.obj W),
        (eX.underlying.hom.app M).hom.app ((openInclusion .ordinary j).op.obj W)
            ((star.hom.app M).val.app W x) =
        ((ProEtale.upperStarIsoOpenImmersionRestriction
          (ModuleCat.{u + 1} A) j).hom.app M).hom.app W
            ((eU.underlying.hom.app _).hom.app W x) := by
  let K := ProEt.topology U
  let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
  let L := F ⋙ eU.equivalence.functor
  let G := eX.equivalence.functor ⋙ restrict .ordinary j R
  let T := toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing .ordinary j R))
  let k := Functor.whiskerLeft (openInclusion .ordinary j).op i
  let α := Functor.whiskerRight k (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : (proEtaleOpenComposition j).IsCocontinuous K (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have : Presheaf.IsLocallySurjective K k :=
    Presheaf.isLocallySurjective_whisker K (ProEt.topology X)
      (proEtaleOpenComposition j) i
  have : Presheaf.IsLocallySurjective K α := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective K
      (Functor.whiskerRight k (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  have : (openInclusion .ordinary j).IsContinuous K (ProEt.topology X) :=
    openInclusion_continuous .ordinary j
  have : Presheaf.IsLocallySurjective (topology .ordinary U) α :=
    inferInstanceAs (Presheaf.IsLocallySurjective K α)
  let h : L ⋙ T ≅ G ⋙ T :=
    Functor.isoWhiskerLeft F eU.underlying ≪≫
      Functor.isoWhiskerRight
        (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)
        (sheafCompose K (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})) ≪≫
      Functor.isoWhiskerRight eX.underlying.symm
        ((openInclusion .ordinary j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          K (ProEt.topology X))
  let g (M : FiniteModules A X) : L.obj M ⟶ G.obj M :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α (G.obj M).isSheaf).symm
      (PresheafOfModules.homMk (h.hom.app M).hom (fun W a x ↦ by
        change (eX.underlying.inv.app M).hom.app ((openInclusion .ordinary j).op.obj W)
          (((ProEtale.upperStarIsoOpenImmersionRestriction
          (ModuleCat.{u + 1} A) j).hom.app M).hom.app W
            ((eU.underlying.hom.app _).hom.app W
              (@SMul.smul
                (((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                  (restrictRing .ordinary j R)).obj.obj W)
                ((L.obj M).val.obj W) inferInstance (k.app W a) x))) = _
        erw [eU.scalar]
        erw [((ProEtale.upperStarIsoOpenImmersionRestriction
          (ModuleCat.{u + 1} A) j).hom.app M).hom.app W |>.hom.map_smul]
        exact finite_inverse_scalar eX M ((openInclusion .ordinary j).op.obj W) a _))⟩
  have hg (M : FiniteModules A X) : T.map (g M) = h.hom.app M := rfl
  let t : L ⟶ G :=
    { app := g
      naturality := fun {M N} b ↦ by
        apply T.map_injective
        simp only [Functor.map_comp, hg]
        exact h.hom.naturality b }
  have ht (M : FiniteModules A X) : IsIso (t.app M) := by
    have : IsIso (T.map (t.app M)) := by
      change IsIso (T.map (g M))
      rw [hg]
      infer_instance
    exact isIso_of_reflects_iso _ T
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, ?_⟩
  intro M W x
  change (eX.underlying.hom.app M).hom.app ((openInclusion .ordinary j).op.obj W)
    ((eX.underlying.inv.app M).hom.app ((openInclusion .ordinary j).op.obj W)
      (((ProEtale.upperStarIsoOpenImmersionRestriction
          (ModuleCat.{u + 1} A) j).hom.app M).hom.app W
            ((eU.underlying.hom.app _).hom.app W x))) = _
  exact ConcreteCategory.congr_hom (congr_app
    (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
      (eX.underlying.inv_hom_id_app M)) ((openInclusion .ordinary j).op.obj W)) _

/-- Prescribed finite realizations identify ordinary open inverse image and extension by
zero, preserving the section restriction map and the adjunction unit.

Source: Stacks 03D7 and 0F6Z (blueprint: lem-sf-finite-open-ordinary-comparison).
Proof: identify underlying additive sheaves by the supplied realization comparisons
and the fixed-coefficient open-restriction isomorphism. The scalar equations make this
map linear on constants. Local surjectivity of constants on the open upgrades it to a
module-sheaf morphism. Forgetting module structure reflects isomorphisms, so this map
is an isomorphism. Take its inverse mate under the two open-extension adjunctions.
Both vertical functors are equivalences, hence this mate is invertible. The unit-mate
identity followed by cancellation of the mate and its inverse gives the asserted unit
normalization. -/
theorem finite_open_ordinary_comparison_exists
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (eX : FiniteRealization A X R i)
    (eU : FiniteRealization A U (restrictRing .ordinary j R)
      (Functor.whiskerLeft (openInclusion .ordinary j).op i))
    (o : OpenExtension .ordinary j R) :
    ∃ (star : ProEtale.upperStar (ModuleCat.{u + 1} A) j ⋙ eU.equivalence.functor ≅
        eX.equivalence.functor ⋙ restrict .ordinary j R)
      (shriek : ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
        eX.equivalence.functor ≅ eU.equivalence.functor ⋙ o.ordinary),
      (∀ (M : FiniteModules A X) (W : U.ProEtᵒᵖ)
        (x : (eU.equivalence.functor.obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj M)).val.obj W),
        (eX.underlying.hom.app M).hom.app ((openInclusion .ordinary j).op.obj W)
            ((star.hom.app M).val.app W x) =
        ((ProEtale.upperStarIsoOpenImmersionRestriction
          (ModuleCat.{u + 1} A) j).hom.app M).hom.app W
            ((eU.underlying.hom.app _).hom.app W x)) ∧
      (∀ M : FiniteModules A U,
        eU.equivalence.functor.map
          ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app M) ≫
          star.hom.app ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M) ≫
          (restrict .ordinary j R).map (shriek.hom.app M) =
        o.adjunction.unit.app (eU.equivalence.functor.obj M)) := by
  obtain ⟨star, hs⟩ := finite_open_star_exists A j R i eX eU
  let a := ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := TwoSquare.mk _ _ _ _ star.hom
  have : IsIso b.natTrans := inferInstanceAs (IsIso star.hom)
  have : IsIso ((mateEquiv a o.adjunction).symm b).natTrans :=
    AlgebraicGeometry.ProEtale.StrictTower.inverseMate_isIso_of_equivalences a o.adjunction b
  let shriek := (asIso ((mateEquiv a o.adjunction).symm b).natTrans).symm
  refine ⟨star, shriek, hs, ?_⟩
  intro M
  have hu := unit_mateEquiv_symm a o.adjunction b M
  change eU.equivalence.functor.map (a.unit.app M) ≫ star.hom.app _ =
    o.adjunction.unit.app _ ≫ (restrict .ordinary j R).map (shriek.inv.app M) at hu
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
    shriek.inv_hom_id_app]
  exact (restrict .ordinary j R).map_id _ ▸ Category.comp_id _

end SheafOfModules.OpenTensorNormalization
