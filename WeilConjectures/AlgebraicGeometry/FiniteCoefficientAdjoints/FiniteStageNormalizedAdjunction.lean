/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

/-! # Normalized adjunction at one finite coefficient stage

Source: current blueprint reduction-exceptional, Locality and Charts, with the
ordinary closed-chart preservation argument in the parent node, proof steps 1--4.
(blueprint: lem-pur-finite-stage-normalized-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

section Construction

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [IsNoetherian X] [IsNoetherian Y]
  (c : Compactification f)

private theorem rnu_ctf (T : Scheme.{u}) (K : D A T) (hK : ctf A T K) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((rnu A T).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK.1
  have hLt : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T L := by
    obtain ⟨a, b, ht⟩ :=
      (ctf A T).prop_of_iso e.symm hK |>.2
    exact ⟨a, b, (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      a b L).mp ht⟩
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) T L hL.1.1
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso
    (asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app L) ≪≫
      (rnu A T).mapIso e) ⟨hL, hLt⟩

private theorem etale_preserves
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent A Y]
    [QuasiCompact f] (K : Etale.DerivedCategoryModule A Y)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y K) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
      ((etaleUpper A c).obj K) := by
  let : HasCompactification f := c.hasCompactification
  let adj := (Etale.rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso A c).symm
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
    (((etaleAdjunction A c).rightAdjointUniq adj).app K).symm
    (Etale.constructibleFiniteTor_rightDerivedUpperShriek A aY f hK)

private theorem upper_preserves
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent A Y]
    [QuasiCompact f] (K : D A Y) (hK : ctf A Y K) :
    ctf A X ((upper A c).obj K) := by
  exact ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory A
    (etale_preserves A c k aY _ (rnu_ctf A Y K hK))

variable
  (hL : ∀ K, ctf A X K → ctf A Y ((lower A c).obj K))
  (hR : ∀ K, ctf A Y K → ctf A X ((upper A c).obj K))
  (hb : ∀ K, ctf A Y K → DerivedCategory.TStructure.t.plus
    ((etaleUpper A c).obj ((rnu A Y).obj K)))

private def normalizedCounit (K : (ctf A Y).FullSubcategory) :
    (lower A c).obj ((upper A c).obj K.obj) ⟶ K.obj :=
  (ProEtale.compactSupportSiteComparison A c).hom.app
      ⟨(etaleUpper A c).obj ((rnu A Y).obj K.obj), hb K.obj K.property⟩ ≫
    (nu A Y).map ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj)) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K.obj

private theorem normalizedCounit_naturality
    {K K' : (ctf A Y).FullSubcategory} (v : K ⟶ K') :
    (lower A c).map ((upper A c).map v.hom) ≫ normalizedCounit A c hb K' =
      normalizedCounit A c hb K ≫ v.hom := by
  have h := (ProEtale.compactSupportSiteComparison A c).hom.naturality
    (X := ⟨_, hb K.obj K.property⟩) (Y := ⟨_, hb K'.obj K'.property⟩)
    (ObjectProperty.homMk ((etaleUpper A c).map ((rnu A Y).map v.hom)))
  dsimp at h
  dsimp only [normalizedCounit, upper, Functor.comp_map]
  rw [reassoc_of% h, ← Functor.map_comp_assoc]
  erw [(etaleAdjunction A c).counit_naturality ((rnu A Y).map v.hom)]
  rw [Functor.map_comp_assoc]
  erw [(ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit_naturality]
  simp only [Category.assoc]

private theorem normalizedCounit_bijective
    (M : (ctf A X).FullSubcategory) (K : (ctf A Y).FullSubcategory) :
    Function.Bijective (fun g : M.obj ⟶ (upper A c).obj K.obj ↦
      (lower A c).map g ≫ normalizedCounit A c hb K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := M.property.1
  let F := lower A c
  let N := nu A X
  let eps := normalizedCounit A c hb K
  have hi : Function.Bijective (fun g : N.obj L ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) := by
    let E := (((etaleAdjunction A c).homEquiv L _).symm.trans
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj).symm).trans
        (((ProEtale.compactSupportSiteComparison A c).app
          ⟨L, hL.1.1⟩).symm.homFromEquiv (Z := K.obj))
    have he : (fun g : N.obj L ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) ∘
        (fun g ↦ N.map g) = ⇑E := by
      funext g
      have hn := (ProEtale.compactSupportSiteComparison A c).hom.naturality
        (X := ⟨L, hL.1.1⟩) (Y := ⟨_, hb K.obj K.property⟩)
        (ObjectProperty.homMk g)
      dsimp at hn
      change F.map (N.map g) ≫ eps =
        ((ProEtale.compactSupportSiteComparison A c).app ⟨L, hL.1.1⟩).hom ≫
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv
            _ K.obj).symm (((etaleAdjunction A c).homEquiv L _).symm g)
      simp only [Adjunction.homEquiv_counit, normalizedCounit, eps, Functor.map_comp,
        Category.assoc, Iso.app_hom]
      erw [reassoc_of% hn]
      rfl
    apply (Function.Bijective.of_comp_iff _
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map L _
        (hb K.obj K.property))).1
    rw [he]
    exact E.bijective
  have he : (fun g : M.obj ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) =
      ⇑(F.mapIso e).homFromEquiv ∘
        (fun g : N.obj L ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) ∘
          ⇑e.symm.homFromEquiv := by
    funext g
    simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.symm_inv,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [he]
  exact (F.mapIso e).homFromEquiv.bijective.comp (hi.comp e.symm.homFromEquiv.bijective)

private def normalizedAdjunction : restrict (lower A c) hL ⊣ restrict (upper A c) hR := by
  let e (M : (ctf A X).FullSubcategory) (K : (ctf A Y).FullSubcategory) :
      (M ⟶ (restrict (upper A c) hR).obj K) ≃
        ((restrict (lower A c) hL).obj M ⟶ K) :=
    ((ObjectProperty.fullyFaithfulι (ctf A X)).homEquiv
      (X := M) (Y := (restrict (upper A c) hR).obj K)).trans
      ((Equiv.ofBijective _ (normalizedCounit_bijective A c hb M K)).trans
        ((ObjectProperty.fullyFaithfulι (ctf A Y)).homEquiv
          (X := (restrict (lower A c) hL).obj M) (Y := K)).symm)
  exact Adjunction.mkOfHomEquiv
    { homEquiv := fun M K ↦ (e M K).symm
      homEquiv_naturality_left_symm := by
        intro M' M K v g
        apply ObjectProperty.hom_ext
        change (lower A c).map (v.hom ≫ g.hom) ≫ normalizedCounit A c hb K =
          (lower A c).map v.hom ≫
            ((lower A c).map g.hom ≫ normalizedCounit A c hb K)
        rw [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro M K K' v g
        apply (e M K').injective
        rw [(e M K').apply_symm_apply]
        apply ObjectProperty.hom_ext
        change _ = (lower A c).map
          (((e M K).symm v).hom ≫ (upper A c).map g.hom) ≫ normalizedCounit A c hb K'
        rw [Functor.map_comp, Category.assoc, normalizedCounit_naturality A c hb g]
        have he := congrArg (fun t ↦ t.hom) ((e M K).apply_symm_apply v)
        change (lower A c).map ((e M K).symm v).hom ≫ normalizedCounit A c hb K = v.hom at he
        rw [← Category.assoc, he]
        rfl }

end Construction

end AlgebraicGeometry.FiniteCoefficientAdjoints
