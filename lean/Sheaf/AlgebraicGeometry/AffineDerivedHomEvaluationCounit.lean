/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule
import Sheaf.AlgebraicGeometry.DerivedInternalHomUnitIso
import Sheaf.AlgebraicGeometry.AffineDerivedHomLocalizedEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # AffineDerivedHomEvaluationCounit

Source: Stacks Project, Duality for Schemes, Section 48.11.
-/

@[expose] public section

universe u wY wA

open CategoryTheory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem transportEvaluation
    {C A : Type*} [Category C] [Category A]
    {L ρ : A ⥤ C} {R : C ⥤ A} {F G : C ⥤ C}
    (adj : L ⊣ R) (e : L ≅ ρ) (p : F ⟶ G) (ι : G ≅ 𝟭 C)
    {K₀ K : C} (q : K₀ ≅ K) (d₀ : L.obj (R.obj K₀) ≅ F.obj K₀)
    (hd₀ : d₀.hom ≫ p.app K₀ ≫ ι.hom.app K₀ = adj.counit.app K₀) :
    ∃ d : ρ.obj (R.obj K) ≅ F.obj K,
      d.hom ≫ p.app K ≫ ι.hom.app K = (adj.ofNatIsoLeft e).counit.app K := by
  refine ⟨(e.app (R.obj K)).symm ≪≫ L.mapIso (R.mapIso q.symm) ≪≫ d₀ ≪≫
    F.mapIso q, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [p.naturality_assoc, ι.hom.naturality]
  change e.inv.app (R.obj K) ≫ (R ⋙ L).map q.inv ≫
    d₀.hom ≫ p.app K₀ ≫ ι.hom.app K₀ ≫ q.hom = _
  have hd := congrArg (fun z ↦ z ≫ q.hom) hd₀
  simp only [Category.assoc] at hd
  rw [hd]
  rw [adj.counit.naturality_assoc q.inv]
  simp [q.inv_hom_id]

private noncomputable def affineScalarLocalizationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (t : DerivedCategory.Q ⋙ L ≅
      (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f))
        ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
          (.up ℤ) ⋙ DerivedCategory.Q) :
    L ≅ (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor := by
  let B : Y.CommAlgebraSheaf := Under.mk (⟨f.c⟩ : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  haveI : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    dsimp [B]
    exact inferInstanceAs (HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
  haveI : CategoryTheory.Limits.PreservesFiniteLimits T :=
    sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  haveI : CategoryTheory.Limits.PreservesFiniteColimits T :=
    sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (t ≪≫ T.mapDerivedCategoryFactors.symm) ≪≫
        T.rightDerivedFunctorIsoMapDerivedCategory.symm


set_option maxHeartbeats 1600000 in
-- The nested derived-adjunction existentials require additional elaboration heartbeats.
/-- The affine algebra-valued derived Hom adjunction, with its evaluation counit.
This lemma involves neither a quasi-coherent right adjoint of pushforward nor its
comparison with scalar restriction.

Source: Stacks Project, Tags 0BUZ, 0BV0 and 0AX3
(blueprint: lem-sc-affine-derived-hom-evaluation-counit).

Proof:
1. Take the underived sheaf-Hom adjunction and its derived adjunction from
   `exists_affine_derivedSheafHom_adjunction`. Scalar restriction is exact, so its
   derived functor L is canonically isomorphic to the chosen rightDerivedFunctor.
   Transport the adjunction across that isomorphism, obtaining H and adjH.
2. Compute on a K-injective resolution I of K. After forgetting the algebra action,
   H(K) is Hom(A,I); identify A with the module f_* O_X by the identity on sections.
   The localization comparison for derivedInternalHom gives the displayed d.
3. Hom(O_Y,I) is canonically I, by evaluation at one in every degree. Descend this
   natural chain isomorphism and the resolution quasi-isomorphism to obtain iota.
4. Precomposition by O_Y -> A followed by that evaluation sends a local map to its
   value at one. The derived counit formula of the affine adjunction is the same
   chain map. Localization and its natural comparison therefore give the equality.
The argument works for all derived objects, including zero and arbitrary shifts. -/
theorem exists_affine_derivedHom_evaluation_counit {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
      (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H),
    ∃ ι : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
    ∀ K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
    ∃ d : (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.obj
          (H.obj K) ≅
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
            K),
    d.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op, 𝟙 K) ≫
        ι.hom.app K = adjH.counit.app K := by
  obtain ⟨H₀, hH₀, iH, adj₀, h_eval, R, β, L, t, adj, hR, _, _, h_counit⟩ :=
    exists_affine_derivedSheafHom_adjunction.{u, wY, wA} f
  let _ := hH₀
  obtain ⟨ι⟩ := derivedInternalHom_unit_iso.{u, wY} Y
  let e := affineScalarLocalizationIso.{u, wY, wA} f L t
  refine ⟨R, adj.ofNatIsoLeft e, ι, ?_⟩
  intro K
  let Kc := DerivedCategory.Q.objPreimage K
  let q := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨d₀, hd₀⟩ := affine_derivedHom_localized_evaluation.{u, wY, wA}
    f H₀ iH adj₀ h_eval R β L t adj hR h_counit ι Kc
  let F := (Functor.curry.obj
    (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))))
  let p := (Functor.curry.obj
    (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).map
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op)
  change d₀.hom ≫ p.app (DerivedCategory.Q.obj Kc) ≫
    ι.hom.app (DerivedCategory.Q.obj Kc) = adj.counit.app (DerivedCategory.Q.obj Kc) at hd₀
  exact transportEvaluation adj e p ι q d₀ hd₀

end AlgebraicGeometry
