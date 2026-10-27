/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.SixFunctors.TraceFormula.SectionAdjunctionCoordinateCoherence

/-! # Coordinate coherence for tensor pullback

Source: Stacks Project, Descent, Tags 03DR, 03DX, 03LC and 05VG.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

private theorem tensorUnit_hom {A B : Scheme.{u}} (a : A ⟶ B) :
    (trfTensorUnit a).hom = Modules.tensorPullbackObjUnitToUnit a := by
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction a)
  apply (adj.homEquiv _ _).injective
  have hknown : adj.homEquiv _ _ (Modules.tensorPullbackObjUnitToUnit a) =
      SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [hknown]
  change adj.homEquiv _ _
      ((adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction a)).hom.app _ ≫
        (Modules.pullbackObjUnitIso a).hom) = _
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have he : (Modules.pullbackPushforwardAdjunction a).homEquiv _ _
      (Modules.pullbackObjUnitIso a).hom =
      SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      a.toRingCatSheafHom
  simpa only [Adjunction.homEquiv_unit] using he

private theorem tensorStructureMap_comp {A B D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) :
    (Modules.tensorSectionsComp a b).hom.app (SheafOfModules.unit D.ringCatSheaf) ≫
        Modules.tensorPullbackObjUnitToUnit (a ≫ b) =
      (Modules.tensorPullback a).map (Modules.tensorPullbackObjUnitToUnit b) ≫
        Modules.tensorPullbackObjUnitToUnit a := by
  let adjA := Classical.choose (Modules.exists_tensorPullbackAdjunction a)
  let adjB := Classical.choose (Modules.exists_tensorPullbackAdjunction b)
  let adjAB := Classical.choose (Modules.exists_tensorPullbackAdjunction (a ≫ b))
  apply ((adjB.comp adjA).homEquiv _ _).injective
  have hu := unit_conjugateEquiv_symm adjAB (adjB.comp adjA)
    (Modules.pushforwardComp a b).inv (SheafOfModules.unit D.ringCatSheaf)
  have ha := (Modules.tensorPullbackObjUnitToUnit_isIso a).2
  have hb := (Modules.tensorPullbackObjUnitToUnit_isIso b).2
  have hab := (Modules.tensorPullbackObjUnitToUnit_isIso (a ≫ b)).2
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Functor.map_comp, ← Category.assoc]
  change adjAB.unit.app _ ≫ (Modules.pushforwardComp a b).inv.app _ =
    (adjB.comp adjA).unit.app _ ≫ (Modules.pushforward a ⋙
      Modules.pushforward b).map ((Modules.tensorSectionsComp a b).hom.app _)
    at hu
  rw [← hu, Category.assoc]
  rw [← (Modules.pushforwardComp a b).inv.naturality]
  rw [← Category.assoc, hab]
  rw [Adjunction.comp_unit_app, Category.assoc]
  dsimp only [Functor.comp_map]
  have hn : adjA.unit.app _ ≫ (Modules.pushforward a).map
      ((Modules.tensorPullback a).map (Modules.tensorPullbackObjUnitToUnit b) ≫
        Modules.tensorPullbackObjUnitToUnit a) =
      Modules.tensorPullbackObjUnitToUnit b ≫
        SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [adjA.unit_naturality (Modules.tensorPullbackObjUnitToUnit b)]
    rw [Category.assoc, ha]
  rw [← Functor.map_comp, hn, Functor.map_comp, ← Category.assoc, hb]
  ext W x
  rfl

/-- Coordinate coherence for normalized tensor pullback, before choosing line modules.
Source: Stacks Project, Descent, Tag 03LC (1); Sheaves, Tags 0096 and 0097.
(blueprint: lem-trf-tensor-sections-coordinate-coherence)

Proof: For identity, left-adjoint unitality identifies c_(w,id) followed by
transport with w-star of the normalized identity comparison. The normalized unit
for the identity arrow cancels its identity comparison, so the inverse composition
map followed by w-star of that comparison is precisely the restriction along the
canonical identity site arrow. For composition, apply left-adjoint composition
associativity to W to Z to Y to X, then cancel the two invertible composition
maps. The resulting equality is the displayed equation, with the identity site
arrow providing the equality transport between the two parenthesizations.
For the structure module, apply the composite adjunction Hom equivalence to
c_(w,v) followed by e_(wv) and to w-star(e_v) followed by e_w. Naturality of its
unit and the characterizing equation for e identify both images with the composite
structure ring map. Injectivity gives equality; cancel c_(w,v) and take sections.
These are equalities of actual module morphisms, so require no nonemptiness,
quasi-coherence or invertibility hypotheses on F.
-/
theorem trf_tensor_sections_coordinate_coherence :
    (∀ (X : Scheme.{u}) (F : X.Modules) (W : X.Etale)
      (s : Γ((Modules.tensorPullback (W.hom ≫ 𝟙 X)).obj F, ⊤)),
      ((Modules.tensorPullback W.hom).map ((trfTensorId X).hom.app F)).app ⊤
        (((Modules.tensorSectionsComp W.hom (𝟙 X)).inv.app F).app ⊤ s) =
      Modules.etaleTensorSectionsRestriction F (trfEtaleIdArrow W) s) ∧
    (∀ (X Y Z : Scheme.{u}) (v : Y ⟶ X) (w : Z ⟶ Y) [Etale v] [Etale w]
      (F : X.Modules) (W : Z.Etale)
      (s : Γ((Modules.tensorPullback ((W.hom ≫ w) ≫ v)).obj F, ⊤)),
      ((Modules.tensorPullback W.hom).map
        ((Modules.tensorSectionsComp w v).hom.app F)).app ⊤
          (((Modules.tensorSectionsComp W.hom w).inv.app
            ((Modules.tensorPullback v).obj F)).app ⊤
              (((Modules.tensorSectionsComp (W.hom ≫ w) v).inv.app F).app ⊤ s)) =
      ((Modules.tensorSectionsComp W.hom (w ≫ v)).inv.app F).app ⊤
        (Modules.etaleTensorSectionsRestriction F (trfEtaleCompArrow v w W) s)) ∧
    (∀ (X Y : Scheme.{u}) (v : Y ⟶ X) [Etale v] (W : Y.Etale)
      (s : Γ((Modules.tensorPullback (W.hom ≫ v)).obj
        (SheafOfModules.unit X.ringCatSheaf), ⊤)),
      (trfTensorUnit W.hom).hom.app ⊤
        (((Modules.tensorPullback W.hom).map (trfTensorUnit v).hom).app ⊤
          (((Modules.tensorSectionsComp W.hom v).inv.app
            (SheafOfModules.unit X.ringCatSheaf)).app ⊤ s)) =
      (trfTensorUnit (W.hom ≫ v)).hom.app ⊤ s) := by
  obtain ⟨hidentity, hinverse, hassoc⟩ := section_adjunction_coordinate_coherence
    (fun {_ _} f ↦ Modules.tensorPullback f)
    (fun {_ _} f ↦ Classical.choose (Modules.exists_tensorPullbackAdjunction f))
  refine ⟨?_, ?_, ?_⟩
  · intro X F W s
    have hs := hidentity (W.hom ≫ 𝟙 X) F
    have hr : Modules.etaleTensorSectionsRestriction F (trfEtaleIdArrow W) = 𝟙 _ := by
      exact hs
    rw [hr]
    exact hinverse (B := X) W.hom F s
  · intro X Y Z v w hv hw F W s
    have hs := hidentity ((W.hom ≫ w) ≫ v) F
    have hr : Modules.etaleTensorSectionsRestriction F (trfEtaleCompArrow v w W) =
        𝟙 _ := by
      exact hs
    rw [hr]
    have he := hassoc W.hom w v F
    exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤) he) s
  · intro X Y v hv W s
    rw [tensorUnit_hom, tensorUnit_hom, tensorUnit_hom]
    have h := tensorStructureMap_comp W.hom v
    have he : (Modules.tensorSectionsComp W.hom v).inv.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Modules.tensorPullback W.hom).map (Modules.tensorPullbackObjUnitToUnit v) ≫
        Modules.tensorPullbackObjUnitToUnit W.hom =
      Modules.tensorPullbackObjUnitToUnit (W.hom ≫ v) := by
      rw [← h, Iso.inv_hom_id_app_assoc]
    exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤) he) s

end

end AlgebraicGeometry.Scheme
