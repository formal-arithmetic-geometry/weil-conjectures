/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Paper.PointInverseEvaluationKFlat
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison

/-! # K-flat behavior of global tensor pullback

Source: Stacks Project, Tags 06YC and 06YJ, after the one-point module identification
of Tag 0B6A. (blueprint: lem-sc-global-tensor-pullback-kflat).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance globalKFlatDataCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalKFlatDataMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalKFlatDataSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalKFlatDataColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalKFlatDataPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalKFlatDataClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
set_option maxHeartbeats 800000 in
-- The sheaf equality transports and iterated termwise functors need extra elaboration.
/-- Global tensor pullback sends K-flat complexes to K-flat complexes and inverts
quasi-isomorphisms between K-flat objects after localization.
Source: Stacks Project, Tags 06YC, 06YJ, 079U and 06XN.
(blueprint: lem-sc-global-tensor-pullback-kflat)

Proof: point evaluation identifies sheaves on the one-point ringed space with modules
on its global ring. Evaluation commutes with tensor products (evaluate the sheafified
sectionwise tensor at the only nonempty open); its inverse is therefore monoidal.
Both directions are exact equivalences and preserve coproducts. Applying them termwise
preserves acyclicity and the total tensor, hence preserves K-flatness. The object and
morphism formulas identify P applied to a complex with concrete tensor pullback of its
image under the inverse equivalence, including the differentials. Pullback preserves
K-flatness by Tag 06YC. Inverse image is exact; extension of scalars preserves
quasi-isomorphisms between K-flat complexes by Tag 06YJ. Thus P preserves such
quasi-isomorphisms. Lift homotopy morphisms to cochain morphisms using fullness of the
quotient, and apply the quasi-isomorphism criterion for the quotient and localization.
The argument includes the zero ring, zero complex, and all unbounded complexes. -/
theorem globalTensorPullback_kflat
    (e : SheafOfModules.{u} (moduleRings (globalSectionsPoint X)) ≌
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      (he : Nonempty (e.functor ≅ RingedSpace.globalSectionsFunctor (globalSectionsPoint X)))
      (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
            ⟨(toGlobalSectionsPoint X).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
          (globalSectionsPoint X).sheaf (e.inverse.obj M)))
      (hm : ∀ {M N} (a : M ⟶ N), P.map a = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
            X.toRingedSpace.sheaf (globalSectionsPoint X).sheaf
              ⟨(toGlobalSectionsPoint X).hom.c⟩)
          (TopCat.Sheaf.inverseImageModule (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M))
          (TopCat.Sheaf.inverseImageModuleMap (toGlobalSectionsPoint X).hom.base
            (globalSectionsPoint X).sheaf (e.inverse.obj M) (e.inverse.map a)) ≫
          eqToHom (h N).symm)
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint] :
    (∀ K : HomotopyCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ),
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ∧
    (∀ K M : HomotopyCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ),
      ∀ a : K ⟶ M,
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat M →
        HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) a →
        IsIso ((P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map a)) := by
  let A := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let Y := globalSectionsPoint X
  have : Unique (globalSectionsPoint X) := inferInstanceAs (Unique PUnit.{u + 1})
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let I := TopCat.Sheaf.inverseImageModuleFunctor (toGlobalSectionsPoint X).hom.base Y.sheaf
  let φ := CochainComplex.tensorPullbackRingMap (toGlobalSectionsPoint X).hom.base
    X.toRingedSpace.sheaf Y.sheaf ⟨(toGlobalSectionsPoint X).hom.c⟩
  have inverse_isKFlat (K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ)
      (hK : K.IsKFlat) : CochainComplex.IsKFlat ((I.mapHomologicalComplex (.up ℤ)).obj K) := by
    obtain ⟨c⟩ := TopCat.Sheaf.exists_inverseImage_tensorPullback_iso
      (toGlobalSectionsPoint X).hom.base Y.sheaf K
    have ht := CochainComplex.isKFlat_pullback (toGlobalSectionsPoint X).hom.base
      (TopCat.Sheaf.inverseImageRing (toGlobalSectionsPoint X).hom.base Y.sheaf) Y.sheaf
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map (toGlobalSectionsPoint X).hom.base) CommRingCat.{u} _ _).unit.app Y.sheaf)
      K hK
    let := SheafOfModules.monoidalCategory
      (TopCat.Sheaf.inverseImageRing (toGlobalSectionsPoint X).hom.base Y.sheaf)
    intro F hF i
    exact (ht F hF i).of_iso
      (((curriedTensor _).map₂CochainComplex.obj F).mapIso c)
  have hp (K : CochainComplex A ℤ)
      (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
      CochainComplex.IsKFlat (R := X.toRingedSpace.sheaf)
        ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
    let K' : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ :=
      (e.inverse.mapHomologicalComplex (.up ℤ)).obj K
    have hK' : K'.IsKFlat := RingedSpace.pointInverseEvaluation_isKFlat Y e he K hK
    let c : (P.mapHomologicalComplex (.up ℤ)).obj K ≅
        CochainComplex.tensorPullbackComplex (toGlobalSectionsPoint X).hom.base
          X.toRingedSpace.sheaf Y.sheaf ⟨(toGlobalSectionsPoint X).hom.c⟩ K' :=
      HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (h (K.X i))) (by
        intro i j hij
        change eqToHom (h (K.X i)) ≫ _ = P.map (K.d i j) ≫ eqToHom (h (K.X j))
        rw [hm]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        rfl)
    have ht := CochainComplex.isKFlat_pullback (toGlobalSectionsPoint X).hom.base
      X.toRingedSpace.sheaf Y.sheaf ⟨(toGlobalSectionsPoint X).hom.c⟩ K' hK'
    intro F hF i
    exact (ht F hF i).of_iso
      (((curriedTensor _).map₂CochainComplex.obj F).mapIso c.symm)
  have hk (K : CochainComplex A ℤ)
      (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
      (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
        ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr : HomotopyCategory.subcategoryAcyclic B
        ((HomotopyCategory.quotient B (.up ℤ)).obj N ⊗
          (HomotopyCategory.quotient B (.up ℤ)).obj
            ((P.mapHomologicalComplex (.up ℤ)).obj K)) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hp K hK N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic B).prop_of_iso (β_ _ _) hr, hr⟩
  let E₀ : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing (toGlobalSectionsPoint X).hom.base Y.sheaf)) ⥤
      _root_.PresheafOfModules.{u} (moduleRings X.toRingedSpace).obj :=
    { obj := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
      map := fun a ↦
        { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u, u} φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro U
        simp
        rfl
      map_comp := by
        intro M N T a b
        apply PresheafOfModules.hom_ext
        intro U
        simp }
  let E := E₀ ⋙ PresheafOfModules.sheafification (𝟙 (moduleRings X.toRingedSpace).obj)
  have hscalar (U) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have hsheaf :
      (PresheafOfModules.sheafification (𝟙 (moduleRings X.toRingedSpace).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  have : E₀.Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro U
    simpa only [E₀, SheafOfModules.add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (φ.hom.app U).hom).map_add (f := a.val.app U) (g := b.val.app U)
  have : E.Additive := inferInstance
  have hE (M) : E.obj M = SheafOfModules.changeOfRings.{u, u, u} φ M := rfl
  have hEmap {M N} (a : M ⟶ N) : E.map a = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (hE N).symm := by
    simp [E, E₀, SheafOfModules.changeOfRingsHom]
  have hobj (M) : (e.inverse ⋙ I ⋙ E).obj M = P.obj M :=
    (hE (I.obj (e.inverse.obj M))).trans (h M).symm
  let c : e.inverse ⋙ I ⋙ E ≅ P :=
    NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) (by
      intro M N a
      dsimp
      rw [hEmap, hm]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      dsimp [hobj, I, TopCat.Sheaf.inverseImageModuleFunctor])
  have hq {K M : CochainComplex A ℤ} (a : K ⟶ M)
      (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K)
      (hM : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat M) (ha : QuasiIso a) :
      QuasiIso ((P.mapHomologicalComplex (.up ℤ)).map a) := by
    have : QuasiIso a := ha
    let a' := (e.inverse.mapHomologicalComplex (.up ℤ)).map a
    have hK' := RingedSpace.pointInverseEvaluation_isKFlat Y e he K hK
    have hM' := RingedSpace.pointInverseEvaluation_isKFlat Y e he M hM
    have ht := SheafOfModules.changeOfRings_kFlat_quasiIso φ E hE hEmap
      ((I.mapHomologicalComplex (.up ℤ)).map a')
      (inverse_isKFlat _ hK') (inverse_isKFlat _ hM') inferInstance
    let ec := Functor.mapHomologicalComplexCompIso c (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (ec.app K) (ec.app M) (ec.hom.naturality a).symm)).mp ht
  constructor
  · intro K hK
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    rw [HomotopyCategory.kFlat_quotient_obj_iff] at hK
    exact (HomotopyCategory.kFlat_quotient_obj_iff _).2 (hk K hK)
  · intro K M a hK hM ha
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨M, rfl⟩ := M.quotient_obj_surjective
    rw [HomotopyCategory.kFlat_quotient_obj_iff] at hK hM
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective a
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] at ha
    have ht := hq a hK hM ha
    change IsIso (DerivedCategory.Qh.map ((P.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient A (.up ℤ)).map a)))
    rw [P.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)

end
end AlgebraicGeometry.Scheme.Modules
