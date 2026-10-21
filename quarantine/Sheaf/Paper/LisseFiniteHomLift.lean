/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all Sheaf.Paper.CondensedFinitePresentationMatrices
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.Paper.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Sheaf.Paper.CondensedLocalCoefficientAdjoints
import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian

/-! # Finite-stage lifting of lisse coefficient morphisms

Source: the finite-descent-lisse blueprint proof, step 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma lisse_raw_cover
    {X : Scheme.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : IsLisseCoefficientModule Λ P) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ X)).obj P) := by
  obtain ⟨U, hU⟩ := hP
  refine ⟨U, fun i ↦ ?_⟩
  let φ := condensedPullbackHom Λ (U.f i)
  have h : Mod.IsFree _ ((Mod.comap (inv φ)).obj
      (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ X)).obj P)) := by
    exact free_of_iso (hU i) ((Mod.extendScalarsIsoComapInv φ).app _)
  exact free_of_comap (inv φ) h

private lemma lisse_hom_stage
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hP : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj P))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (c : Cocone D) (hc : IsColimit c) (a : P ⟶ c.pt) :
    ∃ (i : I) (b : P ⟶ D.obj i), b ≫ c.ι.app i = a := by
  let H := Mod.ihom P
  let : PreservesColimitsOfSize.{u + 1, u + 1} H :=
    condensed_locally_free_ihom_preservesColimits R P hP
  let e : (Mod.tensorLeft P).obj (Mod.regular R) ≅ P :=
    (Mod.relativeTensorRightIso P).app (Mod.regular R) ≪≫ (λ_ P)
  let a' := (Mod.ihomAdjunction P).homEquiv _ _ (e.hom ≫ a)
  let ch := H.mapCocone c
  have hch := isColimitOfPreserves H hc
  obtain ⟨i, b, hb⟩ := unitHom_stage X I _ ((Mod.forget R).mapCocone ch)
    (isColimitOfPreserves (Mod.forget R) hch) (η[R] ≫ a'.hom)
  let b' : Mod.regular R ⟶ H.obj (D.obj i) := Mod.regularLift _ b
  have hb' : b' ≫ H.map (c.ι.app i) = a' := by
    apply Mod.regular_hom_ext
    rw [Mod.comp_hom', ← Category.assoc, Mod.one_comp_regularLift]
    exact hb
  refine ⟨i, e.inv ≫ ((Mod.ihomAdjunction P).homEquiv _ _).symm b', ?_⟩
  apply (cancel_epi e.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply ((Mod.ihomAdjunction P).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact hb'
private lemma conjugation_of_mixed_factorization
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C] [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A : C}
    [MonObj R] [MonObj S] [MonObj A] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ A) [IsMonHom g]
    (k : R ⟶ A) [IsMonHom k] (h : f ≫ g = k)
    (M N : Mod C R)
    (b : M ⟶ (Mod.comap f).obj ((Mod.extendScalars f).obj N))
    (ψ : (Mod.extendScalars k).obj M ⟶ (Mod.extendScalars k).obj N)
    (hb : b ≫ Mod.mixedScalarMap f k f k g h h N =
      (Mod.extendRestrictAdjunction k).homEquiv _ _ ψ) :
    let c := Mod.extendScalarsIsoOfEq h.symm ≪≫ Mod.extendScalarsComp f g
    c.hom.app M ≫ (Mod.extendScalars g).map
      (((Mod.extendRestrictAdjunction f).homEquiv _ _).symm b) ≫ c.inv.app N = ψ := by
  dsimp only
  let t := ((Mod.extendRestrictAdjunction f).homEquiv _ _).symm b
  let c := Mod.extendScalarsIsoOfEq h.symm ≪≫ Mod.extendScalarsComp f g
  change c.hom.app M ≫ (Mod.extendScalars g).map t ≫ c.inv.app N = ψ
  apply (cancel_epi (c.inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply ((Mod.extendRestrictAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  apply ((Mod.extendRestrictAdjunction f).homEquiv _ _).injective
  apply Mod.hom_ext
  simp only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom', Mod.comap_map_hom]
  have ht : (Mod.extendUnit f M).hom ≫ t.hom = b.hom := by
    have hh := Equiv.apply_symm_apply ((Mod.extendRestrictAdjunction f).homEquiv _ _) b
    simpa only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
      Mod.comap_map_hom] using congrArg Mod.Hom.hom hh
  have hcunit (P : Mod C R) :
      (Mod.extendUnit f P).hom ≫
        (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom ≫
          (c.inv.app P).hom = (Mod.extendUnit k P).hom := by
    have heq := Adjunction.unit_leftAdjointUniq_hom_app
      (Mod.extendRestrictAdjunction k)
      ((Mod.extendRestrictAdjunction (f ≫ g)).ofNatIsoRight
        (Mod.comapCongr h.symm).symm) P
    have hcomp := Adjunction.unit_leftAdjointUniq_hom_app
      (Mod.extendRestrictAdjunction (f ≫ g))
      (((Mod.extendRestrictAdjunction f).comp (Mod.extendRestrictAdjunction g)).ofNatIsoRight
        (Mod.comapComp f g).symm) P
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_unit_app, scalar_unit] at heq hcomp
    have heq' := congrArg Mod.Hom.hom heq
    have hcomp' := congrArg Mod.Hom.hom hcomp
    change (Mod.extendUnit k P).hom ≫
        ((Mod.extendScalarsIsoOfEq h.symm).hom.app P).hom =
      (Mod.extendUnit (f ≫ g) P).hom ≫ 𝟙 _ at heq'
    change (Mod.extendUnit (f ≫ g) P).hom ≫
        ((Mod.extendScalarsComp f g).hom.app P).hom =
      ((Mod.extendUnit f P).hom ≫
        (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom) ≫ 𝟙 _ at hcomp'
    simp only [Category.comp_id] at heq' hcomp'
    have hh : (Mod.extendUnit k P).hom ≫ (c.hom.app P).hom =
        (Mod.extendUnit f P).hom ≫
          (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom := by
      change (Mod.extendUnit k P).hom ≫
        (((Mod.extendScalarsIsoOfEq h.symm).hom.app P).hom ≫
          ((Mod.extendScalarsComp f g).hom.app P).hom) = _
      rw [← Category.assoc, heq', hcomp']
    rw [← Category.assoc, ← hh, Category.assoc]
    have hi := congrArg Mod.Hom.hom (c.hom_inv_id_app P)
    change (c.hom.app P).hom ≫ (c.inv.app P).hom = 𝟙 _ at hi
    rw [hi]
    exact Category.comp_id _
  have hmix (P : Mod C R) :
      (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom ≫ (c.inv.app P).hom =
        (Mod.mixedScalarMap f k f k g h h P).hom := by
    have hm : (Mod.extendUnit f P).hom ≫
        (Mod.mixedScalarMap f k f k g h h P).hom = (Mod.extendUnit k P).hom := by
      dsimp only [Mod.mixedScalarMap, Mod.Hom.mk']
      exact Mod.extendUnitHom_extendHom f _
    let q : (Mod.extendScalars f).obj P ⟶
        (Mod.comap g).obj ((Mod.extendScalars k).obj P) :=
      (Mod.extendRestrictAdjunction g).homEquiv _ _ (c.inv.app P)
    let r : (Mod.extendScalars f).obj P ⟶
        (Mod.comap g).obj ((Mod.extendScalars k).obj P) :=
      (Mod.comapId S).inv.app _ ≫
        Mod.mixedScalarMap f k (𝟙 S) g g h (by simp) P
    have hr : r.hom = (Mod.mixedScalarMap f k f k g h h P).hom := by
      change 𝟙 _ ≫ (Mod.mixedScalarMap f k (𝟙 S) g g h (by simp) P).hom = _
      rw [Category.id_comp]
      rfl
    have hqr : q = r := by
      apply ((Mod.extendRestrictAdjunction f).homEquiv _ _).injective
      apply Mod.hom_ext
      simp only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom', Mod.comap_map_hom]
      simpa only [hr, q, Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
        Mod.comap_map_hom] using (hcunit P).trans hm.symm
    simpa only [q, Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
      Mod.comap_map_hom] using (congrArg Mod.Hom.hom hqr).trans hr
  change (Mod.extendUnit f M).hom ≫
      (t.hom ≫ (Mod.extendUnit g ((Mod.extendScalars f).obj N)).hom ≫
        (c.inv.app N).hom) = _
  calc
    _ = b.hom ≫ ((Mod.extendUnit g ((Mod.extendScalars f).obj N)).hom ≫
        (c.inv.app N).hom) := by rw [← Category.assoc, ht]
    _ = b.hom ≫ (Mod.mixedScalarMap f k f k g h h N).hom := congrArg (b.hom ≫ ·) (hmix N)
    _ = (Mod.extendUnit k M).hom ≫ ψ.hom := by
      simpa only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
        Mod.comap_map_hom] using congrArg Mod.Hom.hom hb
    _ = _ := by rw [← hcunit M]; simp only [Category.assoc]

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- A morphism of algebraic-closure extensions of two lisse finite-field modules
is obtained at a finite field. This asserts only existence of representatives, not their
comparison or equality relation.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-lisse.proof.md, proof (2),
surjectivity paragraph (blueprint: lem-sfb-lisse-finite-hom-lift).

Proof in words: remove the invertible coefficient pullback from the local free
trivializations. Internal Hom out of this locally finite free module preserves small
colimits by the existing internal-Hom theorem. Use the filtered final category of finite
coefficient fields above E. The existing coefficient complex colimit, evaluated in degree
zero on N concentrated in degree zero, expresses its restricted closure extension as the
colimit of restricted finite scalar extensions. Transpose the given map by scalar
adjunction and then by internal-Hom adjunction. The qcqs unit-Hom stage lemma factors the
result through a finite stage of the internal-Hom diagram. Transpose back by both
adjunctions. Finally, calculate the units of the canonical scalar-extension comparison:
the mixed scalar cocone map is the composite of the larger-field unit and the inverse
comparison. This gives exactly the conjugation equation in the conclusion. Neither a
constant rank nor nonemptiness is required. -/
theorem exists_lisse_finite_hom_lift [CompactSpace X] [QuasiSeparatedSpace X]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) M)
    (hN : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) N)
    (ψ : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj M ⟶
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F)
      (φ : (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj M ⟶
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj N),
      let c := Mod.extendScalarsIsoOfEq
          (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h).symm ≪≫
        Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
          (padicSubfieldRingObjToPadicAlgCl X ℓ F)
      c.hom.app M ≫
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).map φ ≫
          c.inv.app N = ψ := by
  have _ := hN
  let C := (HomologicalComplex.single _ (.up ℤ) 0).obj N
  let I := AsSmall.{u + 1} (Under E)
  let H : I ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E
  let : H.Final := by dsimp only [H]; infer_instance
  let he (i : I) : E ≤ H.obj i := leOfHom (ULift.down i).hom
  let : HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
    inferInstance
  let c := (HomologicalComplex.eval _ (.up ℤ) 0).mapCocone
    (coefficientComplexCocone X ℓ (E := E) (F := E) C H he he)
  have hc : IsColimit c := isColimitOfPreserves _
    (Classical.choice (nonempty_isColimit_coefficientComplexCocone X ℓ
      (E := E) (F := E) C H he he))
  let a := (Mod.extendRestrictAdjunction
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)).homEquiv _ _ ψ
  obtain ⟨i, b, hb⟩ := lisse_hom_stage (padicSubfieldRingObj X ℓ E) M
    (lisse_raw_cover (Profinite.continuousMapRingObj E) M hM) c hc a
  refine ⟨H.obj i, he i,
    ((Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ (he i))).homEquiv _ _).symm b,
    ?_⟩
  exact conjugation_of_mixed_factorization
    (padicSubfieldRingObjMap X ℓ (he i))
    (padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i))
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)
    (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (he i)) M N b ψ hb

end AlgebraicGeometry.ProEtale
