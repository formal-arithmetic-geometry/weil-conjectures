/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.SixFunctors.IntegralRestrictionFunctors

import all Sheaf.Paper.SignedLineTensorEquivalence
import all Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import all Sheaf.Paper.ContinuousLissePullbackSystem
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-! # Constructibility of the internal integral Tate line

Source: current blueprint, sk-thm-int-restriction-line.proof.md, paragraph (3),
and sk-def-sp-tate-twist, local-generator and signed-power paragraphs.
(blueprint: lem-sfb-integral-tate-line-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local irreducible] spIntegralTwist

private abbrev literalRestriction {X : Scheme.{u}} (U : X.ProEt) :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤ Sheaf (ProEt.topology U.left) Ab.{u + 1} :=
  let : (MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  Functor.sheafPushforwardContinuous
    (MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop)
    Ab.{u + 1} (ProEt.topology U.left) (ProEt.topology X)

set_option backward.isDefEq.respectTransparency false in
private instance {X : Scheme.{u}} (U : X.ProEt) : (literalRestriction U).LaxMonoidal := by
  dsimp only [literalRestriction]
  infer_instance

-- A sectionwise linear trivialization is linear for literal restriction as well.
private noncomputable def sliceInternalIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (U : X.ProEt)
    (e : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj M).over U ≅
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).functor.obj (Mod.regular R)).over U) :
    ((literalRestriction U).mapMod R).obj M ≅
      ((literalRestriction U).mapMod R).obj
        (Mod.regular R) := by
  let G := MorphismProperty.Over.map (P := @WeaklyEtale.{u}) (f := U.hom) ⊤ U.prop
  have : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  have : (ProEt.sliceFrom X U).IsDenseSubsite (ProEt.topology U.left)
      ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let q : (literalRestriction U).obj M.X ≅ (literalRestriction U).obj R :=
    ((ProEt.sliceFrom X U).sheafPushforwardContinuous Ab.{u + 1}
    (ProEt.topology U.left) ((ProEt.topology X).over U)).mapIso
      ((SheafOfModules.toSheaf _).mapIso e)
  have hq (V : U.left.ProEtᵒᵖ)
      (r : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (ProEt.topology X) R).obj (G.op.obj V))
      (m : ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
        (ProEt.topology X) R).obj M).val.obj (G.op.obj V)) :
      (q.hom.hom.app V).hom (r • m) =
        r • (show ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
          (ProEt.topology X) R).obj (Mod.regular R)).val.obj (G.op.obj V) from
          (q.hom.hom.app V).hom m) := by
    exact (e.hom.val.app (op ((ProEt.sliceFrom X U).obj V.unop))).hom.map_smul r m
  clear_value q
  refine Mod.isoMk q ?_
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  change Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
      ((literalRestriction U).obj R) ((literalRestriction U).obj M.X) ≫
      (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1}).map
        (Mod.act (((literalRestriction U).mapMod R).obj M).X) ≫
      (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1}).map q.hom = _
  erw [← Functor.LaxMonoidal.μ_natural_right_assoc
    (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
    ((literalRestriction U).obj R) q.hom]
  ext V : 2
  simp only [NatTrans.comp_app]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro r m
  have hM := (by
    set_option backward.isDefEq.respectTransparency false in
      exact InternalModuleOperations.section_action
        (ProEt.topology U.left) (ProEt.topology X) G R
        ((literalRestriction U).obj R) M.X (𝟙 _) (Mod.act M.X) V r m)
  have hR := (by
    set_option backward.isDefEq.respectTransparency false in
      exact InternalModuleOperations.section_action
        (ProEt.topology U.left) (ProEt.topology X) G R
        ((literalRestriction U).obj R) R (𝟙 _) (Mod.act (Mod.regular R).X) V r
        ((q.hom.hom.app V).hom m))
  set_option backward.isDefEq.respectTransparency false in
    simp only [id_whiskerRight, Category.id_comp] at hM hR
  change (q.hom.hom.app V).hom
      (((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
        ((literalRestriction U).obj R) ((literalRestriction U).obj M.X)).app V ≫
        (Mod.act (((literalRestriction U).mapMod R).obj M).X).hom.app V).hom
          (r ⊗ₜ[ℤ] m)) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
      ((literalRestriction U).obj R) ((literalRestriction U).obj R)).app V ≫
      (Mod.act (((literalRestriction U).mapMod R).obj (Mod.regular R)).X).hom.app V).hom
        (r ⊗ₜ[ℤ] (q.hom.hom.app V).hom m)
  have hm' :
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
        ((literalRestriction U).obj R) ((literalRestriction U).obj M.X)).app V ≫
        (Mod.act (((literalRestriction U).mapMod R).obj M).X).hom.app V).hom
          (r ⊗ₜ[ℤ] m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
        R M.X).app (G.op.obj V) ≫ (Mod.act M.X).hom.app (G.op.obj V)).hom
          (r ⊗ₜ[ℤ] m) := by
    exact hM
  have hr' :
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U.left) Ab.{u + 1})
        ((literalRestriction U).obj R) ((literalRestriction U).obj R)).app V ≫
        (Mod.act (((literalRestriction U).mapMod R).obj (Mod.regular R)).X).hom.app V).hom
          (r ⊗ₜ[ℤ] (q.hom.hom.app V).hom m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
        R R).app (G.op.obj V) ≫ (Mod.act (Mod.regular R).X).hom.app (G.op.obj V)).hom
          (r ⊗ₜ[ℤ] (q.hom.hom.app V).hom m) := by
    exact hR
  rw [hm', hr']
  exact hq V r m

attribute [local irreducible] sliceInternalIso

set_option backward.isDefEq.respectTransparency false in
private theorem free_via_monoidalIso {X Y : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (F G : Sheaf (ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology Y) Ab.{u + 1}) [F.LaxMonoidal] [G.LaxMonoidal]
    (τ : F ≅ G) [NatTrans.IsMonoidal τ.hom]
    (hG : Mod.IsFree (G.obj R) ((G.mapMod R).obj M)) :
    Mod.IsFree (F.obj R) ((F.mapMod R).obj M) := by
  exact ProEtale.free_of_iso (ProEtale.free_comap (τ.hom.app R) hG)
    ((Functor.mapModNatIso τ R).app M).symm

set_option backward.isDefEq.respectTransparency false in
private theorem free_of_slice_trivial (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (U : X.ProEt)
    (e : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj M).over U ≅
      (SheafOfModules.unit _).over U) :
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} U.hom).obj R)
      (((ProEtale.upperStar Ab.{u + 1} U.hom).mapMod R).obj M) := by
  let e₀ :
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).functor.obj (Mod.regular R) ≅ SheafOfModules.unit _ := by
    let i :
        ((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
          (ProEt.topology X) R).obj (Mod.regular R)).val ≅ (SheafOfModules.unit _).val :=
      PresheafOfModules.isoMk
        (fun _ ↦ ModuleCat.isoMk (Iso.refl _) (by intro r; ext x; rfl))
        (by intro U V f; rfl)
    exact
      { hom := ⟨i.hom⟩
        inv := ⟨i.inv⟩
        hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
        inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }
  clear_value e₀
  let er := e ≪≫ (SheafOfModules.overFunctor _ U).mapIso e₀.symm
  let q := sliceInternalIso X R M U er
  clear_value q
  let F := literalRestriction U
  let reg : (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  clear_value reg
  have hF : Mod.IsFree (F.obj R) ((F.mapMod R).obj M) := by
    exact ⟨1, ⟨q ≪≫ reg ≪≫ (biproductUniqueIso
      (fun _ : Fin 1 ↦ Mod.regular (F.obj R))).symm⟩⟩
  let τ : ProEtale.upperStar Ab.{u + 1} U.hom ≅ literalRestriction U :=
    upperStarIsoSheafPushforward Ab.{u + 1} U.hom U.prop
  have : NatTrans.IsMonoidal τ.hom := inferInstance
  clear_value τ
  exact free_via_monoidalIso R M (ProEtale.upperStar Ab.{u + 1} U.hom)
    (literalRestriction U) τ hF

private theorem locallyFree_of_trivial_cover (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (he : ∀ i, Nonempty (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj M).over (U i) ≅
      (SheafOfModules.unit _).over (U i))) :
    CondensedRing.LocallyFree R M := by
  classical
  have hmem : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage X := by
    have h := (ProEt.mem_precoverage_iff).mp hc
    rw [Presieve.map_ofArrows] at h
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at h
    have hf : (fun i ↦ (f i).left) = (fun i ↦ (U i).hom) := by
      funext i
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 X = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    rwa [hf] at h
  let : Precoverage.Small.{u} proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (propQCPrecoverage @WeaklyEtale))
  let C : Scheme.Cover.{u + 1} proetalePrecoverage X :=
    { I₀ := I, X := fun i ↦ (U i).left, f := fun i ↦ (U i).hom, mem₀ := hmem }
  let D := C.restrictIndexOfSmall.{u}
  refine ⟨D, fun i ↦ ?_⟩
  exact free_of_slice_trivial X R M (U (Precoverage.ZeroHypercover.Small.restrictFun C i))
    (he _).some

private noncomputable def signedOverUnit (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (U : X.ProEt)
    (e : (spSignedTwist X R L 1).over U ≅ (spSignedTwist X R L 0).over U)
    (d : ℤ) : (spSignedTwist X R L d).over U ≅ (SheafOfModules.unit _).over U := by
  exact WeilConjectures.lineSignedOverUnit.{u} X
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) R)
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) R).functor.obj L)
    U e d

private theorem bounded_single_of_locallyFree (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (h : CondensedRing.LocallyFree R M) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have hM := CondensedRing.locallyFree_constructible h
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ 0 n hn)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ 0 n hn)

private theorem bounded_signed_of_cover (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) (d : ℤ)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (hi : ∀ i, Nonempty ((spSignedTwist X R L 1).over (U i) ≅
      (spSignedTwist X R L 0).over (U i))) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) R).inverse.obj
        (spSignedTwist X R L d))) := by
  classical
  let S := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) R
  let M := S.inverse.obj (spSignedTwist X R L d)
  have he (i : I) : Nonempty ((S.functor.obj M).over (U i) ≅
      (SheafOfModules.unit _).over (U i)) := by
    exact ⟨(SheafOfModules.overFunctor _ (U i)).mapIso (S.counitIso.app _) ≪≫
      signedOverUnit X R L (U i) (hi i).some d⟩
  exact bounded_single_of_locallyFree X R M
    (locallyFree_of_trivial_cover X R M U f hc he)

/-- The actual internal-module realization of every signed integral Tate line is
constructible in degree zero.

Source: sk-def-sp-tate-twist, local-generator and signed-power paragraphs;
sk-thm-int-restriction-line.proof.md, paragraph (3).
(blueprint: lem-sfb-integral-tate-line-constructible).

Proof: trivialize the degree-one integral line on the compatible-root pro-etale
cover. The section-module equivalence retains the underlying abelian sheaf and
scalar action. Its pullback comparison identifies restriction of the internal
line with restriction of the sectionwise line. On that cover every nonnegative
power is the tensor power of the regular rank-one module, and every negative
power is its dual; multiplication and evaluation identify these with the regular
module. These trivializations are compatible with restriction. Thus the internal
line has a rank-one finite presentation on this cover. Use the trivial single
stratum, including for the empty scheme, to obtain constructibility. The single
complex has this cohomology in degree zero and zero in every other degree,
so it is bounded constructible. -/
theorem integralTateLine_constructible (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (d : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
      ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X d)) := by
  classical
  obtain ⟨I, U, f, ζ, e, hc, _, _, _, hi, _⟩ := spTwists_commonCover X ℓ
  exact bounded_signed_of_cover X _ (spIntegralTwist X ℓ E) d U f hc
    (fun i ↦ (hi E i).1)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
