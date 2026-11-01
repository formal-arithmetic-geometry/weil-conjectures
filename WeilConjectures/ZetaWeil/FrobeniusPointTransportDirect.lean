/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!
# Direct condensed Frobenius point transport

This module states the direct point-fibre transport for geometric Frobenius.  The
construction uses the native sheafified-Kan upper-star and its unit-normalized
comparison with the identity.  At a representative `Q(C)`, the named
termwise-formula theorem below records the restriction `M(r)`, the normalized
inverse-image comparison `e_M⁻¹`, the module insertion `j_M(x)=1⊗x`, and the
finite-coefficient insertion normalization.

Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151;
(blueprint: def-weil-frobenius-point-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open Opposite
open scoped CategoryTheory.Obj
namespace WeilConjectures

private theorem section_smul_global
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf J Ab.{u + 1}) R) (U : C) (r : MonObj.Γ R) :
    ((CondensedRing.Evaluation.sections J R U).obj M).smul
        (InternalAbelianSheafModule.sectionGlobalEval J R U r) =
      (Mod.globalSmul r.hom M).hom.app (op U) := by
  let F := sheafToPresheaf J Ab.{u + 1}
  let E := (evaluation Cᵒᵖ Ab.{u + 1}).obj (op U)
  let _ : E.Monoidal :=
    Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }
  have h := Mod.globalSmul_mapMod (F ⋙ E) r.hom M
  change _ = (F ⋙ E).map (Mod.globalSmul r.hom M)
  rw [← h]
  ext x
  rfl

private theorem evaluation_nat_linear
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : Sheaf J Ab.{u + 1} ⥤ Sheaf K Ab.{u + 1}) [F.LaxMonoidal] [F.Additive]
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] [IsCommMonObj (F.obj R)]
    (U : C) (V : D)
    (δ : (sheafSections J Ab.{u + 1}).obj (op U) ⟶
      F ⋙ (sheafSections K Ab.{u + 1}).obj (op V))
    (M : Mod (Sheaf J Ab.{u + 1}) R) (r : MonObj.Γ R) :
    δ.app M.X ≫
      ((CondensedRing.Evaluation.sections K (F.obj R) V).obj ((F.mapMod R).obj M)).smul
        (InternalAbelianSheafModule.sectionGlobalEval K (F.obj R) V
          (MonObj.Γ.mapFunctor F r)) =
      ((CondensedRing.Evaluation.sections J R U).obj M).smul
        (InternalAbelianSheafModule.sectionGlobalEval J R U r) ≫ δ.app M.X := by
  have htarget :
      ((CondensedRing.Evaluation.sections K (F.obj R) V).obj ((F.mapMod R).obj M)).smul
        (InternalAbelianSheafModule.sectionGlobalEval K (F.obj R) V
          (MonObj.Γ.mapFunctor F r)) =
      (F.map (Mod.globalSmul r.hom M)).hom.app (op V) := by
    refine (section_smul_global K (F.obj R) ((F.mapMod R).obj M) V
      (MonObj.Γ.mapFunctor F r)).trans ?_
    exact congrArg (fun f : F.obj M.X ⟶ F.obj M.X ↦ f.hom.app (op V))
      (Mod.globalSmul_mapMod F r.hom M)
  calc
    _ = δ.app M.X ≫ (F.map (Mod.globalSmul r.hom M)).hom.app (op V) :=
      congrArg (fun f ↦ δ.app M.X ≫ f) htarget
    _ = (Mod.globalSmul r.hom M).hom.app (op U) ≫ δ.app M.X :=
      (δ.naturality (Mod.globalSmul r.hom M)).symm
    _ = _ := congrArg (fun f ↦ f ≫ δ.app M.X) (section_smul_global J R M U r).symm

/-- The terminal profinite object and the singleton test object are identified by their
canonical terminal structures.  This is the object-level transport used in the point-unit map.
Source: Bhatt--Scholze, Example 4.1.10; (blueprint: def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusTopToSingleton :
    (⊤_ Profinite.{u}) ≅ Profinite.of (ULift.{u, 0} PUnit.{1}) := by
  let S := Profinite.of (ULift.{u, 0} PUnit.{1})
  let hS : IsTerminal S :=
    IsTerminal.ofUniqueHom
      (fun _ ↦ ConcreteCategory.ofHom
        ⟨fun _ ↦ default, continuous_const⟩)
      (fun _ _ ↦ by ext)
  let q : (⊤_ Profinite.{u}) ⟶ S := hS.from _
  let q' : S ⟶ (⊤_ Profinite.{u}) := terminal.from S
  refine { hom := q, inv := q', hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply terminal.hom_ext
  · apply hS.hom_ext

/-- The module category on the small pro-etale site of `Spec k`.

Source: `def-weil-pbc-proetale-site` and `det-def-sfb-condensed-ring`;
(blueprint: def-weil-frobenius-point-transport). -/
abbrev directFrobeniusModule
    (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
    (condensedRingObj Λ (Spec (.of D.k)))

/-- The normalized inverse-image comparison followed by restriction on the identity
pro-etale object.

Source: `lem-route-exists-unique-pro-etale-iso-inverse-image-identification`;
(blueprint: def-weil-frobenius-point-transport).  This is the actual section map
`e_M⁻¹ ∘ M(r)`; it is kept separate from the derived transport so that the
representative formula is explicit. -/
def directFrobeniusSigmaSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) ⟶
      (((frobeniusPointIso D).hom)^*[Ab.{u + 1}].obj
        ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) := by
  let e := AlgebraicGeometry.Scheme.proEtaleIsoInverseImageIdentification
    (frobeniusPointIso D).hom Ab.{u + 1}
  exact
    ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M).obj.map
        (frobeniusPointRestriction D).op ≫
      (e.inv.app ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M)).app
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))

/-- The tensor-unit insertion `j_M(x)=1⊗x`, evaluated on the identity object.

Source: `det-def-sfb-module-pushforward-pullback`; (blueprint:
def-weil-frobenius-point-transport). -/
def directFrobeniusInsertionSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    (((frobeniusPointIso D).hom)^*[Ab.{u + 1}].obj
        ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) ⟶
      ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj
        ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ
          (frobeniusPointIso D).hom).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) := by
  let N := (((frobeniusPointIso D).hom)^*[Ab.{u + 1}].mapMod
      (condensedRingObj Λ (Spec (.of D.k)))).obj M
  exact
    (Mod.extendUnitHom (condensedPullbackHom Λ (frobeniusPointIso D).hom) N).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))

/-- The underived chain-level point map `i_C=Γ(j_C)∘σ_C`, before localization.

Source: the displayed formula in `def-weil-frobenius-point-transport`; (blueprint:
def-weil-frobenius-point-transport). -/
def directFrobeniusTermwiseSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj M).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) ⟶
      ((Mod.forget (condensedRingObj Λ (Spec (.of D.k)))).obj
        ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ
          (frobeniusPointIso D).hom).obj M)).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) :=
  directFrobeniusSigmaSections D Λ M ≫ directFrobeniusInsertionSections D Λ M

/-- The scalar sections functor used for the termwise formula.

Source: the canonical scalar-sections construction in
`lem-weil-condensed-isomorphism-cohomology-transport`; (blueprint:
def-weil-frobenius-point-transport). -/
abbrev directFrobeniusSections (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    directFrobeniusModule D Λ ⥤ ModuleCat.{u + 1} (condensedScalarRing Λ) :=
  CondensedRing.CohomologyTransport.sections Λ (Spec (.of D.k))

end WeilConjectures
