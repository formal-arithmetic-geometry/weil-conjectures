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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact

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

/-- The concrete section map supplied by the geometric point adjunction.  It is the
adjunction unit at the singleton, followed by the inverse of the specified final-object map;
the first factor transports sections from the terminal profinite object to the singleton.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11; (blueprint:
 def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusPointSectionsEvaluationMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    P.X.obj.obj (op (⊤_ Profinite.{u})) ⟶
      (((((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).functor.obj P).X.obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ) := by
  let S := Profinite.of (ULift.{u, 0} PUnit.{1})
  letI : IsIso (geometricFieldTestFinalMap (Spec (.of k))) :=
    (geometric_field_proetale_evaluation k).2.2.2.2.2.2.2.1
  exact
    P.X.obj.map (directFrobeniusTopToSingleton).inv.op ≫
      ((geometricFieldAbelianPointAdjunction (Spec (.of k))).unit.app P.X).hom.app (op S) ≫
      (((((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).functor.obj P).X.obj.map
        (inv (geometricFieldTestFinalMap (Spec (.of k)))).op)

/-- The point-unit map is invertible.  Invertibility is the module form of the
invertible abelian point-adjunction unit and of the singleton final-object map in
`geometric_field_proetale_evaluation`; the terminal/singleton transport is an isomorphism.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11; (blueprint:
 def-weil-frobenius-point-transport). -/
theorem directFrobeniusPointSectionsEvaluationMap_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    IsIso (directFrobeniusPointSectionsEvaluationMap Λ k P) := by
  have : IsIso (geometricFieldTestFinalMap (Spec (.of k))) :=
    (geometric_field_proetale_evaluation k).2.2.2.2.2.2.2.1
  have : IsIso (geometricFieldAbelianPointAdjunction (Spec (.of k))).unit :=
    (geometric_field_proetale_evaluation k).2.2.2.2.2.1
  unfold directFrobeniusPointSectionsEvaluationMap
  infer_instance

/-- The explicit point-unit map is linear over terminal condensed scalars.
Source: Bhatt--Scholze, Example 4.2.11;
(blueprint: def-weil-frobenius-point-transport).

Proof: express the scalar action by the module action composed with a global scalar.
Naturality of the point-adjunction unit intertwines this action with its pullback.
Restriction along the terminal/singleton isomorphism and along the inverse final-object
map preserves multiplication. The resulting scalar is exactly `scalarMap`, since that
map is induced by the same strong monoidal point pullback. -/
theorem directFrobeniusPointSectionsEvaluationMap_linear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    ∀ r : condensedScalarRing Λ,
      directFrobeniusPointSectionsEvaluationMap Λ k P ≫
          (((((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).functor ⋙
            CondensedRing.CohomologyTransport.sections Λ (Spec (.of k))).obj P).smul r =
        ((CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
          (⊤_ Profinite.{u})).obj P).smul r ≫
            directFrobeniusPointSectionsEvaluationMap Λ k P := by
  intro r
  let F := upperStarFromPoint (Spec (.of k))
  have : PreservesFiniteLimits F := by
    dsimp [F]
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  let _ := Functor.additive_of_preserves_binary_products F
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology (Spec (.of k))
  let t := ProEt.mk (𝟙 (Spec (.of k)))
  let δ := pointSectionsNat k
  let e := InternalAbelianSheafModule.sectionGlobalEquiv J Λ
    (⊤_ Profinite.{u}) terminalIsTerminal
  let a := e.symm r
  have ha : InternalAbelianSheafModule.sectionGlobalEval J Λ
      (⊤_ Profinite.{u}) a = r := e.apply_symm_apply r
  have h := evaluation_nat_linear J K F Λ (⊤_ Profinite.{u}) t δ P a
  rw [ha] at h
  exact h

/-- The linear lift of the explicit point-adjunction section map.
Source: Bhatt--Scholze, Example 4.2.11;
(blueprint: def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusPointSectionsModuleMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})).obj P ⟶
      (((((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).functor ⋙
        CondensedRing.CohomologyTransport.sections Λ (Spec (.of k))).obj P) :=
  ModuleCat.homMk (directFrobeniusPointSectionsEvaluationMap Λ k P)
    (directFrobeniusPointSectionsEvaluationMap_linear Λ k P)

/-- Naturality of the linear point-unit map.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11;
(blueprint: def-weil-frobenius-point-transport).

Proof: evaluate naturality of the point-adjunction unit at the singleton. Commute
module maps past the restrictions along the terminal/singleton isomorphism and inverse
final-object map by their sheaf naturality. Faithfulness of the module forgetful functor
then gives the displayed module equation. -/
theorem directFrobeniusPointSectionsModuleMap_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (P P' : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) (f : P ⟶ P') :
    (CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})).map f ≫ directFrobeniusPointSectionsModuleMap Λ k P' =
      directFrobeniusPointSectionsModuleMap Λ k P ≫
        (((((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).functor ⋙
          CondensedRing.CohomologyTransport.sections Λ (Spec (.of k))).map f) := by
  apply (forget₂ (ModuleCat (condensedScalarRing Λ)) Ab).map_injective
  exact (pointSectionsNat k).naturality f.hom

/-- The natural transformation whose components are the explicit linear point-unit maps.
Source: Bhatt--Scholze, Example 4.2.11;
(blueprint: def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusPointSectionsEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u}) ⟶
      ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence.functor ⋙
        CondensedRing.CohomologyTransport.sections Λ (Spec (.of k)) where
  app := directFrobeniusPointSectionsModuleMap Λ k
  naturality := fun {P P'} f ↦ directFrobeniusPointSectionsModuleMap_naturality Λ k P P' f

/-- The explicit point-unit natural transformation is invertible.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11;
(blueprint: def-weil-frobenius-point-transport).

Proof: each underlying additive component is invertible by
`directFrobeniusPointSectionsEvaluationMap_isIso`, using the invertible abelian
point-adjunction unit and final-object map of `geometric_field_proetale_evaluation`.
The module forgetful functor reflects isomorphisms. Componentwise invertibility then
makes this particular natural transformation invertible. -/
theorem directFrobeniusPointSectionsEvaluation_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    IsIso (directFrobeniusPointSectionsEvaluation Λ k) := by
  have (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
      IsIso ((directFrobeniusPointSectionsEvaluation Λ k).app P) := by
    have : IsIso ((forget₂ (ModuleCat (condensedScalarRing Λ)) Ab).map
        ((directFrobeniusPointSectionsEvaluation Λ k).app P)) :=
      directFrobeniusPointSectionsEvaluationMap_isIso Λ k P
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat (condensedScalarRing Λ)) Ab)
  exact NatIso.isIso_of_isIso_app _

/-- The canonical point-section comparison, the inverse of the explicit linear
point-adjunction unit at the singleton followed by the inverse final-object map.
Its data is fixed by `directFrobeniusPointSectionsEvaluation`; only the proof of
invertibility is postponed.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11;
(blueprint: def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusPointSectionsEvaluationIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence.functor ⋙
        CondensedRing.CohomologyTransport.sections Λ (Spec (.of k)) ≅
      CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
        (⊤_ Profinite.{u}) := by
  letI := directFrobeniusPointSectionsEvaluation_isIso Λ k
  exact (asIso (directFrobeniusPointSectionsEvaluation Λ k)).symm

/-- Canonical heart-fibre/sections natural isomorphism.  It is obtained by whiskering
`directFrobeniusPointSectionsEvaluationIso` with the inverse point equivalence and then
using its counit; hence it is fixed by the point adjunction.
Source: the point-topos unit and site comparison above; (blueprint:
 def-weil-frobenius-point-transport). -/
noncomputable def directFrobeniusHeartSectionsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    AlgebraicGeometry.ProEtale.CondensedGeometricPoint.heartFiber Λ k ≅
      CondensedRing.CohomologyTransport.sections Λ (Spec (.of k)) := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let a := directFrobeniusPointSectionsEvaluationIso Λ k
  let b := Functor.associator e.inverse e.functor
      (CondensedRing.CohomologyTransport.sections Λ (Spec (.of k))) ≪≫
    Functor.isoWhiskerLeft e.inverse a
  exact b.symm ≪≫ Functor.isoWhiskerRight e.counitIso
    (CondensedRing.CohomologyTransport.sections Λ (Spec (.of k))) ≪≫
    Functor.leftUnitor _

/-- The direct condensed derived pullback along geometric Frobenius.

Source: the direct upper-star construction in the blueprint
(blueprint: def-weil-frobenius-point-transport).  The native sheafified Kan extension is
followed by `mapDerivedCategory`; the derived tensor and point-fibre
comparisons are the canonical ones supplied by the imported dependency modules.
-/
def directFrobeniusPullback (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    AlgebraicGeometry.ProEtale.CondensedGeometricPoint.Complexes Λ D.k ⥤
      AlgebraicGeometry.ProEtale.CondensedGeometricPoint.Complexes Λ D.k :=
  (CondensedRing.upperStar Λ (frobeniusPointIso D).hom).mapDerivedCategory

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

/-- Linearity of the explicit restriction/inverse-image/tensor-unit composite.
Source: the scalar-action calculation in Step 2 of the node;
(blueprint: def-weil-frobenius-point-transport).

Proof: a scalar in `Λ(*)` gives a global scalar sheaf map by point pullback. Naturality
of the normalized inverse-image comparison intertwines multiplication by that scalar.
The monoidal point-pullback compositor `alpha` fixes this global scalar, and the action
on the transported module is through `alpha` inverse. Finally `Mod.extendUnitHom` is
linear, so composing it with sigma gives the asserted scalar equation. -/
theorem directFrobeniusTermwiseSections_linear (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    ∀ r, directFrobeniusTermwiseSections D Λ M ≫
        ((directFrobeniusSections D Λ).obj
          ((CondensedRing.upperStar Λ (frobeniusPointIso D).hom).obj M)).smul r =
      ((directFrobeniusSections D Λ).obj M).smul r ≫
        directFrobeniusTermwiseSections D Λ M := by
  intro r
  let p := upperStarFromPoint (Spec (.of D.k))
  let φ := MonObj.Γ.mapFunctor p (R := Λ)
  let _ := Mod.linearOfRingHom φ
  let F := CondensedRing.upperStar Λ (frobeniusPointIso D).hom
  let _ : F.Linear (MonObj.Γ Λ) := condensedModulePullback_linear Λ _
  let e := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
  let a := e.symm r
  have hF : (F.map ((Mod.smulNatTrans (φ a).hom).app M)).hom =
      Mod.globalSmul (φ a).hom (F.obj M) := by
    have h := F.map_smul a (𝟙 M)
    rw [F.map_id, Mod.linearOfRingHom_smul_id, Mod.linearOfRingHom_smul_id] at h
    exact congrArg Mod.Hom.hom h
  have h := termwiseSections_naturality D Λ M M ((Mod.smulNatTrans (φ a).hom).app M)
  rw [hF] at h
  change directFrobeniusTermwiseSections D Λ M ≫
      ((CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of D.k)))
        (condensedRingObj Λ (Spec (.of D.k))) (ProEt.mk (𝟙 (Spec (.of D.k))))).obj
        (F.obj M)).smul (InternalAbelianSheafModule.sectionGlobalEval
          (Scheme.ProEt.topology (Spec (.of D.k))) (condensedRingObj Λ (Spec (.of D.k)))
          (ProEt.mk (𝟙 (Spec (.of D.k)))) (φ a)) =
    ((CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of D.k)))
      (condensedRingObj Λ (Spec (.of D.k))) (ProEt.mk (𝟙 (Spec (.of D.k))))).obj M).smul
        (InternalAbelianSheafModule.sectionGlobalEval
          (Scheme.ProEt.topology (Spec (.of D.k))) (condensedRingObj Λ (Spec (.of D.k)))
          (ProEt.mk (𝟙 (Spec (.of D.k)))) (φ a)) ≫ directFrobeniusTermwiseSections D Λ M
  rw [section_smul_global, section_smul_global]
  exact h.symm

/-- The linear section map `Γ(j_M) ∘ e_M⁻¹ ∘ M(r)` with its specified scalar actions.
Source: Steps 2 and 3 of the node;
(blueprint: def-weil-frobenius-point-transport). -/
def directFrobeniusTermwiseModuleMap (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M : directFrobeniusModule D Λ) :
    (directFrobeniusSections D Λ).obj M ⟶
      (directFrobeniusSections D Λ).obj
        ((CondensedRing.upperStar Λ (frobeniusPointIso D).hom).obj M) :=
  ModuleCat.homMk (directFrobeniusTermwiseSections D Λ M)
    (directFrobeniusTermwiseSections_linear D Λ M)

/-- Naturality of the explicit linear termwise map; in particular this is its differential
square when `f` is a complex differential.
Source: Steps 2 and 3 of the node;
(blueprint: def-weil-frobenius-point-transport).

Proof: apply sheaf naturality to restriction along `r`, then naturality in the sheaf of
the normalized inverse-image identification, then naturality of `Mod.extendUnitHom`.
Compose these three squares and use faithfulness of the underlying additive group
functor to obtain the module equation. -/
theorem directFrobeniusTermwiseModuleMap_naturality (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (M N : directFrobeniusModule D Λ) (f : M ⟶ N) :
    (directFrobeniusSections D Λ).map f ≫ directFrobeniusTermwiseModuleMap D Λ N =
      directFrobeniusTermwiseModuleMap D Λ M ≫
        (directFrobeniusSections D Λ).map
          ((CondensedRing.upperStar Λ (frobeniusPointIso D).hom).map f) := by
  apply (forget₂ (ModuleCat (condensedScalarRing Λ)) Ab).map_injective
  exact termwiseSections_naturality D Λ M N f

/-- The normalized inverse-image equation at every site object.  It is the
unit/comma formula from `existsUnique_proEtaleIsoInverseImageIdentification`; at
`U=t`, its comma object is `V=t_g` with `φ=(id,id)`, and sheafification is the
canonical map of `proEtaleSheafInverseImage`.

Source: Stacks Tags 09A5 and 00WX;
(blueprint: def-weil-frobenius-point-transport).

Proof: unfold the named normalized inverse-image identification, which is chosen from
`existsUnique_proEtaleIsoInverseImageIdentification`, and apply its normalization
property at F and U. The comma-arrow description specializes at U=t to the stated
finite insertion, and its inverse-image target already includes sheafification. -/
theorem directFrobeniusInverseImage_normalization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (F : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (U : X.ProEt) :
    ((Scheme.proEtaleIsoInverseImageIdentification f Ab.{u + 1}).inv.app F).app (op U) =
      ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).unit.app F).hom.app
          (op ((Scheme.proEtaleIsoPostcompose f).obj U)) ≫
        ((Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).obj F).obj.map
          (Scheme.proEtaleIsoCommaArrow f U).op := by
  exact (Scheme.existsUnique_proEtaleIsoInverseImageIdentification f Ab.{u + 1}).exists.choose_spec
    F U

/-- The direct condensed point transport has the restriction, insertion, tensor-unit,
complex-localization, bounded-constructibility, and natural-isomorphism properties
specified in `def-weil-frobenius-point-transport`.

Source: (blueprint: def-weil-frobenius-point-transport), clauses after the
termwise formula.  Proof plan, clause by clause:
1. Restrict a module along `r : t_g ⟶ t` and apply the normalized inverse-image
   identification, giving `σ_M=e_M⁻¹∘M(r)`.
2. Apply the native `Mod.extendUnitHom` to obtain the A-linear insertion
   `j_M(x)=1⊗x`.
3. Compose these maps in each degree to obtain `i_C=Γ(j_C)∘σ_C`.
4. Verify the differential square and pass to the derived localization through
   the explicit fibre/sections comparison.
5. In the inverse-image colimit model use `V=t_g` and `φ=(id,id)`, then the
   sheafification map of `proEtaleSheafInverseImage`; this gives the finite
   coefficient normalization at every `n≥1`.
6. Apply the point-fibre equivalence for constructibility and the native
   upper-star equivalence for componentwise `IsIso` and naturality. -/
theorem directFrobeniusPointTransport_spec (D : FiniteFieldDatum.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ K : AlgebraicGeometry.ProEtale.CondensedGeometricPoint.Complexes Λ D.k,
      constantModelBoundedConstructible Λ (Spec (.of D.k)) K →
        constantModelBoundedConstructible Λ (Spec (.of D.k))
          ((directFrobeniusPullback D ℓ _hℓ E n _hn Λ).obj K)) := by
  intro K hK
  have := (constantModelConstructibleFiniteTor_wellDefined Λ (Spec (.of D.k))).2.1
  let e := Functor.mapDerivedCategoryNatIso
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (frobeniusPointIso D).hom) ≪≫
      Functor.mapDerivedCategoryIdIso _
  exact (constantModelBoundedConstructible Λ (Spec (.of D.k))).prop_of_iso
    (e.app K).symm hK

end WeilConjectures
