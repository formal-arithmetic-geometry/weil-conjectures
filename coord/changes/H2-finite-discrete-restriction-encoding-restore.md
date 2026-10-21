# AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_restrictionEncoding

## Reason

Restore the concrete implementation quarantined after the cluster restore recorded
in coord/rework.tsv on 2026-10-20. The live item file is absent. Its archive is
preserved at quarantine/Sheaf/Paper/FiniteDiscreteRestrictionEncoding.lean.
A plain compile of the archive succeeds in 11.2 seconds, but the delivery probe
and a standalone compile expose a generated-name collision: the naturality proofs
contain an unknown constant instEssentiallySmallProfinite_sheaf_2. Naming the
local smallness instance explicitly and making it private removes that collision.
A standalone compile of this repair succeeds in 9.4 seconds; printing the public
theorem's axioms gives only propext, Classical.choice and Quot.sound.
The repair restores the actual sectionwise comparison, its naturality, and the
inverse-image isomorphism. It does not withdraw the node or replace it with an
empty module. There are zero holes in this implementation.

## Old

The live file lean/Sheaf/Paper/FiniteDiscreteRestrictionEncoding.lean is absent.
The archived local instance is:

```lean
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
```

All remaining archived implementation text is preserved exactly under New below.

## New

Restore the archived module, preserving every theorem and construction, its
signature and body, public imports, and docstrings. Give the first local instance
the explicit private name restrictionEncodingEssentiallySmall. Its type and value
are unchanged; its registration remains local. No new public declaration or global
instance is introduced. This avoids the anonymous-instance name collision.

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2 -/
module

public import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import Sheaf.Paper.FiniteDiscreteCoefficientSections

/-! # Restriction compatibility of the fixed coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

private local instance restrictionEncodingEssentiallySmall :
    EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

local instance (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := AlgebraicGeometry.Scheme.ProEt.topology T)
    (A := Ab.{u + 1})

local instance (T : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint

noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

local notation "ΛB" => Profinite.continuousMapRingObj B

private noncomputable def coefficientUnit (T : Scheme.{u}) :
    A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B) ⟶
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T).obj :=
  (sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ≫
    (finiteDiscreteSchemeRingIso B T eR).hom.hom

private lemma encoding_action (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T) (V : T.ProEtᵒᵖ) :
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology T)
          (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M))).obj V).X =
    (coefficientUnit B eR T).app V ▷ M.X.obj.obj V ≫
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
        M.X).hom.app V := by
  dsimp only [presheafToFunctor, moduleLocalizationRight, Adjunction.modRight,
    Functor.comp_obj]
  simp only [Functor.act_mapMod_obj, Mod.act_comap_obj]
  dsimp only [CategoryTheory.evaluation_obj_map, CategoryTheory.evaluation_obj_obj]
  change (((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ▷ M.X.obj ≫
    Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
      ((presheafToSheaf (ProEt.topology T) Ab.{u + 1}).obj
        (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))) M.X ≫
    (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      ((finiteDiscreteSchemeRingIso B T eR).hom ▷ M.X) ≫
    (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
        M.X)).app V) = _
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [NatTrans.comp_app, Monoidal.whiskerRight_app,
    coefficientUnit, Category.assoc, comp_whiskerRight]
  rfl

omit [IsMonHom eR.hom] in
private lemma coefficientUnit_pushforward (T U : Scheme.{u}) (j : U ⟶ T)
    (V : T.ProEtᵒᵖ) :
    (coefficientUnit B eR T).app V ≫
      (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app V =
    (coefficientUnit B eR U).app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  exact finiteDiscreteCoefficient_coefficientUnit_pushforward B eR T U j V

private lemma pushforward_tensor (T U : Scheme.{u}) (j : U ⟶ T)
    (P Q : Sheaf (ProEt.topology U) Ab.{u + 1}) (V : T.ProEtᵒᵖ) :
    (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
      (((j)_*[Ab.{u + 1}]).obj P) (((j)_*[Ab.{u + 1}]).obj Q)).app V ≫
      (Functor.LaxMonoidal.μ ((j)_*[Ab.{u + 1}]) P Q).hom.app V =
    (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U) Ab.{u + 1}) P Q).app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  exact @Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    T.ProEt _ U.ProEt _ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j)
    Ab.{u + 1} _ _ _ (ProEt.topology T) (ProEt.topology U)
    (GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})) _
    (Scheme.ProEt.isContinuous_overPullback j)
    (GrothendieckTopology.W.monoidal (J := ProEt.topology U) (A := Ab.{u + 1})) _ P Q V

private lemma push_action (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B U) (V : T.ProEtᵒᵖ) :
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology T)
          (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj
            ((lowerStar (Profinite.continuousMapRingObj.{u} B) j).obj M)))).obj V).X =
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := U.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology U)
          (A (C := U.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B U eR).hom).obj M))).obj
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)).X := by
  rw [encoding_action B eR T
    ((lowerStar (Profinite.continuousMapRingObj.{u} B) j).obj M) V,
    encoding_action B eR U M
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)]
  let F := (j)_*[Ab.{u + 1}]
  let I := sheafToPresheaf (ProEt.topology T) Ab.{u + 1}
  change (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
    (Functor.LaxMonoidal.μ I (condensedRingObj ΛB T) (F.obj M.X)).app V ≫
    (condensedPushforwardHom ΛB j ▷ F.obj M.X ≫
      Functor.LaxMonoidal.μ F (condensedRingObj ΛB U) M.X ≫
      F.map (Mod.act (A := condensedRingObj ΛB U) M.X)).hom.app V = _
  change (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
    (Functor.LaxMonoidal.μ I (condensedRingObj ΛB T) (F.obj M.X) ≫
      I.map (condensedPushforwardHom ΛB j ▷ F.obj M.X) ≫
      I.map (Functor.LaxMonoidal.μ F (condensedRingObj ΛB U) M.X) ≫
      I.map (F.map (Mod.act (A := condensedRingObj ΛB U) M.X))).app V = _
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [NatTrans.comp_app]
  change (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
    (condensedPushforwardHom ΛB j).hom.app V ▷ (F.obj M.X).obj.obj V ≫
    (Functor.LaxMonoidal.μ I (F.obj (condensedRingObj ΛB U)) (F.obj M.X)).app V ≫
    (Functor.LaxMonoidal.μ F (condensedRingObj ΛB U) M.X).hom.app V ≫
    (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) = _
  have hμ' := pushforward_tensor T U j (condensedRingObj ΛB U) M.X V
  calc
    _ = (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
        (condensedPushforwardHom ΛB j).hom.app V ▷ (F.obj M.X).obj.obj V ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U) Ab.{u + 1})
          (condensedRingObj ΛB U) M.X).app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) ≫
        (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
          (condensedPushforwardHom ΛB j).hom.app V ▷ (F.obj M.X).obj.obj V ≫ k ≫
          (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)) hμ'
    _ = _ := by
      have hs := coefficientUnit_pushforward B eR T U j V
      have h := congrArg (fun k ↦ k ▷ (F.obj M.X).obj.obj V ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U) Ab.{u + 1})
          (condensedRingObj ΛB U) M.X).app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) ≫
        (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)) hs
      simp only [comp_whiskerRight, Category.assoc] at h
      convert h using 1; rfl

private noncomputable def encodingPushforwardIso (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B U) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj
      ((lowerStar (Profinite.continuousMapRingObj.{u} B) j).obj M) ≅
    ((j)_*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.obj M) := by
  unfold finiteDiscreteCoefficientEquivalence
  apply (fullyFaithfulSheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} B))).preimageIso
  refine NatIso.ofComponents (fun V ↦ ?_) (fun f ↦ ?_)
  · refine G.mapIso (Mod.isoMk (Iso.refl _) ?_)
    simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
    exact push_action B eR T U j M V
  · change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
    rw [← G.map_comp, ← G.map_comp]
    congr 1

private noncomputable def encodingPushforwardNatIso (T U : Scheme.{u}) (j : U ⟶ T) :
    lowerStar (Profinite.continuousMapRingObj.{u} B) j ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse ≅
      (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse ⋙
        (j)_*[ModuleCat.{u + 1} (ULift.{u + 1} B)] := by
  refine NatIso.ofComponents (encodingPushforwardIso B eR G hG T U j) ?_
  intro M N f
  apply (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} B))).map_injective
  apply NatTrans.ext
  funext V
  simp only [Functor.map_comp, NatTrans.comp_app, encodingPushforwardIso]
  unfold finiteDiscreteCoefficientEquivalence
  change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
  rw [← G.map_comp, ← G.map_comp]
  congr 1

private noncomputable def encodingPullbackNatIso (T U : Scheme.{u}) (j : U ⟶ T) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse ⋙
      (j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)] ≅
    upperStar (Profinite.continuousMapRingObj.{u} B) j ⋙
      (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse := by
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let EU := finiteDiscreteCoefficientEquivalence B eR G hG U
  let i := encodingPushforwardNatIso B eR G hG T U j
  let k := Iso.isoCompInverse (H := ET.symm) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU.symm) k
  let a := ET.symm.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} B)) j)
  let b := (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj.{u} B) j).comp
    EU.symm.toAdjunction
  exact a.leftAdjointUniq (b.ofNatIsoRight kr)

/-- The common coefficient encoding commutes with inverse image along a scheme morphism.
Source: Bhatt--Scholze, Proposition 5.3.2; the sectionwise encoding of internal
modules and the coefficient identification pulled back from one fixed point.
(blueprint: lem-weil-pbc-finite-discrete-restriction-encoding)

Proof in words. Write the encoding as restriction of scalars along the fixed
constant-ring identification, followed by sectionwise encoding. At the presheaf
level, sectionwise encoding commutes with direct image, which is precomposition;
restriction of scalars commutes with that same precomposition. The coefficient
maps commute because all are obtained by pulling back eR from the profinite point.
Restrict this direct-image isomorphism to sheaves. Conjugating by the two encoding
equivalences and using uniqueness of left adjoints gives the inverse-image
isomorphism. The internal inverse image is mapMod followed by extension of
scalars along condensedPullbackHom. This ring map is invertible, so extension
of scalars is canonically restriction along its inverse. Evaluate the resulting
natural isomorphism at M. This uses no finiteness, nonempty-space, or nonzero-ring
assumption. -/
theorem finiteDiscreteCoefficient_restrictionEncoding
    (T U : Scheme.{u}) (j : U ⟶ T) (M : FiniteDiscreteInternalModules B T) :
    Nonempty (
      ((j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M) ≅
      (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.obj
        ((Mod.comap (inv (condensedPullbackHom
          (Profinite.continuousMapRingObj.{u} B) j))).obj
          ((((j)^*[Ab.{u + 1}]).mapMod
            (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M))) := by
  refine ⟨(encodingPullbackNatIso B eR G hG T U j).app M ≪≫ ?_⟩
  exact (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.mapIso
    ((Mod.extendScalarsIsoComapInv
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j)).app
      ((((j)^*[Ab.{u + 1}]).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M))

end AlgebraicGeometry.ProEtale.CondensedRing
```

## Users

The live downstream.py query cannot enumerate consumers of the missing module.
An import-graph scan of lean/ and quarantine/, with live source taking precedence,
finds 4 direct consumers and 152 total transitive consumers.
All are listed below. No consumer is edited or taken from another group; therefore
its holder is not queried. Each recovers the archived theorem and helper interface and
proofs, including the private helpers used by the existing proof-only import all
in FiniteDiscreteCoefficientRestriction. No target statement or definition changes
meaning and no target-statement review is reopened. The DAG attachment, dependencies,
proof steps and unit route remain valid and are preserved unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.AdmissibleVerdierExchange | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.CurveIntermediateExtension | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | not queried; not adapted | Direct consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | not queried; not adapted | Direct consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | not queried; not adapted | Direct consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeCompactComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeCompactScalar | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteFreeScalarProjection | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteTorStability | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.GlobalVerdierDuality | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.IntegralDirectImageTower | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.IntegralExchangeReduction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.MateOpenRestriction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.NonrationalCompositionSeed | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ProjectionFiniteReduction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ProperProductCounitTranspose | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalExceptionalRestriction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalHomScalarTranspose | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalRestrictionGlue | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalTensorSymmetry | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.RestrictionLocal | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.ScalarExchangeConstituents | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.SfBidualityClass | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.SitePerfectRationalBidual | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.TateTwistSupportCondition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.TensorAdjunctionExchange | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Paper.VerdierExchange | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not queried; not adapted | Direct consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteDualizing | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteExceptional | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralDualizing | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.IntegralVerdier | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.RationalOperations | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctors.RationalVerdier | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Targets.AffineSpaceRationalLine | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Targets.PoincareUncurry | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.Targets.SmoothPurityQbar | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.PoincareDuality.Poincare | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.PoincareDuality.Verdier | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.SmoothPurity.Defs | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Basic | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.Main | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried; not adapted | Transitive consumer in lean; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.TraceFormula.Statement | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; not adapted | Transitive consumer in quarantine; Archived theorem and helper interface restored; smallness instance explicitly named and private. |

## Status

landed 20261021T022436-L-2847130 2026-10-21 (merge of deliver/H2/Sheaf.Paper.FiniteDiscreteRestrictionEncoding)
