/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! # Local finite freeness of continuous coefficients in the scheme universe

Source: Stacks Project, Tags 03DM and 03DO; Bhatt--Scholze, Section 6.8.
(blueprint: lem-zl-continuous-universe-local-freeness)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.ProEtale.CondensedRing
@[irreducible] private noncomputable def universeFunctionPushforward {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousCoefficientRingSheaf X O) ⟶
    (ProEtale.lowerStar Ab.{u + 1} f).obj
      ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousCoefficientRingSheaf Y O)) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up
            (s.down.comp (pullback.fst U.unop.hom f).base.hom)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro U V g
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       change (s.down.comp g.unop.left.base.hom).comp
         (pullback.fst V.unop.hom f).base.hom =
           (s.down.comp (pullback.fst U.unop.hom f).base.hom).comp
             ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left.base.hom
       have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
           pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ g.unop.left := by
         exact pullback.lift_fst _ _ _
       ext x
       exact congrArg (fun h : pullback V.unop.hom f ⟶ U.unop.left ↦ s.down (h x)) h.symm }⟩

/-- Sections of continuous direct image are precomposed with the pullback projection.
Source: the defining section formula for universeFunctionPushforward.
(blueprint: def-weil-pbc-integral-matrix-analytic-data) -/
private theorem universeFunctionPushforward_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (U : X.ProEt) (s : ULift.{u + 1} C(U.left, O)) :
    ((universeFunctionPushforward f O).hom.app (op U)) s =
      ULift.up (s.down.comp (pullback.fst U.hom f).base.hom) := by
  unfold universeFunctionPushforward
  rfl

private theorem universeChart_scheme_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    condensedPushforwardHom (Profinite.continuousCoefficientRingObj O) f ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (ContinuousRingUniverse.comparison Y O) =
    ContinuousRingUniverse.comparison X O ≫ universeFunctionPushforward f O := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let CY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf Y O)
  have hleft := chartMate_homEquiv f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)
    (pointUpperStar.obj (Profinite.continuousCoefficientRingObj O)) CY
    (ContinuousRingUniverse.comparison Y O)
  rw [← condensedPullbackHom_eq (Profinite.continuousCoefficientRingObj O) f] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  have hchart : adjX.homEquiv _ _ (ContinuousRingUniverse.comparison X O) =
      ContinuousRingUniverse.comparisonAdjoint X O := by
    rw [ContinuousRingUniverse.comparison]
    exact Equiv.apply_symm_apply _ _
  erw [hchart]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [← unitAlgHom_comp_map_condensedPullbackHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  have hchartY :
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).homEquiv _ _
          (ContinuousRingUniverse.comparison Y O) =
            ContinuousRingUniverse.comparisonAdjoint Y O := by
    rw [ContinuousRingUniverse.comparison]
    exact Equiv.apply_symm_apply _ _
  simp only [Adjunction.comp_homEquiv] at hchartY
  erw [hchartY]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor Ab.{u + 1} (comp_toSpecZ f)).inv.app CY).hom.app
    (op (profiniteToProEt.obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection Y S.unop)))).down =
    (((universeFunctionPushforward f O).hom.app
      (op ((profiniteToProEtOf X).obj S.unop)))
        (ULift.up (s.down.comp (profiniteTestProjection X S.unop)))).down
  rw [lowerStarFactor_inv_app_hom_app, universeFunctionPushforward_app]
  change (s.down.comp (profiniteTestProjection Y S.unop)).comp
      (((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection X S.unop)).comp
      (pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) =
      pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ X) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

private lemma universeChart_pullback (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f]
    (E : Type u) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] :
    (ProEtale.upperStar Ab.{u + 1} f).map (ContinuousRingUniverse.comparison X E) ≫
      (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).hom.app
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X E)) =
      condensedPullbackHom (Profinite.continuousCoefficientRingObj E) f ≫
        ContinuousRingUniverse.comparison Y E := by
  let adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  apply (adj.homEquiv _ _).injective
  have hl := adj.homEquiv_naturality_left (ContinuousRingUniverse.comparison X E)
    ((upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).hom.app
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X E)))
  erw [hl]
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app adj
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f inferInstance)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X E))
  erw [hu]
  erw [adj.homEquiv_naturality_right]
  change ContinuousRingUniverse.comparison X E ≫ _ =
    (adj.unit.app _ ≫ (ProEtale.lowerStar Ab.{u + 1} f).map
      (condensedPullbackHom (Profinite.continuousCoefficientRingObj E) f)) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map (ContinuousRingUniverse.comparison Y E)
  rw [← Adjunction.unitAlgHom, unitAlgHom_comp_map_condensedPullbackHom]
  rw [CondensedRing.universeChart_scheme_naturality]
  congr 1
  ext U : 3
  apply ConcreteCategory.hom_ext
  intro s
  erw [CondensedRing.universeFunctionPushforward_app f E U.unop s]
  rfl

private noncomputable def universeRingRegularIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    (continuousRingModuleEquivalenceUniverse X T).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) ≅
      SheafOfModules.unit (continuousCoefficientRingSheaf X T) := by
  letI := ContinuousRingUniverse.comparison_isIso X T
  let J := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let F := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A
  let G := ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm
  exact G.functor.mapIso (F.functor.mapIso
    (Mod.regularIsoOfIsIso (ContinuousRingUniverse.comparison X T)) ≪≫
      sectionModuleRegularIso X A) ≪≫
      ringModuleUnitIso X (reconstructedRingIso X R).symm

/-- The continuous module encoding identifies finite biproducts with finite free sheaves.
Map the biproduct through the equivalence, use universeRingRegularIso and
reindex the corresponding coproduct along Equiv.ulift.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(blueprint: def-weil-pbc-continuous-coefficient-module-encoding) -/
private noncomputable def universeRingFreeIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (n : ℕ) :
    (continuousRingModuleEquivalenceUniverse X T).functor.obj
        (⨁ fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) ≅
      SheafOfModules.free (R := continuousCoefficientRingSheaf X T) (ULift.{u + 1} (Fin n)) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let F := (continuousRingModuleEquivalenceUniverse X T).functor
  letI : PreservesBiproduct (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) F :=
    preservesBiproduct_of_preservesCoproduct F
  exact F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ universeRingRegularIso X T) ≪≫
    biproduct.isoCoproduct _ ≪≫
      (Sigma.reindex Equiv.ulift (fun _ : Fin n ↦
        SheafOfModules.unit (continuousCoefficientRingSheaf X T))).symm

private noncomputable def universeRestrictionMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    (continuousCoefficientRingSheaf Y T).obj ⟶
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op ⋙
        (continuousCoefficientRingSheaf X T).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }

/-- Encoding canonical inverse image agrees with restriction of the sectionwise module.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tags 03EK and 03EL.
(blueprint: lem-weil-pbc-continuous-module-encoding-restriction)

Proof. Apply the monoidal localization comparison to the underlying module.
Conjugate its coefficient map by the two continuous charts. The chart-pullback
square identifies the result with the identity continuous-function coefficient
map. Evaluating the actions on pure tensors gives the sectionwise linearity.
Naturality is the localization comparison's naturality. -/
private theorem universeRing_module_restriction
    (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) :
    Nonempty (((continuousRingModuleEquivalenceUniverse Y T).functor.obj
        ((upperStar (Profinite.continuousCoefficientRingObj T) f).obj P)).val ≅
      (PresheafOfModules.pushforward (universeRestrictionMap f T)).obj
        ((continuousRingModuleEquivalenceUniverse X T).functor.obj P).val) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
    Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let τ := ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance
  let cX := ContinuousRingUniverse.comparison X T
  let cY := ContinuousRingUniverse.comparison Y T
  let : IsIso cX := ContinuousRingUniverse.comparison_isIso X T
  let : IsIso cY := ContinuousRingUniverse.comparison_isIso Y T
  let : NatTrans.IsMonoidal τ.hom := inferInstance
  let φ := condensedPullbackHom (Profinite.continuousCoefficientRingObj T) f
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X T)
  let C := condensedRingObj (Profinite.continuousCoefficientRingObj T) X
  let : MonObj C := inferInstanceAs
    (MonObj (condensedRingObj (Profinite.continuousCoefficientRingObj T) X))
  have hs : G.map cX ≫ τ.hom.app A = φ ≫ cY := universeChart_pullback X Y f T
  have hc : (inv cY ≫ inv φ) ≫ τ.hom.app C = L.map (inv cX) := by
    apply (cancel_epi (φ ≫ cY)).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    calc
      τ.hom.app C = G.map cX ≫ τ.hom.app A ≫ L.map (inv cX) := by
        rw [← τ.hom.naturality]
        simp
        rfl
      _ = φ ≫ cY ≫ L.map (inv cX) := by rw [← Category.assoc, hs, Category.assoc]
  let : IsMonHom (τ.hom.app C) := NatTrans.isMonHom_app τ.hom C
  let Q := (G.mapMod C).obj P
  let ψ := inv cY ≫ inv φ
  let e := (Functor.mapModNatIso τ C).app P
  let Q' := (Mod.comap ψ).obj Q
  let Q'' := (Mod.comap ψ).obj ((Mod.comap (τ.hom.app C)).obj ((L.mapMod C).obj P))
  let R := continuousCoefficientRingSheaf Y T
  let AY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : IsCommMonObj AY := Sheaf.isCommMonObj_sheafCompose_obj _ R
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let H := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology Y) AY).functor ⋙
      (ringModuleEquivalenceOfIso Y (reconstructedRingIso Y R).symm).functor
  let e₀ := ((Mod.comap (inv cY)).mapIso ((Mod.extendScalarsIsoComapInv φ).app Q)) ≪≫
    ((Mod.comapComp (inv cY) (inv φ)).app Q).symm ≪≫
      (Mod.comap ψ).mapIso e
  refine ⟨((SheafOfModules.forget _).mapIso (H.mapIso e₀)) ≪≫ ?_⟩
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    let Z' := (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale f)).op.obj Z
    have ha :
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          AY (L.obj P.X)).app Z ≫
          (ψ ▷ _ ≫ (τ.hom.app C) ▷ _ ≫
            Functor.LaxMonoidal.μ L C P.X ≫ L.map (Mod.act P.X)).hom.app Z =
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          A P.X).app Z' ≫ ((inv cX) ▷ P.X ≫ Mod.act P.X).hom.app Z' := by
      have hh : ψ ▷ L.obj P.X ≫ (τ.hom.app C) ▷ L.obj P.X =
          (L.map (inv cX)) ▷ L.obj P.X := by
        rw [← comp_whiskerRight]
        exact congrArg (fun a ↦ a ▷ L.obj P.X) hc
      rw [← Category.assoc (ψ ▷ _) ((τ.hom.app C) ▷ _) _, hh]
      erw [Functor.LaxMonoidal.μ_natural_left_assoc L (inv cX) P.X,
        ← Functor.map_comp]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      rw [← Category.assoc]
      erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) A P.X Z]
      rfl
    exact ConcreteCategory.congr_hom ha.symm (r ⊗ₜ[ℤ] m)
  · intro Z W a
    ext m
    rfl

private theorem universeRing_slice_free_iff
    (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X))
    (W : X.ProEt) :
    (∃ n : ℕ, Nonempty (((continuousRingModuleEquivalenceUniverse X T).functor.obj P).over W ≅
      SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X))
      (((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod _).obj P) := by
  let R := continuousCoefficientRingSheaf X T
  let S := continuousCoefficientRingSheaf W.left T
  let e := Scheme.ProEt.sliceEquiv X W
  let : e.inverse.IsDenseSubsite (Scheme.ProEt.topology W.left)
      ((Scheme.ProEt.topology X).over W) := Scheme.ProEt.sliceDense X W
  let c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology W.left) ((Scheme.ProEt.topology X).over W)).obj (R.over W) :=
    Iso.refl _
  obtain ⟨q, hq⟩ := Scheme.ProEt.module_transport
    ((Scheme.ProEt.topology X).over W) (Scheme.ProEt.topology W.left)
    e (R.over W) S c
  have hforget (N : SheafOfModules.{u + 1} (R.over W)) :
      (q.functor.obj N).val = (PresheafOfModules.pushforward c.hom.hom).obj N.val :=
    congrArg (fun F ↦ F.obj N) hq
  let η : SheafOfModules.unit S ≅ q.functor.obj (SheafOfModules.unit (R.over W)) := by
    apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    change (SheafOfModules.unit S).val ≅
      (q.functor.obj (SheafOfModules.unit (R.over W))).val
    rw [hforget]
    refine PresheafOfModules.isoMk (fun Z ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro r
      ext m
      rfl
    · intro Z Z' a
      ext
      rfl
  let M := (continuousRingModuleEquivalenceUniverse X T).functor.obj P
  let Q := (upperStar (X := W.left) (Y := X)
    (Profinite.continuousCoefficientRingObj T) W.hom).obj P
  let F := continuousRingModuleEquivalenceUniverse W.left T
  obtain ⟨er⟩ := universeRing_module_restriction X W.left W.hom T P
  let es : (q.functor.obj (M.over W)).val ≅
      (PresheafOfModules.pushforward (universeRestrictionMap W.hom T)).obj M.val := by
    rw [hforget]
    refine PresheafOfModules.isoMk (fun Z ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro r
      ext m
      rfl
    · intro Z Z' a
      ext m
      rfl
  let em : q.functor.obj (M.over W) ≅ F.functor.obj Q :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso (es ≪≫ er.symm)
  have he :
      (∃ n : ℕ, Nonempty (M.over W ≅ SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
      Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj T) W.left) Q := by
    constructor
    · rintro ⟨n, ⟨en⟩⟩
      refine ⟨n, ⟨F.fullyFaithfulFunctor.preimageIso ?_⟩⟩
      exact em.symm ≪≫ q.functor.mapIso en ≪≫
        (SheafOfModules.mapFreeIso q.functor _ η).symm ≪≫
          (universeRingFreeIso W.left T n).symm
    · rintro ⟨n, ⟨en⟩⟩
      refine ⟨n, ⟨q.fullyFaithfulFunctor.preimageIso ?_⟩⟩
      exact em ≪≫ F.functor.mapIso en ≪≫ universeRingFreeIso W.left T n ≪≫
        SheafOfModules.mapFreeIso q.functor _ η
  rw [he]
  let φ := condensedPullbackHom (X := W.left) (Y := X)
    (Profinite.continuousCoefficientRingObj T) W.hom
  let Qraw := ((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod _).obj P
  let ec := (Mod.extendScalarsIsoComapInv φ).app Qraw
  let E := Mod.comapEquivalenceOfIsIso (inv φ)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  let ef (n : ℕ) : E.functor.obj (Mod.finiteFree _ n) ≅ Mod.finiteFree _ n :=
    E.functor.mapBiproduct (fun _ : Fin n ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.regularIsoOfIsIso φ)
  constructor
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨E.fullyFaithfulFunctor.preimageIso (ec.symm ≪≫ en ≪≫ (ef n).symm)⟩⟩
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨ec ≪≫ E.functor.mapIso en ≪≫ ef n⟩⟩

private theorem universeRing_locallyFree_iff
    (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousCoefficientRingObj T) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P)) ↔
      ((continuousRingModuleEquivalenceUniverse X T).functor.obj P).IsFiniteLocallyFree := by
  classical
  let R := continuousCoefficientRingSheaf X T
  let M := (continuousRingModuleEquivalenceUniverse X T).functor.obj P
  constructor
  · rintro ⟨C, hC⟩
    let (s : C.I₀) : WeaklyEtale (C.f s) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
    let U (s : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f s)
    have hU : (Scheme.ProEt.topology X).CoversTop U := by
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _
        (Scheme.ProEt.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X)]
      let a (s : C.I₀) : U s ⟶ Scheme.ProEt.mk (𝟙 X) :=
        MorphismProperty.Over.homMk (C.f s) (by
          change C.f s ≫ 𝟙 X = C.f s
          exact Category.comp_id _)
      apply Scheme.ProEt.mem_topology_iff.mpr
      refine ⟨Presieve.ofArrows U a, ?_, ?_⟩
      · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
        exact C.mem₀
      · intro W f hf
        obtain ⟨s⟩ := hf
        exact ⟨s, ⟨𝟙 _⟩⟩
    have hfree (s : C.I₀) : ∃ n : ℕ, Nonempty (M.over (U s) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) :=
      (universeRing_slice_free_iff X T P (U s)).mpr (hC s)
    choose n hn using hfree
    have hU' : (Scheme.ProEt.topology X).CoversTop
        (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) := by
      intro V
      apply (Scheme.ProEt.topology X).superset_covering _ (hU V)
      rintro W f ⟨s, ⟨a⟩⟩
      exact ⟨ULift.up s, ⟨a⟩⟩
    exact SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free (M := M)
      (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) hU'
      (fun s ↦ ULift.{u + 1} (Fin (n s.down))) (fun s ↦ hn s.down)
  · intro hM
    let : M.IsFiniteLocallyFree := hM
    obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
    let : q.IsLocallyFreeData := hq
    have hfree (i : q.I) : ∃ n : ℕ, Nonempty (M.over (q.X i) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let : (q.generators i).IsFiniteType := hf.isFiniteType i
      obtain ⟨n, ⟨en⟩⟩ := Finite.exists_equiv_fin (q.generators i).I
      exact ⟨n, ⟨(asIso (q.generators i).π).symm ≪≫
        SheafOfModules.freeFunctor.mapIso (en.trans Equiv.ulift.symm).toIso⟩⟩
    let V : X.ProEt := Scheme.ProEt.mk (𝟙 X)
    obtain ⟨S, hS, hle⟩ := Scheme.ProEt.mem_topology_iff.mp (q.coversTop V)
    obtain ⟨C, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hS
    have hw (i : C.I₀) : (C.f i).left = (C.X i).hom := by
      have h := MorphismProperty.Over.w (C.f i)
      change (C.f i).left ≫ 𝟙 X = (C.X i).hom at h
      exact (Category.comp_id _).symm.trans h
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
      { I₀ := C.I₀
        X := fun i ↦ (C.X i).left
        f := fun i ↦ (C.X i).hom
        mem₀ := by
          have hm := Scheme.ProEt.mem_precoverage_iff.mp C.mem₀
          rw [Presieve.map_ofArrows] at hm
          change (Presieve.ofArrows (fun i ↦ (C.X i).left)
            (fun i ↦ (C.f i).left)) ∈ Scheme.proetalePrecoverage X at hm
          simpa only [hw] using hm }
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage (@WeaklyEtale)))
    let D' := D.restrictIndexOfSmall.{u}
    refine ⟨D', fun s ↦ ?_⟩
    let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} D s
    obtain ⟨i, ⟨a⟩⟩ := hle _ _ (.mk j)
    obtain ⟨n, ⟨en⟩⟩ := hfree i
    have en' : Nonempty (M.over (C.X j) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let F := SheafOfModules.overMap R a
      let e : F.obj (SheafOfModules.unit (R.over (q.X i))) ≅
          SheafOfModules.unit (R.over (C.X j)) := SheafOfModules.overMapUnitIso a
      exact ⟨((SheafOfModules.overFunctorMap R a).app M).symm ≪≫ F.mapIso en ≪≫
        (SheafOfModules.mapFreeIso F _ e.symm).symm⟩
    exact (universeRing_slice_free_iff X T P (C.X j)).mp ⟨n, en'⟩

/-- The section-action equivalence detects exactly the finite pro-etale free charts.
Source: Stacks Project, Tags 03DM and 03DO; Bhatt--Scholze, Section 6.8.
(blueprint: lem-zl-continuous-universe-local-freeness)

Proof. The canonical continuous coefficient chart commutes with weakly etale
restriction. On each slice the section-action equivalence takes the internal
regular module and its finite biproducts to the usual finite free module sheaves.
Thus a pro-etale free cover gives local finite freeness. Conversely evaluate a
finite locally free covering at the terminal pro-etale object, refine its sieve
by a pro-etale precover, and restrict its finite bases. The canonical coefficient
pullback is invertible, so normalized and raw free charts agree. Empty schemes,
rank zero, and ranks varying with the covering chart are included. -/
theorem continuousUniverse_lisse_iff (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) :
    IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj T) P ↔
      ((continuousRingModuleEquivalenceUniverse X T).functor.obj P).IsFiniteLocallyFree := by
  rw [← universeRing_locallyFree_iff]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun s ↦ (freeAt_iff_standard _ (C.f s) P).mpr (hC s)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun s ↦ (freeAt_iff_standard _ (C.f s) P).mp (hC s)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
