/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Sites.LocalSite
public import WeilConjectures.Algebra.Homology.RingedSitePointFlat
public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedWeaklyContractible
public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ExactDerivedMonoidalConstruction
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
public import WeilConjectures.SixFunctors.RingedSitePoint
public import WeilConjectures.SmoothPurity.RingedSitePointTensor

/-! # Normalized exact scalar sections cup at a geometric point

Source: Stacks Project, Tags 0FPJ, 0B6C and 0FPK, sections cup and its naive
normalization (blueprint: lem-sf-exact-sections-derived-cup-map).

## Main definitions

* `pairingExactScalarPointCup`: the uniquely normalized exact scalar cup.
* `pairingExactScalarPointCup_unitIso`: its geometric-point unit identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Use the published site-size specialization, avoiding an unassigned max universe.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

private theorem point_ab_locallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralOperationsAbLocallyBijective.{u, 0} X

private theorem point_scalar_bijective :
    Function.Bijective (CohomologyTransport.scalarMap Λ (Spec (.of k))) := by
  have : PreservesFiniteLimits (upperStarFromPoint (Spec (.of k))) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have := Functor.additive_of_preserves_binary_products (upperStarFromPoint (Spec (.of k)))
  unfold CohomologyTransport.scalarMap
  let := (upperStarFromPoint (Spec (.of k))).monObjObj Λ
  let := Functor.isCommMonObj_obj (F := upperStarFromPoint (Spec (.of k))) (M := Λ)
  exact (InternalAbelianSheafModule.sectionGlobalEval_bijective.{u + 1, u + 1, u}
    (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj Λ (Spec (.of k))) _
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale _)).comp
      ((InternalAbelianSheafModule.globalMapFunctor_bijective
        (upperStarFromPoint (Spec (.of k)))
        (Functor.FullyFaithful.ofFullyFaithful _) Λ).comp
          (InternalAbelianSheafModule.sectionGlobalEquiv.{u + 1, u + 1, u}
            (coherentTopology Profinite.{u}) Λ _ terminalIsTerminal).symm.bijective)

/-- An exact cocontinuous flat-preserving strong monoidal functor has cup data
with precisely its given ordinary lax structure. Source: Stacks 07A4, 0FPQ and 0FPT.
Proof: choose flat-term functorial K-flat resolutions whose images remain K-flat.
The source and target tensor bifunctors have invertible localization comparisons on
these representatives. Their universal comparison supplies the derived monoidal
structure. Retain the monoidal factorization square, which is exactly the tensor and
unit normalization required by the cup. The ordinary summand and degree-zero unit
formulas follow from the existing complex monoidal comparison.
(blueprint: lem-pod-exact-monoidal-sections-cup) -/
private theorem exact_monoidal_sections_cup
    (G : B ⥤ ModuleCat.{r} Rcoeff) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesColimitsOfSize.{0, 0} G] [G.PreservesFlat] (m : G.Monoidal) :
    ∃ d : ExactSectionsDerivedCup G, d.ordinary = m.toLaxMonoidal := by
  letI := m
  letI : (G.mapHomologicalComplex (.up ℤ)).Monoidal := G.mapCochainComplexMonoidal
  letI : (G.mapHomologicalComplex (.up ℤ)).LaxMonoidal :=
    (G.mapCochainComplexMonoidal).toLaxMonoidal
  letI : (G.mapHomologicalComplex (.up ℤ)).OplaxMonoidal :=
    (G.mapCochainComplexMonoidal).toOplaxMonoidal
  have hμ (K L : CochainComplex B ℤ) :
      μ (G.mapHomologicalComplex (.up ℤ)) K L = (G.mapCochainComplexμIso K L).hom := by
    rfl
  have hε : ε (G.mapHomologicalComplex (.up ℤ)) = G.mapCochainComplexεIso.hom := by
    rfl
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let S : ObjectProperty (CochainComplex B ℤ) := W.kFlat ⊓
    (HomologicalComplex.quasiIso (ModuleCat.{r} Rcoeff) (.up ℤ)).kFlat.inverseImage
      (G.mapHomologicalComplex (.up ℤ))
  let Φ := property_localizer W S
  have : HasExactColimitsOfShape ℤ B := by
    have := AB5OfSize_of_univLE.{0, 0, ha, ha} B
    infer_instance
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} Rcoeff) := by
    have := AB5OfSize_of_univLE.{0, 0, r, r} (ModuleCat.{r} Rcoeff)
    infer_instance
  have (X : ModuleCat.{r} Rcoeff) :
      PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{r} Rcoeff)).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution B).some.reduced
  have hρ (P : CochainComplex B ℤ) : S (Λ.resolutionFunctor.obj P) :=
    ⟨Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P,
      G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
        ObjectProperty.flat.essImage_ι_le P⟩
  have : Φ.functor.Full := inferInstanceAs S.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs S.ι.Faithful
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLeftDerivabilityStructure :=
    Φ.isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift S Λ.resolutionFunctor hρ) Λ.resolutionNatTrans
      (fun P ↦ by
        change HomologicalComplex.quasiIso B (.up ℤ) _
        rw [HomologicalComplex.mem_quasiIso_iff]
        exact Λ.quasiIso_resolutionNatTrans_app P) rfl
  have : IsIso (ε (DerivedCategory.Q (C := B))) :=
    RingedDerivedNative.localization_isIso_ε
  have : IsIso (ε (DerivedCategory.Q (C := (ModuleCat.{r} Rcoeff)))) :=
    RingedDerivedNative.localization_isIso_ε
  have hmodels (X : DerivedCategory B) :
      ∃ P, S P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let P := DerivedCategory.Q.objPreimage X
    have : QuasiIso (Λ.resolutionNatTrans.app P) := Λ.quasiIso_resolutionNatTrans_app P
    exact ⟨Λ.resolutionFunctor.obj P, hρ P,
      ⟨asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app P)) ≪≫
        DerivedCategory.Q.objObjPreimageIso X⟩⟩
  obtain ⟨n, hn⟩ := monoidal_localization_square DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategory G.mapDerivedCategoryFactors W S
    hmodels (fun P R hR ↦ ConstantModuleDerivedProjection.tensor_localization_iso P R hR.1)
    (fun X R hR ↦ ConstantModuleDerivedProjection.tensor_localization_iso X _ hR.2)
  letI := n
  refine ⟨{
    ordinary := m.toLaxMonoidal
    derived := n.toLaxMonoidal
    chain := fun K L ↦ (G.mapCochainComplexμIso K L).hom
    chain_summand := G.ιTensorObj_mapCochainComplexμIso_hom_f
    chainUnit := G.mapCochainComplexεIso.hom
    chainUnit_zero := G.mapCochainComplexεIso_hom_f_zero
    tensor_normalization := ?_
    unit_normalization := ?_
  }, rfl⟩
  · intro K L
    simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc, hμ] using hn.tensor K L
  · simpa only [Functor.LaxMonoidal.comp_ε, Category.assoc, hε] using hn.unit

private theorem monoidal_localization_square
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (Q : B ⥤ F) (L : E ⥤ H) (G : B ⥤ E) (V : F ⥤ H)
    [Q.LaxMonoidal] [L.LaxMonoidal] [G.Monoidal]
    (e : Q ⋙ V ≅ G ⋙ L) (W : MorphismProperty B) (S : ObjectProperty B)
    [W.ContainsIdentities] [W.RespectsIso] [Q.IsLocalization W]
    [(property_localizer W S).IsLeftDerivabilityStructure]
    [IsIso (ε Q)] [IsIso (ε L)]
    (hmodels : ∀ X : F, ∃ P, S P ∧ Nonempty (Q.obj P ≅ X))
    (hQ : ∀ P R, S R → IsIso (μ Q P R))
    (hL : ∀ (X : E) R, S R → IsIso (μ L X (G.obj R))) :
    ∃ m : V.Monoidal, letI := m
      NatTrans.IsMonoidal e.hom := by
  let T := (((whiskeringLeft₂ H).obj V).obj V).obj (curriedTensor H)
  let U := (postcompose₂.obj V).obj (curriedTensor F)
  let a : (((whiskeringLeft₂ H).obj Q).obj Q).obj T ⟶
      (((whiskeringLeft₂ H).obj G).obj G).obj
        ((postcompose₂.obj L).obj (curriedTensor E)) :=
    (((whiskeringLeft₂ H).map e.hom).app (Q ⋙ V)).app (curriedTensor H) ≫
      (((whiskeringLeft₂ H).obj (G ⋙ L)).map e.hom).app (curriedTensor H) ≫
      (((whiskeringLeft₂ H).obj G).obj G).map (μNatTrans L)
  have ha P R : (a.app P).app R =
      (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) := by
    dsimp [a]
    rw [MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  let b : (((whiskeringLeft₂ H).obj Q).obj Q).obj U ⟶
      (((whiskeringLeft₂ H).obj G).obj G).obj
        ((postcompose₂.obj L).obj (curriedTensor E)) :=
    (postcompose₂.obj V).map (μNatTrans Q) ≫
      (postcompose₂.map e.hom).app (curriedTensor B) ≫
      postcompose₂MapWhiskeringLeft₂ (δNatTrans G) L
  have hb P R : (b.app P).app R =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := rfl
  have : T.IsLeftDerivedFunctor₂ a W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (property_localizer W S) a
    intro P R
    have := hL (G.obj P) R.obj R.property
    change IsIso ((a.app P).app R.obj)
    rw [ha]
    infer_instance
  have : U.IsLeftDerivedFunctor₂ b W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (property_localizer W S) b
    intro P R
    have := hQ P R.obj R.property
    change IsIso (V.map (μ Q P R.obj) ≫ e.hom.app (P ⊗ R.obj) ≫
      L.map (δ G P R.obj))
    infer_instance
  let t : U ≅ T := leftDerived₂NatIso T a W W U b (Iso.refl _)
  have ht P R : (t.hom.app (Q.obj P)).app (Q.obj R) ≫
      (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := by
    have h := leftDerived₂NatTrans_app_app T a W W U b (𝟙 _) P R
    rw [ha, hb] at h
    exact h.trans (Category.comp_id _)
  let : V.OplaxMonoidal := .ofLaxSquare t.hom (fun P ↦ e.hom.app P)
    (fun _ _ f ↦ e.hom.naturality f) ht S hmodels hL
  have (X Y : F) : IsIso (δ V X Y) :=
    inferInstanceAs (IsIso ((t.hom.app X).app Y))
  have : IsIso (η V) := by
    change IsIso (V.map (ε Q) ≫ e.hom.app _ ≫ L.map (η G) ≫ inv (ε L))
    infer_instance
  letI : V.Monoidal := .ofOplaxMonoidal V
  exact ⟨inferInstance,
    ExactMonoidalEquivalenceDerived.square_monoidal Q L G V e.hom rfl ht⟩

private theorem local_module_unit_isIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [J.IsLocalSite]
    (R : Sheaf J CommRingCat.{u + 1})
    (P : PresheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
    (U : C) (hU : IsTerminal U) :
    IsIso (((PresheafOfModules.sheafificationAdjunction (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
        P).app (Opposite.op U)) := by
  haveI := local_sheafification_unit_isIso J P.presheaf U hU
  let f := (((PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
      P).app (Opposite.op U))
  haveI : IsIso ((forget₂ (ModuleCat.{u + 1} (R.obj.obj (Opposite.op U)))
      AddCommGrpCat.{u + 1}).map f) := by
    change IsIso ((toSheafify J P.presheaf).app (Opposite.op U))
    infer_instance
  exact isIso_of_reflects_iso f (forget₂
    (ModuleCat.{u + 1} (R.obj.obj (Opposite.op U))) AddCommGrpCat.{u + 1})

private theorem local_sheafification_unit_isIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.IsLocalSite] (P : Cᵒᵖ ⥤ Ab.{u + 1}) (U : C) (hU : IsTerminal U) :
    IsIso ((toSheafify J P).app (Opposite.op U)) := by
  let p := GrothendieckTopology.IsLocalSite.point.{u} J
  let e := terminalIsoIsTerminal hU
  let unitMap := toSheafify J P
  haveI hpoint : IsIso (p.presheafFiber.map unitMap) := inferInstance
  haveI ht : IsIso (unitMap.app (Opposite.op (⊤_ C))) := by
    have hn := GrothendieckTopology.IsLocalSite.pointPresheafFiberIso_naturality.{u} J unitMap
    haveI hc : IsIso
        ((GrothendieckTopology.IsLocalSite.pointPresheafFiberIso.{u} J P).hom ≫
          unitMap.app (Opposite.op (⊤_ C))) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (GrothendieckTopology.IsLocalSite.pointPresheafFiberIso.{u} J P).hom
      (unitMap.app (Opposite.op (⊤_ C)))
  haveI he : IsIso (unitMap.app (Opposite.op U) ≫ (sheafify J P).map e.op.hom) := by
    rw [← unitMap.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (unitMap.app (Opposite.op U))
    ((sheafify J P).map e.op.hom)

private def terminalModulePoint
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [J.IsLocalSite]
    (R : Sheaf J CommRingCat.{u + 1}) (U : C) (hU : IsTerminal U)
    {A : Type (u + 1)} [CommRing A] (a : A ≃+* R.obj.obj (Opposite.op U)) :
    RingedSitePoint R (terminalPoint J U hU) where
  ring := CommRingCat.of A
  ringUnderlying := a.symm.toEquiv.toIso
  ringAdd T b c t h x := by
    change a.symm (t.hom.app _ x) = a.symm (b.hom.app _ x) + a.symm (c.hom.app _ x)
    change T.obj.obj (Opposite.op U) at x
    simpa only [_root_.id, _root_.map_add] using congrArg a.symm (h _ x)
  ringMul T b c t h x := by
    change a.symm (t.hom.app _ x) = a.symm (b.hom.app _ x) * a.symm (c.hom.app _ x)
    change T.obj.obj (Opposite.op U) at x
    simpa only [_root_.id, _root_.map_mul] using congrArg a.symm (h _ x)
  ringZero T b h x := by
    change a.symm (b.hom.app _ x) = 0
    change T.obj.obj (Opposite.op U) at x
    simpa only [_root_.id, _root_.map_zero] using congrArg a.symm (h _ x)
  ringOne T b h x := by
    change a.symm (b.hom.app _ x) = 1
    change T.obj.obj (Opposite.op U) at x
    simpa only [_root_.id, _root_.map_one] using congrArg a.symm (h _ x)
  modules := SheafOfModules.evaluation _ (Opposite.op U) ⋙ ModuleCat.restrictScalars a.toRingHom
  moduleUnderlying := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  moduleAdd M T b c t h x := h _ x
  moduleZero M T b h x := h _ x
  moduleSMul M T b c t h x := by
    change T.obj.obj (Opposite.op U) at x
    change (@id (M.val.obj (Opposite.op U)) (t.hom.app _ x)) =
      a (a.symm (b.hom.app _ x)) • (@id (M.val.obj (Opposite.op U)) (c.hom.app _ x))
    rw [a.apply_symm_apply]
    exact h _ x
  modules_additive := ⟨by intros; rfl⟩

private def terminalPoint
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.IsLocalSite] (U : C) (hU : IsTerminal U) :
    GeometricMorphism (Type (u + 1)) (Sheaf J (Type (u + 1))) where
  inverse := sheafToPresheaf J (Type (u + 1)) ⋙
    (evaluation Cᵒᵖ (Type (u + 1))).obj (Opposite.op U)
  direct := GrothendieckTopology.IsLocalSite.coconstantSheaf.{u} J (Type (u + 1))
  adj := (GrothendieckTopology.IsLocalSite.ΓCoconstantSheafAdj.{u}
    J (Type (u + 1))).ofNatIsoLeft (Sheaf.ΓNatIsoSheafSections J (Type (u + 1)) hU)
  leftExact := inferInstance

private theorem localSite_of_final
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (U : C) (hU : IsTerminal U) (h : ∀ S ∈ J U, S = ⊤) : J.IsLocalSite := by
  letI : HasTerminal C := hU.hasTerminal
  refine { eq_top_of_mem := ?_ }
  intro S hS
  let e := terminalIsoIsTerminal hU
  have hs : Sieve.pullback e.inv S = ⊤ := h _ (J.pullback_stable e.inv hS)
  apply S.id_mem_iff_eq_top.mp
  have hi : (Sieve.pullback e.inv S) (𝟙 _) := by rw [hs]; trivial
  have hi' : S e.inv := by simpa using hi
  simpa using S.downward_closed hi' e.hom

private theorem final_cover_eq_top
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Sieve (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
    (hS : S ∈ Scheme.ProEt.topology (Spec (.of k)) _) : S = ⊤ := by
  letI : Unique ↥(Scheme.ProEt.mk (𝟙 (Spec (.of k)))).left :=
    inferInstanceAs (Unique (PrimeSpectrum k))
  obtain ⟨idx, O, _, hcover, hmem⟩ :=
    Scheme.ProEt.exists_disjoint_opens_of_forall_exists_retraction
      (R := .of k) (fun T _ _ _ _ ↦ by
        have : Nontrivial (k ⊗[k] T) := Module.FaithfullyFlat.rTensor_nontrivial k T k
        have : Nontrivial T := (TensorProduct.lid k T).symm.toEquiv.nontrivial
        obtain ⟨φ⟩ := Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed (K := k) (R := T)
        exact ⟨φ.toRingHom, RingHom.ext fun x ↦ φ.commutes x⟩)
      (Iso.refl _) hS
  obtain ⟨i, hi⟩ := hcover default
  have hO : O i = ⊤ := by
    apply top_unique
    intro x _
    simpa only [Subsingleton.elim x default] using hi
  have hι : IsIso (O i).ι := by rw [hO]; exact (Scheme.topIso _).isIso_hom
  let f := Scheme.ProEt.ofOpenImmersionHom
    (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) (O i).ι
  let g : Scheme.ProEt.mk (𝟙 (Spec (.of k))) ⟶
      Scheme.ProEt.ofOpenImmersion (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) (O i).ι :=
    MorphismProperty.Over.homMk (inv (O i).ι) (by
      change inv (O i).ι ≫ ((O i).ι ≫ 𝟙 _) = 𝟙 _
      simp)
  have hgf : g ≫ f = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change inv (O i).ι ≫ (O i).ι = 𝟙 _
    simp
  apply S.id_mem_iff_eq_top.mp
  rw [← hgf]
  exact S.downward_closed (hmem i) g

/-- The representative-normalized sections cup over the actual scalar ring Lambda(*).
The ordinary tensorator multiplies pure sections, its unit is the canonical scalar
map, and ExactSectionsDerivedCup imposes every total-complex summand and the native
localization square. Consequently the data used by the cup are uniquely determined.
Source: Stacks 0FPJ, 0B6C and 0FPK
(blueprint: lem-sf-exact-sections-derived-cup-map).
Proof: apply exists_internal to the reconstructed coefficient ring at the final
object of Spec k. Exactness is pairingPointScalarSections_exact. Restrict scalars
along CohomologyTransport.scalarMap and compose its ordinary unital lax tensorator
with that cup. Its chain components are the direct sums of the section pairings,
so the chain_summand and chainUnit_zero normalizations hold. Localization on K-flat
representatives gives the displayed derived tensorator and unit normalizations.
Pure tensors generate the ordinary tensor, total-tensor inclusions determine each
chain map, and every derived object is represented by a K-flat complex. Thus the
localization square determines each derived tensorator and the unit; all laws are
proof fields, proving uniqueness. No invertibility of the tensorator is asserted. -/
theorem pairingExactScalarPointCup_exists :
    ∃! d : CategoryTheory.ExactSectionsDerivedCup
        (CohomologyTransport.sections Λ (Spec (.of k))),
      (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (y : N.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
        (d.ordinary.μ M N).hom (x ⊗ₜ[condensedScalarRing Λ] y) =
          InternalAbelianSheafModule.comparison_internalTmul
            (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))
            M N (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y) ∧
      (∀ a : condensedScalarRing Λ,
        d.ordinary.ε.hom a = CohomologyTransport.scalarMap Λ (Spec (.of k)) a) := by
  sorry

/-- The unique sectionwise-normalized cup, retaining its signed total-complex and
localization normalizations. This choice is from uniqueness, rather than from a
mere existence of an unconstrained tensor map.
Source: Stacks 0FPJ and 0FPK (blueprint: lem-sf-exact-sections-derived-cup-map). -/
def pairingExactScalarPointCup : CategoryTheory.ExactSectionsDerivedCup
    (CohomologyTransport.sections Λ (Spec (.of k))) :=
  (pairingExactScalarPointCup_exists Λ k).choose

/-- At the geometric point the normalized sections unit is the coefficient ring
identification, so its derived map is invertible.
Source: Stacks 03P2 and the point-coefficient identification
(blueprint: lem-sf-exact-sections-derived-cup-map).
Proof: scalarMap is the composite of the inverse terminal section-ring equivalence
sectionGlobalEquiv, the global-section map of upperStarFromPoint, and terminal
evaluation sectionGlobalEval. Pullback from the point is fully faithful for an
algebraically closed field (isEquivalence_upperStarFromPoint), so the middle map is
bijective (globalMapFunctor_bijective), and both evaluations are bijective. By the
ordinary unit normalization of pairingExactScalarPointCup_exists the ordinary unit
is scalarMap, hence an isomorphism. The chain unit is this map in degree zero by
chainUnit_zero and a map between zero objects in every other degree, so it is an
isomorphism. Both localization unit comparisons are isomorphisms
(localization_isIso_ε). The unit_normalization square identifies the derived unit
followed by two isomorphisms with an isomorphism; cancellation proves the claim. -/
theorem pairingExactScalarPointCup_unit_isIso :
    IsIso (pairingExactScalarPointCup Λ k).derived.ε := by
  let G := CohomologyTransport.sections Λ (Spec (.of k))
  let d := pairingExactScalarPointCup Λ k
  have hscalar := point_scalar_bijective Λ k
  have hordinary : IsIso d.ordinary.ε := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun a ↦ d.ordinary.ε.hom a)
    have hn := (pairingExactScalarPointCup_exists Λ k).choose_spec.1.2
    change ∀ a, d.ordinary.ε.hom a = CohomologyTransport.scalarMap Λ (Spec (.of k)) a at hn
    simpa only [hn] using hscalar
  have hchain : IsIso d.chainUnit := by
    have : ∀ n, IsIso (d.chainUnit.f n) := by
      intro n
      by_cases hn : n = 0
      · subst n
        rw [d.chainUnit_zero]
        infer_instance
      · apply Limits.IsZero.isIso
        · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
        · exact G.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
    exact HomologicalComplex.Hom.isIso_of_components d.chainUnit
  have hQ : IsIso (Functor.LaxMonoidal.ε
      (DerivedCategory.Q : CochainComplex
        (ModuleCat.{u + 1} (condensedScalarRing Λ)) ℤ ⥤ _)) :=
    RingedDerivedNative.localization_isIso_ε
  have hQB : IsIso (Functor.LaxMonoidal.ε
      (DerivedCategory.Q : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k)))) ℤ ⥤ _)) :=
    RingedDerivedNative.localization_isIso_ε
  have hnormalized : IsIso (d.derived.ε ≫
      G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _)) := by
    rw [d.unit_normalization]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _))

/-- The inverse unit comparison furnished by the actual point-coefficient map.
Source: point coefficients and exact sections (blueprint: lem-sf-exact-sections-derived-cup-map). -/
def pairingExactScalarPointCup_unitIso :
    𝟙_ (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) ≅
      (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory.obj (𝟙_ _) :=
  @asIso _ _ _ _ (pairingExactScalarPointCup Λ k).derived.ε
    (pairingExactScalarPointCup_unit_isIso Λ k)

end AlgebraicGeometry.ProEtale.CondensedRing
