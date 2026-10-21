/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.SheafExt
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.Algebra.Homology.HomComplexToSingle
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.AlgebraicGeometry.FiniteFreeResolutionSheafification
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictScheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Coherence of sheaf Ext

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.11.5 (Tag 0D0C)
(blueprint: lem-sc-sheaf-ext-coherent).
-/

@[expose] public section

universe u₁ w₁ u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry


-- The affine resolution construction only uses local Noetherianity. Keep the source
-- theorem unchanged and use its construction with the weaker local hypothesis here.
private theorem local_free_resolution
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (x : X) :
    ∃ (U : X.Opens) (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A)
      (_ : x ∈ U) (_ : IsAffineOpen U)
      (M : Type u) (_ : AddCommGroup M) (_ : Module A M) (_ : Module.Finite A M)
      (e : U.toScheme ≅ Spec (CommRingCat.of A)),
      Nonempty (F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj
        (tilde (ModuleCat.of A M))) ∧
      ∃ (E : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ),
        (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (E.X i)) ∧
        (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
        ∃ q : E ⟶ (CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) 0).obj (F.over U),
          QuasiIso q := by
  obtain ⟨hq, ht⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := ht
  obtain ⟨D, hD⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ D.X).mp D.coversTop).exists_mem x
  obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset hxi
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let W : X.Opens := D.X i
  let f := hU.fromSpec
  let v : Spec Γ(X, U) ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι f (by
      rw [Scheme.Opens.range_ι]
      exact hU.opensRange_fromSpec.le.trans hUi)
  have hv : v ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (v ≫ W.ι) := by rw [hv]; infer_instance
  have : IsOpenImmersion v := IsOpenImmersion.of_comp v W.ι
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor v) :=
    inferInstance
  let H := (Scheme.Modules.overEquiv (D.X i)).functor ⋙
    Scheme.Modules.restrictFunctor v
  let a₀ : SheafOfModules.overFunctor X.ringCatSheaf (D.X i) ⋙ H ≅
      Scheme.Modules.restrictFunctor f :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (D.X i)) _ ≪≫
      (Scheme.Modules.restrictFunctorComp v W.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hv
  have := hD.isFiniteType i
  let σ := ((D.generators i).map H (Scheme.Modules.restrictUnitIso v).symm).ofEpi
    (a₀.app F).hom
  let G := F.restrict hU.fromSpec
  let M := moduleSpecΓFunctor.obj G
  have : Module.Finite Γ(X, U) Γ(G, ⊤) :=
    Scheme.Modules.finite_sections_top_of_isIso_fromTildeΓ G σ
  have : Module.Finite Γ(X, U) M :=
    inferInstanceAs (Module.Finite Γ(X, U) Γ(G, ⊤))
  let e := hU.isoSpec
  let a : F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj G :=
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec.symm).app F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom hU.fromSpec).app F
  let b : G ≅ tilde M := (asIso G.fromTildeΓ).symm
  let c := a ≪≫ (Scheme.Modules.restrictFunctor e.hom).mapIso b
  refine ⟨U, Γ(X, U), inferInstance, inferInstance, hxU, hU,
    M, inferInstance, inferInstance, inferInstance, e, ⟨c⟩, ?_⟩
  obtain ⟨n, ε, d, hε, h₀, hd⟩ := Module.exists_finite_free_resolution Γ(X, U) M
  obtain ⟨E, hbound, hfree, q, hq⟩ :=
    finite_free_resolution_sheafification X U Γ(X, U) e M n ε d hε h₀ hd
  let t : F.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj
      ((Scheme.Modules.restrictFunctor e.hom).obj (tilde (ModuleCat.of Γ(X, U) M))) :=
    (Scheme.Modules.overEquiv U).unitIso.app (F.over U) ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv U).app F ≪≫ c)
  have : QuasiIso q := hq
  refine ⟨E, hbound, hfree, q ≫ (CochainComplex.singleFunctor _ 0).map t.inv, ?_⟩
  infer_instance


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Scheme.Modules.overEquiv Scheme.Modules.restrictFunctor
  homComplexFunctor derivedInternalHom

-- The scalar Hom computation works with any module in the second argument.
private theorem local_homology_model
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (K G : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj K)) [QuasiIso ε] (q : ℤ) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj (moduleSheafExt Y q K G) ≅
      (homComplex (R := U.toScheme.toRingedSpace.sheaf) E
        ((CochainComplex.singleFunctor U.toScheme.Modules 0).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj G))).homology q) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let O := SheafOfModules.overFunctor.{u} Y.ringCatSheaf U
  let T := (Scheme.Modules.overEquiv U).functor
  let : PreservesFiniteLimits O := moduleOverFunctor_limits_proof Y.toRingedSpace U
  let : PreservesFiniteColimits O := moduleOverFunctor_colimits_proof Y.toRingedSpace U
  let : PreservesFiniteLimits (O ⋙ T) := comp_preservesFiniteLimits O T
  let : PreservesFiniteColimits (O ⋙ T) := comp_preservesFiniteColimits O T
  let : T.Additive := T.additive_of_preserves_binary_products
  let R := O ⋙ T
  have hRAdd : R.Additive := R.additive_of_preserves_binary_products
  let eR : R ≅ Scheme.Modules.restrictFunctor U.ι := Scheme.Modules.overFunctorEquiv U
  have hRestrAdd : (Scheme.Modules.restrictFunctor U.ι).Additive :=
    @Functor.additive_of_iso _ _ _ _ _ _ R hRAdd _ eR
  have hRestrZero : (Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ hRestrAdd
  have hRZero : R.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ R hRAdd
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let eRc := @NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ R
    (Scheme.Modules.restrictFunctor U.ι) hRZero hRestrZero eR (.up ℤ)
  let L := (CochainComplex.singleFunctor A 0).obj K
  let M := (CochainComplex.singleFunctor A 0).obj G
  obtain ⟨I, η, hη, _, _, hI⟩ := SheafOfModules.exists_boundedBelow_injective_resolution
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf M ⟨0, inferInstance⟩
  let : QuasiIso η := hη
  let : I.IsKInjective := hI
  let eI : DerivedCategory.Q.obj I ≅ (DerivedCategory.singleFunctor A 0).obj
      G := (asIso (DerivedCategory.Q.map η)).symm
  let DY := (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
    (op ((DerivedCategory.singleFunctor A 0).obj K),
      (DerivedCategory.singleFunctor A 0).obj G)
  obtain ⟨eY⟩ := derivedInternalHom_obj_iso.{u, w} (Opens.grothendieckTopology Y)
    Y.toRingedSpace.sheaf ((DerivedCategory.singleFunctor A 0).obj K)
    ((DerivedCategory.singleFunctor A 0).obj G)
    L I (Iso.refl _) eI
  let : (Scheme.Modules.overEquiv U).symm.functor.Additive :=
    (Scheme.Modules.overEquiv U).symm.functor.additive_of_preserves_binary_products
  let : T.PreservesKInjectiveComplexes :=
    (Scheme.Modules.overEquiv U).symm.toAdjunction.preservesKInjectiveComplexes
  let : CochainComplex.IsKInjective ((O.mapHomologicalComplex (.up ℤ)).obj I) :=
    kInjective_of_restrict_open Y.toRingedSpace U I
  let : CochainComplex.IsKInjective ((T.mapHomologicalComplex (.up ℤ)).obj
      ((O.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
  have hRcKI : CochainComplex.IsKInjective (Rc.obj I) :=
    CochainComplex.isKInjective_of_iso (L₁ := (T.mapHomologicalComplex (.up ℤ)).obj
      ((O.mapHomologicalComplex (.up ℤ)).obj I))
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (O ⋙ T)) (.up ℤ)).app I)
  let B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let : HasDerivedCategory.{u + 1} B := HasDerivedCategory.standard B
  let QU := @DerivedCategory.Q B _ _ (HasDerivedCategory.standard B)
  let KU := (CochainComplex.singleFunctor B 0).obj
    ((Scheme.Modules.restrictFunctor U.ι).obj K)
  let GU := (CochainComplex.singleFunctor B 0).obj
    ((Scheme.Modules.restrictFunctor U.ι).obj G)
  let eL : Rc.obj L ≅ KU :=
    (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app K ≪≫
      (CochainComplex.singleFunctor B 0).mapIso (eR.app K)
  let eM : Rc.obj M ≅ GU :=
    (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app _ ≪≫
      (CochainComplex.singleFunctor B 0).mapIso
        (eR.app G)
  have hRcη : QuasiIso (Rc.map η) := inferInstance
  let : IsIso (QU.map (Rc.map η)) :=
    (@DerivedCategory.isIso_Q_map_iff_quasiIso B _ _ (HasDerivedCategory.standard B)
      _ _ (Rc.map η)).mpr hRcη
  let eIU : QU.obj (Rc.obj I) ≅ QU.obj GU :=
    (asIso (QU.map (Rc.map η))).symm ≪≫ QU.mapIso eM
  obtain ⟨eU⟩ := @derivedInternalHom_obj_iso.{u, u + 1}
    (TopologicalSpace.Opens U.toScheme) _ (Opens.grothendieckTopology U.toScheme)
    U.toScheme.toRingedSpace.sheaf (HasDerivedCategory.standard B) (QU.obj KU) (QU.obj GU)
    (Rc.obj L) (Rc.obj I) hRcKI (QU.mapIso eL) eIU
  have hε : QuasiIso ε := inferInstance
  obtain ⟨eE⟩ := @derivedInternalHom_of_boundedAbove_finiteFree.{u, u + 1}
    U.toScheme.toRingedSpace (HasDerivedCategory.standard B) E GU KU hbounded hfree
    ⟨0, fun i hi ↦
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i (ne_of_lt hi)⟩ ε hε
  obtain ⟨eC⟩ := homComplex_restrict_scheme U L I
  let changeInputs := (Functor.uncurry.obj
    (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf))).mapIso
      ((eRc.app L).op.prod
        (eRc.app I).symm)
  let H := homComplex (R := Y.toRingedSpace.sheaf) L I
  let HY := DerivedCategory.homologyFunctor A q
  let HU := @DerivedCategory.homologyFunctor B _ _ (HasDerivedCategory.standard B) q
  let fU := @DerivedCategory.homologyFunctorFactors B _ _ (HasDerivedCategory.standard B) q
  let eH : R.obj (HY.obj DY) ≅
      (homComplex (R := U.toScheme.toRingedSpace.sheaf) E GU).homology q :=
    R.mapIso (HY.mapIso eY ≪≫ (DerivedCategory.homologyFunctorFactors A q).app H) ≪≫
      ((R.mapHomologicalComplexHomologyIso (.up ℤ) q).app H).symm ≪≫
      (HomologicalComplex.homologyFunctor B (.up ℤ) q).mapIso
        (eRc.app H ≪≫ eC ≪≫ changeInputs) ≪≫
      (fU.app _).symm ≪≫
      HU.mapIso (eU.symm ≪≫ eE.symm) ≪≫
      fU.app _
  exact ⟨(eR.app (moduleSheafExt Y q K G)).symm ≪≫ eH⟩

private theorem coherent_homology (X : Scheme.{u}) (C : CochainComplex X.Modules ℤ)
    (hC : ∀ i, RingedSpace.IsCoherent X.toRingedSpace (C.X i)) (q : ℤ) :
    RingedSpace.IsCoherent X.toRingedSpace (C.homology q) := by
  let h := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  let S := C.sc q
  have hk : RingedSpace.IsCoherent X.toRingedSpace (kernel S.g) :=
    (h.1 _ _ S.g (hC q) (hC _)).1
  have hh := (h.1 _ _ (kernel.lift S.g S.f S.zero) (hC _) hk).2
  exact h.2.2.2.2 _ _ S.homologyIsoCokernelLift.symm hh

private theorem coherent_finite_free_homology (X : Scheme.{u})
    (E : CochainComplex X.Modules ℤ) (G : X.Modules)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hE : ∀ i, ∃ r : ℕ, Nonempty (E.X i ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) (q : ℤ) :
    RingedSpace.IsCoherent X.toRingedSpace
      ((homComplex (R := X.sheaf) E
        ((CochainComplex.singleFunctor X.Modules 0).obj G)).homology q) := by
  obtain ⟨e⟩ := homComplex_to_single_iso (R := X.sheaf) E G
  let h := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have hc (i : ℤ) : RingedSpace.IsCoherent X.toRingedSpace
      ((signedSheafDualComplex (R := X.sheaf) E G).X i) := by
    obtain ⟨r, ⟨a⟩⟩ := hE (-i)
    let b : SheafOfModules.homObj (R := X.sheaf) (E.X (-i)) G ≅
        ⨁ fun _ : Fin r ↦ G :=
      ((SheafOfModules.homFunctor X.sheaf).flip.obj G).mapIso a.symm.op ≪≫
        SheafOfModules.homObjFreeIso G (ULift.{u} (Fin r)) ≪≫
        biproduct.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl G)
    exact h.2.2.2.2 _ _ b.symm (h.2.2.1 r (fun _ ↦ G) (fun _ ↦ hG))
  exact h.2.2.2.2 _ _ (HomologicalComplex.homologyMapIso e q).symm
    (coherent_homology X _ hc q)

/-- On a locally Noetherian scheme, sheaf Ext of coherent modules is coherent in every
integer degree. Source: Stacks Project, Derived Categories of Schemes, Lemma 36.11.5
(Tag 0D0C) (blueprint: lem-sc-sheaf-ext-coherent). 

Proof:
1. Work locally on an affine open `U = Spec A` with `A` Noetherian
   (`pqf-def-locnoeth`). Coherent modules are quasi-coherent of finite type
   (`pqf-lem-coherent-ft-locnoeth`). Thus their sections `M = F(U)` and `N = G(U)`
   are finite A-modules (`lem-weil-pbc-quasi-coherent-finite-type-affine`), and
   the affine counits identify their associated sheaves with the restrictions of F and G
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`).
2. Sheaf Ext is the cohomology sheaf of derived internal Hom
   (`def-weil-pbc-sheaf-ext`). Cohomology sheaves commute with open restriction,
   as does derived internal Hom (`lem-sc-derived-internal-hom-restrict-open`, Tag 08DL).
   The affine calculation (`lem-sc-affine-rhom-qcoherent`) identifies this restriction
   with zero for q < 0 and with the associated sheaf of Ext^q_A(M,N) for q >= 0.
3. For q >= 0, Ext^q_A(M,N) is finite (`lem-sc-ext-noetherian-finite`), so its
   associated sheaf is quasi-coherent and of finite type, by the affine adjunction
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`) and the affine finite-type criterion
   (`lem-weil-pbc-quasi-coherent-finite-type-affine`). For q < 0 the zero sheaf is coherent.
   Quasi-coherence and finite type are local on X, hence all these sheaf Ext modules
   are coherent (`pqf-lem-coherent-ft-locnoeth`, Tag 01XZ).
-/
theorem sheafExt_isCoherent (X : Scheme.{u₁}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (F G : SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∀ q : ℤ, RingedSpace.IsCoherent X.toRingedSpace (moduleSheafExt X q F G) := by
  classical
  choose U A hA hnoeth hx hU M hM hmod hfin e he E hb hf ε hε using
    local_free_resolution X F hF
  have hcover : (⨆ x, U x) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  intro q
  apply (coherent_module_local_on_open_cover X (moduleSheafExt X q F G)
    X U hcover).2
  intro x
  let T := (Scheme.Modules.overEquiv (U x)).functor
  have : T.Additive := Functor.additive_of_preserves_binary_products T
  let Ec := (T.mapHomologicalComplex (.up ℤ)).obj (E x)
  let η : Ec ⟶ (CochainComplex.singleFunctor (U x).toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor (U x).ι).obj F) :=
    (T.mapHomologicalComplex (.up ℤ)).map (ε x) ≫
      ((HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app (F.over (U x))).hom ≫
      (CochainComplex.singleFunctor _ 0).map ((Scheme.Modules.overFunctorEquiv (U x)).app F).hom
  have : QuasiIso (ε x) := hε x
  have : QuasiIso η := by dsimp only [η]; infer_instance
  have hb' : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (Ec.X i) := by
    obtain ⟨N, hN⟩ := hb x
    exact ⟨N, fun i hi ↦ T.map_isZero (hN i hi)⟩
  have hf' (i : ℤ) : ∃ r : ℕ, Nonempty (Ec.X i ≅
      SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (ULift.{u₁} (Fin r))) := by
    obtain ⟨r, ⟨a⟩⟩ := hf x i
    have eunit : SheafOfModules.unit (U x).toScheme.ringCatSheaf ≅
        T.obj (SheafOfModules.unit (X.ringCatSheaf.over (U x))) :=
      Scheme.Modules.overEquivFunctorObjUnitIso (U x)
    exact ⟨r, ⟨T.mapIso a ≪≫
      (SheafOfModules.mapFreeIso T (ULift.{u₁} (Fin r)) eunit).symm⟩⟩
  obtain ⟨a⟩ := local_homology_model (U x) F G Ec hb' hf' η q
  have hG' := (coherent_module_local_on_open_cover X G X U hcover).1 hG (U x)
  exact (RingedSpace.coherent_kernel_cokernel_sum (U x).toScheme.toRingedSpace).2.2.2.2
    _ _ a.symm (coherent_finite_free_homology (U x).toScheme Ec _ hG' hf' q)

end AlgebraicGeometry
