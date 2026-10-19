/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex
public import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# The supported-kernel adjunction and its unbounded derived counit

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
lem-exc-proetale-support-triangle, first and last sentences of the proof;
Stacks Project, Tags 08BJ, 070I, 070K, 070Y, 079P, 079Q and 015F
(blueprint: lem-exc-proetale-derived-adjunction-triangle).

The existing finiteSupportedKernel and finiteSupportedH constructions are reused.
All coefficients are left modules over the actual continuous-function ring sheaves,
including noncommutative finite rings. The open restriction hypothesis spells out
coefficient compatibility, naturality, and the normalization of the actual unit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem kan_of_full_whiskering
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (G : D ⥤ E)
    [((Functor.whiskeringLeft C D E).obj L).Full]
    [((Functor.whiskeringLeft C D E).obj L).Faithful]
    {F : C ⥤ E} (e : F ≅ L ⋙ G) : G.IsLeftKanExtension e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  let W := (Functor.whiskeringLeft C D E).obj L
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun Y ↦ StructuredArrow.homMk (W.preimage (e.inv ≫ Y.hom)) ?_) ?_⟩⟩
  · change e.hom ≫ W.map (W.preimage (e.inv ≫ Y.hom)) = Y.hom
    rw [W.map_preimage]
    simp
  · intro Y m
    apply StructuredArrow.hom_ext
    apply W.map_injective
    change W.map m.right = W.map (W.preimage (e.inv ≫ Y.hom))
    rw [W.map_preimage]
    have h := m.w
    change e.hom ≫ W.map m.right = Y.hom at h
    rw [← h]
    simp


/-- Closed pushforward is left adjoint to H = i* ker(1 → j*j*), with the specified
supported-kernel counit, and its termwise descent is left adjoint to the total right
derived H. The comparison beta computes RH on every K-injective complex. The final
isomorphism c is fixed by the exact-pushforward comparison and beta, and identifies
the derived counit with Q of the actual termwise sheaf counit.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
lem-exc-proetale-support-triangle, first and last sentences of its proof;
Stacks Project, Tags 08BJ, 070I, 070K, 070Y, 079P, 079Q and 015F
(blueprint: lem-exc-proetale-derived-adjunction-triangle).

Proof:
1. Kernels are sectionwise by def-weil-sheaf-of-modules-category. The restriction
   hypothesis makes the open unit the identity on an object over U, using the
   base-change formula of def-weil-proetale-inverse-image. Thus j*F(N) = 0.
   The supported-unit assumption gives the natural isomorphism theta, whose
   components are exactly the closed units. Kernel maps and i* are additive by
   prop-weil-pbc-proetale-constant-exact, as in the existing F and H constructions.
2. For h:i*M → N, naturality of the open unit and j*i*M = 0 factor h uniquely
   through F(N). Full faithfulness of i* then gives the unique map M → H(N).
   Conversely compose i* of such a map with theta inverse and the kernel inclusion.
   Kernel uniqueness and full faithfulness show the two natural maps are inverse.
   The transpose of the identity is the asserted sheaf counit.
3. Lift the additive adjunction to complexes and homotopy categories by
   lem-weil-pbc-termwise-adjunction-homotopy. Its counit is the termwise chain map.
   Exactness of the left adjoint gives K-injectivity of H(I) by
   lem-weil-pbc-right-adjoint-preserves-kinjective, without boundedness assumptions.
4. Apply lem-weil-pbc-ring-sheaves-grothendieck on the small site models and
   lem-weil-pbc-kinjective-functorial-existence. Both module categories have enough
   K-injectives, also for noncommutative rings, by transport back to the original sites.
5. Additivity preserves the cone block differential, the inclusion, the negative
   projection, and the shifted differential. Hence the homotopy functor followed by Q
   is exact, by def-weil-abstract-derived-category, lem-pur-homotopy-category-triangulated
   and def-weil-triangulated-category. Apply lem-weil-pbc-kinjective-total-derived:
   RH exists with beta invertible on every K-injective I.
6. By lem-sf-exact-functor-derived-triangulated, exact i* has its termwise descent L
   and factorization a. For a complex M and K-injective I, identify Hom(L QM,QI)
   with Hom_K(i*M,I), then Hom_K(M,H(I)), then Hom_D(QM,QH(I)), using
   lem-weil-pbc-kinjective-hom-derived and the termwise homotopy adjunction.
   Postcomposition with beta_I gives Hom_D(QM,RH(QI)).
7. Naturality holds for chain maps and their homotopy classes. Every morphism
   between K-injectives is a unique such class. In the source variable, localization
   extends naturality to inverse quasi-isomorphisms. Every target has a K-injective
   representative, and transport is independent of that representative by naturality.
   Thus these are bifunctorial Hom bijections on the full derived categories.
8. The termwise counit transposes to the identity of H(I). Under the derived
   bijection its localized map, preceded by a, transposes to beta_I. Hence the
   derived counit is its composite with L(beta_I inverse). The inverse comparison
   a inverse followed by L(beta_I) is precisely c and gives the final two formulas.
   Step 2 identifies its degreewise arrows with the claimed kernel inclusions. -/
theorem finiteSupportedH_derivedAdjunction
    {T Z U : Scheme.{u}} (i : Z ⟶ T) (j : U ⟶ T)
    [IsLocallyNoetherian T] [CompactSpace T]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (A : Type (u + 1)) [Ring A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    [PreservesFiniteLimits (finiteModulePushforward i A)]
    [PreservesFiniteColimits (finiteModulePushforward i A)]
    [(finiteModulePushforward i A).Full] [(finiteModulePushforward i A).Faithful]
    (hRestriction : ∃ d : (finiteCoefficientRingSheaf U A).obj ≅
        (Scheme.proEtaleOpenComposition j).op ⋙ (finiteCoefficientRingSheaf T A).obj,
      (∀ (W : U.ProEt) (a : A),
        (d.hom.app (op W)) ((finiteCoefficientScalarMap U A).app (op W) a) =
          (finiteCoefficientScalarMap T A).app
            (op ((Scheme.proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (N : FiniteCoefficientModules T A) (W : U.ProEt),
          ((finiteCoefficientModulePullback j A).obj N).val.obj (op W) ≃+
            N.val.obj (op ((Scheme.proEtaleOpenComposition j).obj W)),
        (∀ (N : FiniteCoefficientModules T A) (W : U.ProEt)
          (r : (finiteCoefficientRingSheaf U A).obj.obj (op W))
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W (r • m) = (d.hom.app (op W) r) • rho N W m) ∧
        (∀ (N : FiniteCoefficientModules T A) (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W' (((finiteCoefficientModulePullback j A).obj N).val.map b.op m) =
            N.val.map ((Scheme.proEtaleOpenComposition j).map b).op (rho N W m)) ∧
        (∀ (N N' : FiniteCoefficientModules T A) (h : N ⟶ N') (W : U.ProEt)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N' W (((finiteCoefficientModulePullback j A).map h).val.app (op W) m) =
            h.val.app (op ((Scheme.proEtaleOpenComposition j).obj W)) (rho N W m)) ∧
        (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
          rho N ((Scheme.proEtaleBaseChange j).obj V)
              (((finiteModuleAdjunction j A).unit.app N).val.app (op V) m) =
            N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m))
    (hVanishing : ∀ M : FiniteCoefficientModules Z A,
      IsZero ((finiteCoefficientModulePullback j A).obj
        ((finiteModulePushforward i A).obj M)))
    (hSupported : ∀ N : FiniteCoefficientModules T A,
      IsZero ((finiteCoefficientModulePullback j A).obj N) →
        IsIso ((finiteModuleAdjunction i A).unit.app N)) :
    ∃ theta : finiteSupportedKernel j A ≅ finiteSupportedH i j A ⋙ finiteModulePushforward i A,
      (∀ N : FiniteCoefficientModules T A,
        theta.hom.app N =
          (finiteModuleAdjunction i A).unit.app ((finiteSupportedKernel j A).obj N)) ∧
      ∃ adj : finiteModulePushforward i A ⊣ finiteSupportedH i j A,
        (∀ N : FiniteCoefficientModules T A,
          adj.counit.app N = theta.inv.app N ≫
            kernel.ι ((finiteModuleAdjunction j A).unit.app N)) ∧
        ∃ (RH : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory Z A)
          (beta : (finiteSupportedH i j A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
            DerivedCategory.Q ⋙ RH),
          RH.IsRightDerivedFunctor beta
              (HomologicalComplex.quasiIso (FiniteCoefficientModules T A) (.up ℤ)) ∧
          ∃ derivedAdj : (finiteModulePushforward i A).mapDerivedCategory ⊣ RH,
            ∀ (I : CochainComplex (FiniteCoefficientModules T A) ℤ) [I.IsKInjective],
              CochainComplex.IsKInjective
                  (((finiteSupportedH i j A).mapHomologicalComplex (.up ℤ)).obj I) ∧
              IsIso (beta.app I) ∧
              ∃ c : DerivedCategory.Q.obj
                    (((finiteModulePushforward i A).mapHomologicalComplex (.up ℤ)).obj
                      (((finiteSupportedH i j A).mapHomologicalComplex (.up ℤ)).obj I)) ≅
                  (finiteModulePushforward i A).mapDerivedCategory.obj
                    (RH.obj (DerivedCategory.Q.obj I)),
                c.hom = (finiteModulePushforward i A).mapDerivedCategoryFactors.inv.app
                    (((finiteSupportedH i j A).mapHomologicalComplex (.up ℤ)).obj I) ≫
                  (finiteModulePushforward i A).mapDerivedCategory.map (beta.app I) ∧
                c.hom ≫ derivedAdj.counit.app (DerivedCategory.Q.obj I) =
                  DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  have _hComplement := hU
  let F := finiteSupportedKernel j A
  let L := finiteModulePushforward i A
  let H := finiteSupportedH i j A
  let r := (finiteModuleAdjunction j A).unit
  have hker (N : FiniteCoefficientModules T A) :
      IsZero ((finiteCoefficientModulePullback j A).obj (F.obj N)) := by
    obtain ⟨d, _, rho, _, _, _, hunit⟩ := hRestriction
    have hsections (W : U.ProEt)
        (x : (F.obj N).val.obj (op ((Scheme.proEtaleOpenComposition j).obj W))) : x = 0 := by
      let V := (Scheme.proEtaleOpenComposition j).obj W
      let k := kernel.ι (r.app N)
      let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
        (inferInstance : WeaklyEtale j) trivial
      let b := (Scheme.proEtaleOpenComposition j).map (a.unit.app W)
      have hbp : b ≫ Scheme.proEtaleOpenSectionProjection j V = 𝟙 V :=
        a.left_triangle_components W
      have hx : k.val.app (op V) x = 0 := by
        have hc := congrArg (fun f ↦ f.val.app (op V) x) (kernel.condition (r.app N))
        change (r.app N).val.app (op V) (k.val.app (op V) x) = 0 at hc
        have hp := hunit N V (k.val.app (op V) x)
        rw [hc, map_zero] at hp
        have hb := congrArg (fun y ↦ N.val.map b.op y) hp.symm
        have hh := N.val.map_comp_apply
          (Scheme.proEtaleOpenSectionProjection j V).op b.op (k.val.app (op V) x)
        rw [← op_comp, hbp] at hh
        change N.val.map (𝟙 (op V)) (k.val.app (op V) x) = _ at hh
        have hh' : k.val.app (op V) x = N.val.map b.op
            (N.val.map (Scheme.proEtaleOpenSectionProjection j V).op
              (k.val.app (op V) x)) := by
          simp only [N.val.map_id, ModuleCat.restrictScalarsId',
            NatIso.ofComponents_inv_app, ModuleCat.restrictScalarsId'App_inv_apply] at hh
          exact hh
        exact hh'.trans (by simpa only [map_zero] using hb)
      let E := SheafOfModules.evaluation (finiteCoefficientRingSheaf T A) (op V)
      have : Mono (E.map k) := inferInstance
      apply ((ModuleCat.mono_iff_injective (E.map k)).mp inferInstance)
      exact hx.trans (map_zero _).symm
    apply (IsZero.iff_id_eq_zero _).mpr
    ext ⟨W⟩ m
    change m = 0
    apply (rho (F.obj N) W).injective
    exact (hsections W _).trans (map_zero _).symm
  have htheta (N : FiniteCoefficientModules T A) :
      IsIso ((finiteModuleAdjunction i A).unit.app (F.obj N)) := hSupported _ (hker N)
  let theta : F ≅ H ⋙ L :=
    NatIso.ofComponents (fun N ↦ asIso ((finiteModuleAdjunction i A).unit.app (F.obj N)))
      (fun {N N'} a ↦ (finiteModuleAdjunction i A).unit.naturality (F.map a))
  have hz (M : FiniteCoefficientModules Z A) (N : FiniteCoefficientModules T A)
      (f : L.obj M ⟶ N) : f ≫ r.app N = 0 := by
    have hf : (finiteCoefficientModulePullback j A).map f = 0 :=
      (hVanishing M).eq_of_src _ _
    calc
      f ≫ r.app N = r.app (L.obj M) ≫
          (finiteModulePushforward j A).map
            ((finiteCoefficientModulePullback j A).map f) := r.naturality f
      _ = 0 := by rw [hf]; simp
  let e (M : FiniteCoefficientModules Z A) (N : FiniteCoefficientModules T A) :
      (L.obj M ⟶ N) ≃ (M ⟶ H.obj N) :=
    { toFun := fun f ↦ L.preimage (kernel.lift (r.app N) f (hz M N f) ≫ theta.hom.app N)
      invFun := fun g ↦ L.map g ≫ theta.inv.app N ≫ kernel.ι (r.app N)
      left_inv := by
        intro f
        simp [Functor.map_preimage, Category.assoc]
      right_inv := by
        intro g
        apply L.map_injective
        simp only [Functor.map_preimage]
        apply (cancel_mono (theta.inv.app N ≫ kernel.ι (r.app N))).mp
        simp [Category.assoc] }
  let adj : L ⊣ H := Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro M M' N a g
        change L.map (a ≫ g) ≫ _ ≫ _ = L.map a ≫ (L.map g ≫ _ ≫ _)
        simp [Functor.map_comp]
      homEquiv_naturality_right := by
        intro M N N' f b
        apply L.map_injective
        change L.map (L.preimage
            (kernel.lift (r.app N') (f ≫ b) (hz M N' (f ≫ b)) ≫ theta.hom.app N')) =
          L.map (L.preimage
            (kernel.lift (r.app N) f (hz M N f) ≫ theta.hom.app N) ≫ H.map b)
        rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage]
        change _ = (kernel.lift (r.app N) f _ ≫ theta.hom.app N) ≫ (H ⋙ L).map b
        rw [Category.assoc, ← theta.hom.naturality b, ← Category.assoc]
        congr 1
        apply (cancel_mono (kernel.ι (r.app N'))).mp
        change _ = kernel.lift (r.app N) f _ ≫
          (finiteSupportedKernel j A).map b ≫ kernel.ι (r.app N')
        rw [finiteSupportedKernelInclusion_naturality, kernel.lift_ι_assoc,
          kernel.lift_ι] }
  refine ⟨theta, fun _ ↦ rfl, adj, ?_, ?_⟩
  · intro N
    change L.map (𝟙 (H.obj N)) ≫ _ ≫ _ = _
    rw [L.map_id, Category.id_comp]
    rfl
  · have : IsGrothendieckAbelian.{u + 1} (FiniteCoefficientModules T A) :=
      SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
        (Scheme.ProEt.topology T) (finiteCoefficientRingSheaf T A)
    have : Abelian.HasKInjectiveResolutions (FiniteCoefficientModules T A) := inferInstance
    let q := HomotopyCategory.quotient (FiniteCoefficientModules T A) (.up ℤ)
    let RH := H.rightDerivedFunctor
    let eh : q ⋙ (H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
        H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (H.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (DerivedCategory.quotientCompQhIso (FiniteCoefficientModules Z A))
    let beta := eh.inv ≫ Functor.whiskerLeft q H.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (DerivedCategory.quotientCompQhIso (FiniteCoefficientModules T A)).hom RH
    have hkan : (H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).IsLeftKanExtension
        eh.inv := kan_of_full_whiskering q _ eh.symm
    have hright : RH.IsRightDerivedFunctor beta
        (HomologicalComplex.quasiIso (FiniteCoefficientModules T A) (.up ℤ)) := by
      constructor
      exact (Functor.isLeftKanExtension_iff_postcompose eh.inv DerivedCategory.Q
        (DerivedCategory.quotientCompQhIso _) H.rightDerivedFunctorUnit beta (by rfl)).mp
          (Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
            (HomotopyCategory.quasiIso (FiniteCoefficientModules T A) (.up ℤ)))
    have hrightcomp : (RH ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
        (Functor.whiskerRight beta L.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom)
        (HomologicalComplex.quasiIso (FiniteCoefficientModules T A) (.up ℤ)) := by
      let bh := Functor.whiskerRight H.rightDerivedFunctorUnit L.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom
      have hb : (RH ⋙ L.mapDerivedCategory).IsLeftKanExtension bh :=
        Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
          (HomotopyCategory.quasiIso (FiniteCoefficientModules T A) (.up ℤ))
      let epost := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eh L.mapDerivedCategory ≪≫
        Functor.associator _ _ _
      have hp : ((H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙
          L.mapDerivedCategory).IsLeftKanExtension epost.inv :=
        kan_of_full_whiskering q _ epost.symm
      constructor
      exact (Functor.isLeftKanExtension_iff_postcompose epost.inv DerivedCategory.Q
        (DerivedCategory.quotientCompQhIso _) bh
        (Functor.whiskerRight beta L.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom) (by
            ext K
            dsimp [beta, bh, epost]
            simp only [Functor.map_comp, Category.id_comp, Category.comp_id]
            rfl)).mp hb
    have hleft : L.mapDerivedCategory.IsLeftDerivedFunctor L.mapDerivedCategoryFactors.hom
        (HomologicalComplex.quasiIso (FiniteCoefficientModules Z A) (.up ℤ)) :=
      Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryFactors
    have hleftcomp : (L.mapDerivedCategory ⋙ RH).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight L.mapDerivedCategoryFactors.hom RH)
        (HomologicalComplex.quasiIso (FiniteCoefficientModules Z A) (.up ℤ)) :=
      Functor.isLeftDerivedFunctor_of_inverts _ _
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight L.mapDerivedCategoryFactors RH)
    let da := (adj.mapHomologicalComplex (.up ℤ)).derived
      (HomologicalComplex.quasiIso (FiniteCoefficientModules Z A) (.up ℤ))
      (HomologicalComplex.quasiIso (FiniteCoefficientModules T A) (.up ℤ))
      L.mapDerivedCategoryFactors.hom beta
    refine ⟨RH, beta, hright, da, ?_⟩
    intro I hI
    have : H.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
    have hbeta : IsIso (beta.app I) := by
      dsimp [beta]
      infer_instance
    refine ⟨inferInstance, hbeta, ?_⟩
    refine ⟨(L.mapDerivedCategoryFactors.app
        ((H.mapHomologicalComplex (.up ℤ)).obj I)).symm ≪≫
      L.mapDerivedCategory.mapIso (asIso (beta.app I)), rfl, ?_⟩
    have he := (adj.mapHomologicalComplex (.up ℤ)).derivedε_fac_app
      (HomologicalComplex.quasiIso (FiniteCoefficientModules T A) (.up ℤ))
      L.mapDerivedCategoryFactors.hom beta I
    change (L.mapDerivedCategoryFactors.inv.app _ ≫
      L.mapDerivedCategory.map (beta.app I)) ≫ da.counit.app _ = _
    change L.mapDerivedCategory.map (beta.app I) ≫ da.counit.app _ = _ at he
    rw [Category.assoc, he]
    simp

end AlgebraicGeometry.ProEtale
