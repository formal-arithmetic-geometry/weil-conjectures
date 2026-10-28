/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
public import Sheaf.SixFunctors.IntegralDualizingResolvedGlobalHom
import Sheaf.SixFunctors.IntegralDualizingResolvedMappingTower
import all Sheaf.Paper.CoefficientConstantTowerRoosComparison
import all Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import all Sheaf.CategoryTheory.SequentialTowerEvaluationFull
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-! # Ordinary global Hom models for a resolved strict tower

Source: Stacks 0A95, 0A96 and 0941. This comparison concerns the mapping-tower side
only. It neither mentions the dualizing limit in module sheaves nor a DVR tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

section ModuleLimit
universe r

private theorem moduleRoosInclusionQuasiIso (R : Type r) [CommRing R]
    [HasDerivedCategory (ModuleCat.{r} R)]
    (T : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{r} R) ℤ)
    (hT : ∀ (q : ℤ) (n : ℕ), Epi ((T.X q).map (homOfLE n.le_succ).op)) :
    QuasiIso (roosι T) := by
  let A := ModuleCat.{r} R
  let K := fun n : ℕ ↦ T.asFunctor.obj (op n)
  let P : Fan K := Fan.mk (roosP T) (Pi.π K)
  let s : P.pt ⟶ P.pt := towerProductShift
    (fun n ↦ T.asFunctor.map (homOfLE n.le_succ).op)
  have hs (n : ℕ) : s ≫ P.proj n =
      P.proj (n + 1) ≫ T.asFunctor.map (homOfLE n.le_succ).op := Pi.lift_π _ _
  have hu (q : ℤ) : Epi ((roosU T).f q) := by
    let ev := HomologicalComplex.eval A (.up ℤ) q
    let F := T.asFunctor ⋙ ev
    let B : Fan (fun n : ℕ ↦ F.obj (op n)) :=
      Fan.mk (P.pt.X q) (fun n ↦ (P.proj n).f q)
    have hB : IsLimit B :=
      (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (productIsProduct K))
    have hsp (n : ℕ) : s.f q ≫ B.proj n =
        B.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
      change s.f q ≫ (P.proj n).f q =
        (P.proj (n + 1)).f q ≫ (T.asFunctor.map (homOfLE n.le_succ).op).f q
      simpa only [HomologicalComplex.comp_f] using congrArg (fun f ↦ f.f q) (hs n)
    exact ModuleCat.epi_one_sub_of_epi hB (s.f q) hsp (fun n ↦ hT q n)
  obtain ⟨κ, hκ, hqκ, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi (roosU T) hu
  let hk := Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct K) s hs
    (limit.isLimit T.asFunctor)
  let k : limit T.asFunctor ≅ kernel (roosU T) :=
    hk.conePointUniqueUpToIso (limit.isLimit _)
  have hkι : k.hom ≫ kernel.ι (roosU T) =
      Pi.lift (fun n : ℕ ↦ limit.π T.asFunctor (op n)) := by
    exact hk.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  have heq : k.hom ≫ κ = roosι T := by
    apply HomologicalComplex.hom_ext
    intro q
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective q
    apply (cancel_mono (roosχ T p).hom).mp
    change (k.hom ≫ κ).f (p + 1) ≫ (roosχ T p).hom =
      (roosι T).f (p + 1) ≫ (roosχ T p).hom
    rw [roosι_χ]
    have hκ' (r j : ℤ) (hj : j = r - 1) :
        κ.f r ≫ ((CochainComplex.mappingCone (roosU T)).shiftFunctorObjXIso
          (-1) r j (by omega)).hom ≫
          HomologicalComplex.homotopyCofiber.sndX (roosU T) j = 0 ∧
        κ.f r ≫ ((CochainComplex.mappingCone (roosU T)).shiftFunctorObjXIso
          (-1) r j (by omega)).hom ≫
          HomologicalComplex.homotopyCofiber.fstX (roosU T) j r
            (by change j + 1 = r; omega) = (kernel.ι (roosU T)).f r := by
      subst j
      exact hκ r
    have hsnd' (j : ℤ) (h : (ComplexShape.up ℤ).Rel p j) :
        HomologicalComplex.homotopyCofiber.sndX (roosU T) p =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU T) p j h).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' h
      simp only [HomologicalComplex.homotopyCofiber.sndX, dif_pos h]
    have hsnd := hsnd' (p + 1) rfl
    apply biprod.hom_ext
    · have h := (hκ' (p + 1) p (by omega)).1
      simpa only [roosχ, Iso.trans_hom, Category.assoc,
        biprod.braiding_hom, biprod.lift_fst, biprod.lift_snd,
        HomologicalComplex.comp_f, hsnd, comp_zero] using
          congrArg (fun f ↦ k.hom.f (p + 1) ≫ f) h
    · have h := (hκ' (p + 1) p (by omega)).2
      have hkf := congrArg (fun f ↦ f.f (p + 1)) hkι
      simpa only [roosχ, Iso.trans_hom, Category.assoc,
        biprod.braiding_hom, biprod.lift_fst, biprod.lift_snd,
        HomologicalComplex.comp_f, HomologicalComplex.homotopyCofiber.fstX] using
          (congrArg (fun f ↦ k.hom.f (p + 1) ≫ f) h).trans hkf
  rw [← heq]
  have : QuasiIso κ := hqκ
  infer_instance

private theorem moduleLimitUnitOfSurjective (R : Type r) [CommRing R]
    [HasDerivedCategory (ModuleCat.{r} R)]
    (T : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{r} R) ℤ)
    (hT : ∀ (q : ℤ) (n : ℕ), Epi ((T.X q).map (homOfLE n.le_succ).op)) :
    IsIso ((lim : (ℕᵒᵖ ⥤ ModuleCat.{r} R) ⥤ _).rightDerivedFunctorUnitQ T) := by
  let A := ModuleCat.{r} R
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) :=
    { ab5OfSize := ⟨fun _ _ _ ↦ inferInstance⟩ }
  let L : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let β := (Functor.isoWhiskerRight (strictTowerLimitIso (A := A))
    DerivedCategory.Q).hom ≫ η
  obtain ⟨e, he⟩ := normalizedRoosIso L.rightDerivedFunctor β (fun I hI ↦ by
    have := hI
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, η]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    exact ((DerivedCategory.Q.mapIso ((strictTowerLimitIso (A := A)).app I)) ≪≫
      (L.rightDerivedFunctorObjQIso I).symm).isIso_hom)
  have : QuasiIso (roosι T) := moduleRoosInclusionQuasiIso R T hT
  have hβ : IsIso (β.app T) := by
    rw [← congr_app he T]
    change IsIso (DerivedCategory.Q.map (roosι T) ≫ e.hom.app T)
    infer_instance
  have : IsIso
      ((Functor.isoWhiskerRight (strictTowerLimitIso (A := A)) DerivedCategory.Q).hom.app T ≫
        η.app T) := hβ
  exact IsIso.of_isIso_comp_left
    ((Functor.isoWhiskerRight (strictTowerLimitIso (A := A)) DerivedCategory.Q).hom.app T)
    (η.app T)

end ModuleLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem homComplex_post_split
    (P J K : CochainComplex (scalarReductionSource l E X) ℤ) (f : J ⟶ K)
    (hf : ∀ q : ℤ, IsSplitEpi (f.f q)) (q : ℤ) :
    IsSplitEpi ((((homComplexFunctor
      (R := completedIntegralCommRingSheafUnrestricted l E X)).obj (op P)).map f).f q) := by
  classical
  have (r : ℤ) : IsSplitEpi (f.f r) := hf r
  obtain ⟨π, hπ, _, hm⟩ :=
    homComplex_projections_exists.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
  let a := ((homComplexFunctor
    (R := completedIntegralCommRingSheafUnrestricted l E X)).obj (op P)).map f
  have ha (p : ℤ) : a.f q ≫ π P K q p (p + q) rfl =
      π P J q p (p + q) rfl ≫ SheafOfModules.homObjMap
        (R := completedIntegralCommRingSheafUnrestricted l E X) (𝟙 (P.X p)) (f.f (p + q)) := by
    have h := hm P P J K (𝟙 P) f q p (p + q) rfl
    have hi : (homComplexFunctor
        (R := completedIntegralCommRingSheafUnrestricted l E X)).map (𝟙 P).op =
          𝟙 _ := by
      change (homComplexFunctor
        (R := completedIntegralCommRingSheafUnrestricted l E X)).map (𝟙 (op P)) = _
      exact CategoryTheory.Functor.map_id _ _
    rw [hi] at h
    simpa only [NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f] using h
  let r := Fan.IsLimit.lift (hπ P J q).some (fun p : ℤ ↦
    π P K q p (p + q) rfl ≫
      SheafOfModules.homObjMap
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (𝟙 (P.X p)) (section_ (f.f (p + q))))
  have hr (p : ℤ) : r ≫ π P J q p (p + q) rfl =
      π P K q p (p + q) rfl ≫ SheafOfModules.homObjMap
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (𝟙 (P.X p)) (section_ (f.f (p + q))) :=
    Fan.IsLimit.fac (hπ P J q).some _ p
  refine IsSplitEpi.mk' ⟨r, ?_⟩
  apply Fan.IsLimit.hom_ext (hπ P K q).some
  intro p
  change (r ≫ a.f q) ≫ π P K q p (p + q) rfl =
    𝟙 _ ≫ π P K q p (p + q) rfl
  rw [Category.assoc, ha, ← Category.assoc, hr]
  simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    Category.id_comp, IsSplitEpi.id, SheafOfModules.homObjMap_id, Category.comp_id]

private theorem resolvedMappingCochains_epi
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
    (hinj : ∀ q : ℤ, Injective (I.X q))
    (P : (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ) (q : ℤ) (n : ℕ) :
    Epi ((((integralDualizingResolvedMappingCochains l E X I).obj P).X q).map
      (homOfLE n.le_succ).op) := by
  let Γ := RingedSiteGlobalRHom.sections
    (completedIntegralCommRingSheafUnrestricted l E X)
    (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X)
  let t := I.asFunctor.map (homOfLE n.le_succ).op
  have ht (r : ℤ) : IsSplitEpi (t.f r) := by
    have : Injective (I.X r) := hinj r
    exact injective_tower_transition_split (I.X r) n
  have hs := homComplex_post_split l E X P.unop _ _ t ht q
  change Epi (Γ.map ((((homComplexFunctor
    (R := completedIntegralCommRingSheafUnrestricted l E X)).obj P).map t).f q))
  infer_instance

attribute [local irreducible] integralDualizingResolvedHom
  CategoryTheory.Functor.rightDerivedFunctor coefHomDerivedConstant
  coefHomConstantInternalHom coefHomConstantDerivedSections coefHomEquivalence

@[irreducible] private def resolvedMappingCochainsIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    integralDualizingResolvedMappingCochains l E X I ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      integralDualizingResolvedHom l E X ⋙
        (Functor.whiskeringLeft _ _ _).obj I.asFunctor :=
  Iso.refl _

/-- The same strict mapping tower on every source object, before constructibility.
Source: Stacks 0A95, 0941
(blueprint: lem-coef-integral-dualizing-resolved-mapping-limit). -/
def integralDualizingAmbientMappingTower
    (Z : DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E X)) :
    (DerivedCategory (scalarReductionSource l E X))ᵒᵖ ⥤ coefPairingDerived l E :=
  (coefHomDerivedConstant l E X).op ⋙
    (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
      ((coefHomEquivalence l E X).inverse.mapDerivedCategory.obj Z) ⋙
        coefHomConstantDerivedSections l E X

/-- Global Hom into the evaluated complexes of a strict tower, followed by the
ordinary limit in complexes and localization. No derived limit occurs in this model.
Source: Stacks 08JA, 0941
(blueprint: lem-coef-integral-dualizing-resolved-mapping-limit). -/
def integralDualizingResolvedHomLimit
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  integralDualizingResolvedHom l E X ⋙
    (Functor.whiskeringLeft _ _ _).obj I.asFunctor ⋙ lim ⋙ DerivedCategory.Q

/-- A resolved strict mapping tower is computed by the ordinary limiting complex
of global Hom cochains, naturally in its source complex.

Source: Stacks 0A95, 0A96, 08JA and 0941; blueprint prop-coef-integral-dualizing,
second displayed paragraph, and the resolved-tower model in its mapping-limit step.
(blueprint: lem-coef-integral-dualizing-resolved-mapping-limit).

Proof: the section-preserving constant-ring sequence equivalence carries I to a
K-injective sequence-site complex. For flat-term K-flat P, its constant sequence
is K-flat; the sequence internal-Hom and derived-sections comparison therefore
computes the strict signed complex Hom(P,I_n), with postcomposition transitions.
The slice restriction and reconstruction formulas for coefHomSequenceSections_iso
commute with precomposition, so this identification is natural in P. For arbitrary
P, precompose a K-flat resolution; K-injectivity of I and its evaluations makes
both global Hom complexes invert this quasi-isomorphism. Integral scalar actions
are unchanged by the section-preserving equivalence. Each term of I is an injective
tower, so consecutive transitions split. The same splittings act by postcomposition
on global Hom cochains. Thus 1-shift on their product is degreewise surjective:
start with x_0=0 and lift x_n-b_n recursively along each transition. Its kernel is
the ordinary limit. Exact products of integral modules identify its kernel-to-Roos
cone inclusion as a quasi-isomorphism, computing CoefTower.totalLimit. These
inclusions and all previous comparisons commute with precomposition. This proves
the stated natural isomorphism, including for zero inputs or zero transitions. -/
theorem integralDualizing_resolved_mappingLimit
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
    [I.IsKInjective] (hinj : ∀ q : ℤ, Injective (I.X q)) :
    Nonempty (DerivedCategory.Q.op ⋙
      integralDualizingAmbientMappingTower l E X (DerivedCategory.Q.obj I) ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E) ≅
      integralDualizingResolvedHomLimit l E X I) := by
  obtain ⟨a⟩ := integralDualizing_resolved_mappingTower l E X I
  let H := integralDualizingResolvedMappingCochains l E X I
  let A := ModuleCat.{u + 1} (integralDualizingCoefficients l E)
  let L : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let β := Functor.whiskerLeft H η
  have hβ (P) : IsIso (β.app P) :=
    moduleLimitUnitOfSurjective (integralDualizingCoefficients l E) (H.obj P)
      (resolvedMappingCochains_epi l E X I hinj P)
  have : IsIso β := (NatTrans.isIso_iff_isIso_app β).mpr hβ
  let c := resolvedMappingCochainsIso l E X I
  let d := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft H (strictTowerLimitIso (A := A)).symm) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight c (lim ⋙ DerivedCategory.Q)
  exact ⟨Functor.isoWhiskerRight a L.rightDerivedFunctor ≪≫
    (asIso β).symm ≪≫ d⟩

end WeilConjectures
