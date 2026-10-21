/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.TelescopeColimit
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.CategoryTheory.RingedCechKoszulComparisonOnSite
import Sheaf.CategoryTheory.RingedCechCompletionHomInjective
import Sheaf.CategoryTheory.RingedCechCompletionRestriction
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.CategoryTheory.RingedCechKoszulColimitIso
import Sheaf.CategoryTheory.RingedCechKoszulDualKFlat

/-!
# Extended Cech complex and the strict Koszul dual limit

Source: Stacks Project, Tags 0913, 0A0A, 0941, 08JB and 0949
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-limit).

A comparison includes its actual strict tower, its total right derived inverse limit,
its unit normalization, and normalized restriction comparisons. Uniqueness of the normalized
natural isomorphisms specifies canonical comparisons, rather than arbitrary isomorphisms.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private def transportCompletionIso
    {A B : Type*} [Category A] [Category B]
    {L D : A ⥤ A} {L' D' : B ⥤ B} (R : A ⥤ B)
    (theta : L ≅ D) (theta' : L' ≅ D') (e : L ⋙ R ≅ R ⋙ L') :
    D ⋙ R ≅ R ⋙ D' :=
  Functor.isoWhiskerRight theta.symm R ≪≫ e ≪≫ Functor.isoWhiskerLeft R theta'

private theorem transportCompletionIso_unit
    {A B : Type*} [Category A] [Category B]
    {L D : A ⥤ A} {L' D' : B ⥤ B} (R : A ⥤ B)
    (eta : ∀ E, E ⟶ L.obj E) (eta' : ∀ E, E ⟶ L'.obj E)
    (u : ∀ E, E ⟶ D.obj E) (u' : ∀ E, E ⟶ D'.obj E)
    (theta : L ≅ D) (theta' : L' ≅ D') (e : L ⋙ R ≅ R ⋙ L')
    (htheta : ∀ E, eta E ≫ theta.hom.app E = u E)
    (htheta' : ∀ E, eta' E ≫ theta'.hom.app E = u' E)
    (he : ∀ E, R.map (eta E) ≫ e.hom.app E = eta' (R.obj E)) (E : A) :
    R.map (u E) ≫ (transportCompletionIso R theta theta' e).hom.app E = u' (R.obj E) := by
  dsimp only [transportCompletionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← htheta E, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, theta.hom_inv_id_app,
    Category.comp_id]
  rw [← Category.assoc, he E, htheta']

private theorem normalizedCompletionIso_unique
    {A : Type*} [Category A] {L D : A ⥤ A}
    (eta : ∀ E, E ⟶ L.obj E) (u : ∀ E, E ⟶ D.obj E)
    (theta : L ≅ D) (htheta : ∀ E, eta E ≫ theta.hom.app E = u E)
    (hinj : ∀ E Y, Function.Injective
      (fun f : L.obj E ⟶ L.obj Y ↦ eta E ≫ f))
    (theta' : L ≅ D) (htheta' : ∀ E, eta E ≫ theta'.hom.app E = u E) :
    theta' = theta := by
  apply Iso.ext
  apply NatTrans.ext
  funext E
  apply (cancel_mono (theta.inv.app E)).1
  apply hinj E E
  simp only [← Category.assoc, htheta, htheta']

private theorem normalizedRestrictionIso_unique
    {A B : Type*} [Category A] [Category B]
    {L D : A ⥤ A} {L' D' : B ⥤ B} (R : A ⥤ B)
    (eta : ∀ E, E ⟶ L.obj E) (eta' : ∀ E, E ⟶ L'.obj E)
    (u : ∀ E, E ⟶ D.obj E) (u' : ∀ E, E ⟶ D'.obj E)
    (theta : L ≅ D) (theta' : L' ≅ D') (e : L ⋙ R ≅ R ⋙ L')
    (htheta : ∀ E, eta E ≫ theta.hom.app E = u E)
    (htheta' : ∀ E, eta' E ≫ theta'.hom.app E = u' E)
    (he : ∀ E, R.map (eta E) ≫ e.hom.app E = eta' (R.obj E))
    (hinj : ∀ E Y, Function.Injective
      (fun f : L'.obj E ⟶ L'.obj Y ↦ eta' E ≫ f))
    (beta : D ⋙ R ≅ R ⋙ D')
    (hbeta : ∀ E, R.map (u E) ≫ beta.hom.app E = u' (R.obj E)) :
    beta = transportCompletionIso R theta theta' e := by
  let t := transportCompletionIso R theta theta' e
  have ht := transportCompletionIso_unit R eta eta' u u' theta theta' e
    htheta htheta' he
  apply Iso.ext
  apply NatTrans.ext
  funext E
  let xi := (e.app E).symm ≪≫ R.mapIso (theta.app E)
  have hxi : eta' (R.obj E) ≫ xi.hom = R.map (u E) := by
    change eta' (R.obj E) ≫ (e.inv.app E ≫ R.map (theta.hom.app E)) = R.map (u E)
    rw [← he E]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← R.map_comp, htheta E]
  apply (cancel_epi xi.hom).1
  apply (cancel_mono (theta'.inv.app (R.obj E))).1
  apply hinj (R.obj E) (R.obj E)
  simp only [← Category.assoc, hxi, hbeta E, ht E]


private theorem transportedUnit_natural
    {A : Type*} [Category A] {L D : A ⥤ A}
    (eta : ∀ E, E ⟶ L.obj E) (u : ∀ E, E ⟶ D.obj E)
    (theta : L ≅ D) (htheta : ∀ E, eta E ≫ theta.hom.app E = u E)
    (hnat : ∀ E E' (f : E ⟶ E'), eta E ≫ L.map f = f ≫ eta E')
    {E E' : A} (f : E ⟶ E') : u E ≫ D.map f = f ≫ u E' := by
  rw [← htheta E, Category.assoc, ← theta.hom.naturality,
    ← Category.assoc, hnat E E' f, Category.assoc, htheta E']

private theorem normalizedRestriction_coherence
    {A B C' : Type*} [Category A] [Category B] [Category C']
    {D : A ⥤ A} {D₁ : B ⥤ B} {D₂ : C' ⥤ C'}
    (u : ∀ E, E ⟶ D.obj E) (u₁ : ∀ E, E ⟶ D₁.obj E)
    (u₂ : ∀ E, E ⟶ D₂.obj E)
    (R₁ : A ⥤ B) (R₂ : A ⥤ C')
    (beta₁ : D ⋙ R₁ ≅ R₁ ⋙ D₁) (beta₂ : D ⋙ R₂ ≅ R₂ ⋙ D₂)
    (hbeta₁ : ∀ E, R₁.map (u E) ≫ beta₁.hom.app E = u₁ (R₁.obj E))
    (hnat₂ : ∀ E E' (f : E ⟶ E'), u₂ E ≫ D₂.map f = f ≫ u₂ E')
    (unique₂ : ∀ (beta : D ⋙ R₂ ≅ R₂ ⋙ D₂),
      (∀ E, R₂.map (u E) ≫ beta.hom.app E = u₂ (R₂.obj E)) → beta = beta₂)
    (F : B ⥤ C') (rho : R₁ ⋙ F ≅ R₂) (gamma : D₁ ⋙ F ≅ F ⋙ D₂)
    (hgamma : ∀ E, F.map (u₁ E) ≫ gamma.hom.app E = u₂ (F.obj E)) :
    Functor.whiskerRight beta₁.hom F ≫ Functor.whiskerLeft R₁ gamma.hom ≫
        Functor.whiskerRight rho.hom D₂ =
      Functor.whiskerLeft D rho.hom ≫ beta₂.hom := by
  let t : D ⋙ R₂ ≅ R₂ ⋙ D₂ :=
    Functor.isoWhiskerLeft D rho.symm ≪≫
      Functor.isoWhiskerRight beta₁ F ≪≫
        Functor.isoWhiskerLeft R₁ gamma ≪≫ Functor.isoWhiskerRight rho D₂
  have ht : ∀ E, R₂.map (u E) ≫ t.hom.app E = u₂ (R₂.obj E) := by
    intro E
    dsimp only [t, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← Category.assoc, rho.inv.naturality (u E)]
    dsimp only [Functor.comp_map]
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, hbeta₁ E]
    rw [← Category.assoc (F.map (u₁ (R₁.obj E))), hgamma (R₁.obj E)]
    have hn := hnat₂ _ _ (rho.hom.app E)
    dsimp only [Functor.comp_obj] at hn
    rw [hn]
    simp
  have h := unique₂ t ht
  rw [← h]
  apply NatTrans.ext
  funext E
  dsimp only [t, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp


set_option backward.isDefEq.respectTransparency false in
private theorem cech_empty_unit_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (b0 : Fin 0 → (O.obj ⋙ forget CommRingCat).sections) (E : ringedSiteDerived O) :
    IsIso (ringedCechCompletionUnit O (ringedExtendedCech O 0 b0).1
      (ringedExtendedCech O 0 b0).2 E) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app
      (DerivedCategory.Q.objPreimage E)) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
  let e := DerivedCategory.Q.objObjPreimageIso E
  have : IsIso (ringedDerivedHomUnit O E) := by
    dsimp only [ringedDerivedHomUnit]
    repeat' apply IsIso.comp_isIso'
    all_goals first | infer_instance | skip
    change IsIso ((derivedInternalHom J O).mapIso ((Iso.refl _).prod e)).hom
    infer_instance
  change IsIso (ringedCechCompletionUnit O (ringedSiteRingComplex O) (𝟙 _) E)
  simp only [ringedCechCompletionUnit, Functor.map_id, op_id]
  change IsIso (ringedDerivedHomUnit O E ≫ (derivedInternalHom J O).map (𝟙 _))
  infer_instance


variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
variable [∀ U : C, HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]

/-- The normalized Cech--Koszul comparison, with its slice comparisons and their coherence.
The source is the actual extended localization complex; the target is the total derived
inverse limit of the actual strict tensor tower. Units come from the degree-zero maps,
not from a choice of a triangulated filler. Natural isomorphisms are required to be uniquely
normalized by those units. This is also a specification of the comparisons on all further
slice restrictions: the coherence field applies to the derived restriction functor and
its canonical composition isomorphism, and more generally to every normalized comparison.
Source: Stacks Project, Tags 0A0A, 0941 and 08JB
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-limit). -/
structure RingedKoszulCechComparison where
  presentation : RingedKoszulLimitPresentation O r b
  theta : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅
    presentation.completion
  unit : ∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2 E ≫ theta.hom.app E = presentation.unit E
  theta_unique : ∀ theta' : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅
      presentation.completion,
    (∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
      (ringedExtendedCech O r b).2 E ≫ theta'.hom.app E = presentation.unit E) → theta' = theta
  slicePresentation : ∀ U : C, RingedKoszulLimitPresentation (O.over U) r
    (fun i ↦ ringedKoszulSliceSection O (b i) U)
  sliceTheta : ∀ U : C,
    ringedCechCompletionFunctor (O.over U)
      (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1 ≅
      (slicePresentation U).completion
  slice_unit : ∀ (U : C) E,
    ringedCechCompletionUnit (O.over U)
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 E ≫
      (sliceTheta U).hom.app E = (slicePresentation U).unit E
  sourceRestriction : ∀ U : C,
    ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ⋙ ringedDerivedRestriction O U ≅
      ringedDerivedRestriction O U ⋙ ringedCechCompletionFunctor (O.over U)
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
  targetRestriction : ∀ U : C,
    presentation.completion ⋙ ringedDerivedRestriction O U ≅
      ringedDerivedRestriction O U ⋙ (slicePresentation U).completion
  source_unit : ∀ (U : C) E,
    (ringedDerivedRestriction O U).map
        (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
          (ringedExtendedCech O r b).2 E) ≫ (sourceRestriction U).hom.app E =
      ringedCechCompletionUnit (O.over U)
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).2
        ((ringedDerivedRestriction O U).obj E)
  target_unit : ∀ (U : C) E,
    (ringedDerivedRestriction O U).map (presentation.unit E) ≫
      (targetRestriction U).hom.app E =
        (slicePresentation U).unit ((ringedDerivedRestriction O U).obj E)
  restriction_square : ∀ U : C,
    Functor.whiskerRight theta.hom (ringedDerivedRestriction O U) ≫
        (targetRestriction U).hom =
      (sourceRestriction U).hom ≫
        Functor.whiskerLeft (ringedDerivedRestriction O U) (sliceTheta U).hom
  target_unique : ∀ (U : C)
      (beta : presentation.completion ⋙ ringedDerivedRestriction O U ≅
        ringedDerivedRestriction O U ⋙ (slicePresentation U).completion),
    (∀ E, (ringedDerivedRestriction O U).map (presentation.unit E) ≫ beta.hom.app E =
      (slicePresentation U).unit ((ringedDerivedRestriction O U).obj E)) →
        beta = targetRestriction U
  target_coherence : ∀ (U V : C)
      (F : ringedSiteDerived (O.over U) ⥤ ringedSiteDerived (O.over V))
      (rho : ringedDerivedRestriction O U ⋙ F ≅ ringedDerivedRestriction O V)
      (gamma : (slicePresentation U).completion ⋙ F ≅ F ⋙ (slicePresentation V).completion),
    (∀ E, F.map ((slicePresentation U).unit E) ≫ gamma.hom.app E =
      (slicePresentation V).unit (F.obj E)) →
    Functor.whiskerRight (targetRestriction U).hom F ≫
        Functor.whiskerLeft (ringedDerivedRestriction O U) gamma.hom ≫
        Functor.whiskerRight rho.hom (slicePresentation V).completion =
      Functor.whiskerLeft presentation.completion rho.hom ≫ (targetRestriction V).hom
  furtherTarget : ∀ (U V : C) (f : V ⟶ U),
    (slicePresentation U).completion ⋙ ringedKoszulDerivedOverMap O f ≅
      ringedKoszulDerivedOverMap O f ⋙ (slicePresentation V).completion
  further_unit : ∀ (U V : C) (f : V ⟶ U) E,
    (ringedKoszulDerivedOverMap O f).map ((slicePresentation U).unit E) ≫
        (furtherTarget U V f).hom.app E =
      (slicePresentation V).unit ((ringedKoszulDerivedOverMap O f).obj E)
  further_coherence : ∀ (U V : C) (f : V ⟶ U),
    Functor.whiskerRight (targetRestriction U).hom (ringedKoszulDerivedOverMap O f) ≫
        Functor.whiskerLeft (ringedDerivedRestriction O U) (furtherTarget U V f).hom ≫
        Functor.whiskerRight (ringedKoszulDerivedOverComparison O f).hom
          (slicePresentation V).completion =
      Functor.whiskerLeft presentation.completion (ringedKoszulDerivedOverComparison O f).hom ≫
        (targetRestriction V).hom
  empty_identity : r = 0 → ∀ E, IsIso (presentation.unit E)

/-- The normalized comparison structure exists for the ringed extended Cech model.
Source: Stacks Project, Tags 0913, 0A0A, 0941 and 08JB
(blueprint: lem-weil-pbc-ringed-cech-koszul-comparison-existence).
Proof: construct the strict presentations and their unit-compatible Cech comparisons
on the site and all its slices. Conjugate unit-normalized source restriction by these
comparisons. Descend evaluation at one on K-injective representatives to obtain
naturality of the Cech unit, then transport it to the strict units. Unit cancellation
proves uniqueness of all normalized isomorphisms; apply it to a composite normalized
candidate to prove arbitrary restriction coherence and its canonical specialization.
For the empty list, evaluation at one and the K-injective replacement make the Cech
unit invertible, hence also the strict unit. These facts assemble every structure field. -/
theorem exists_ringed_koszul_cech_comparison :
    Nonempty (RingedKoszulCechComparison O r b) := by
  classical
  obtain ⟨D, theta, htheta⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  have hs (U : C) := exists_ringed_cech_koszul_comparison_on_site (O.over U) r
    (fun i ↦ ringedKoszulSliceSection O (b i) U)
  choose Ds thetaS hthetaS using hs
  obtain ⟨e, s, he, hs⟩ := exists_ringed_cech_completion_restriction O r b
  let L := ringedCechCompletionFunctor O (ringedExtendedCech O r b).1
  let eta := ringedCechCompletionUnit O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2
  let Ls (U : C) := ringedCechCompletionFunctor (O.over U)
    (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
  let etaS (U : C) := ringedCechCompletionUnit (O.over U)
    (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
    (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)).2
  let beta (U : C) := transportCompletionIso (ringedDerivedRestriction O U)
    theta (thetaS U) (e U)
  let gamma (U V : C) (f : V ⟶ U) :=
    transportCompletionIso (ringedKoszulDerivedOverMap O f)
      (thetaS U) (thetaS V) (s U V f)
  have hbeta (U : C) (E : ringedSiteDerived O) :
      (ringedDerivedRestriction O U).map (D.unit E) ≫ (beta U).hom.app E =
        (Ds U).unit ((ringedDerivedRestriction O U).obj E) :=
    transportCompletionIso_unit _ eta (etaS U) D.unit (Ds U).unit
      theta (thetaS U) (e U) htheta (hthetaS U) (he U) E
  have hgamma (U V : C) (f : V ⟶ U) (E : ringedSiteDerived (O.over U)) :
      (ringedKoszulDerivedOverMap O f).map ((Ds U).unit E) ≫
          (gamma U V f).hom.app E =
        (Ds V).unit ((ringedKoszulDerivedOverMap O f).obj E) :=
    transportCompletionIso_unit _ (etaS U) (etaS V) (Ds U).unit (Ds V).unit
      (thetaS U) (thetaS V) (s U V f) (hthetaS U) (hthetaS V) (hs U V f) E
  have huniq (U : C)
      (beta' : D.completion ⋙ ringedDerivedRestriction O U ≅
        ringedDerivedRestriction O U ⋙ (Ds U).completion)
      (hb : ∀ E, (ringedDerivedRestriction O U).map (D.unit E) ≫ beta'.hom.app E =
        (Ds U).unit ((ringedDerivedRestriction O U).obj E)) : beta' = beta U :=
    normalizedRestrictionIso_unique _ eta (etaS U) D.unit (Ds U).unit
      theta (thetaS U) (e U) htheta (hthetaS U) (he U)
      (ringed_cech_completion_unit_hom_injective (O.over U) r
        (fun i ↦ ringedKoszulSliceSection O (b i) U)) beta' hb
  have hnatS (U : C) (E E' : ringedSiteDerived (O.over U)) (f : E ⟶ E') :
      (Ds U).unit E ≫ (Ds U).completion.map f = f ≫ (Ds U).unit E' :=
    transportedUnit_natural (etaS U) (Ds U).unit (thetaS U) (hthetaS U)
      (completion_unit_natural (O.over U) _ _) f
  have hcoh (U V : C)
      (F : ringedSiteDerived (O.over U) ⥤ ringedSiteDerived (O.over V))
      (rho : ringedDerivedRestriction O U ⋙ F ≅ ringedDerivedRestriction O V)
      (g : (Ds U).completion ⋙ F ≅ F ⋙ (Ds V).completion)
      (hg : ∀ E, F.map ((Ds U).unit E) ≫ g.hom.app E = (Ds V).unit (F.obj E)) :
      Functor.whiskerRight (beta U).hom F ≫
          Functor.whiskerLeft (ringedDerivedRestriction O U) g.hom ≫
          Functor.whiskerRight rho.hom (Ds V).completion =
        Functor.whiskerLeft D.completion rho.hom ≫ (beta V).hom :=
    normalizedRestriction_coherence D.unit (Ds U).unit (Ds V).unit
      (ringedDerivedRestriction O U) (ringedDerivedRestriction O V)
      (beta U) (beta V) (hbeta U) (hnatS V) (huniq V) F rho g hg
  refine ⟨{
    presentation := D
    theta := theta
    unit := htheta
    theta_unique := normalizedCompletionIso_unique eta D.unit theta htheta
      (ringed_cech_completion_unit_hom_injective O r b)
    slicePresentation := Ds
    sliceTheta := thetaS
    slice_unit := hthetaS
    sourceRestriction := e
    targetRestriction := beta
    source_unit := he
    target_unit := hbeta
    restriction_square := ?_
    target_unique := huniq
    target_coherence := hcoh
    furtherTarget := gamma
    further_unit := hgamma
    further_coherence := fun U V f ↦ hcoh U V (ringedKoszulDerivedOverMap O f)
      (ringedKoszulDerivedOverComparison O f) (gamma U V f) (hgamma U V f)
    empty_identity := ?_ }⟩
  · intro U
    apply NatTrans.ext
    funext E
    dsimp only [beta, transportCompletionIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
  · intro hr E
    subst r
    have := cech_empty_unit_isIso O b E
    rw [← htheta E]
    infer_instance


/-- The augmented extended Cech complex is the filtered colimit and homotopy colimit of
its finite positive Koszul system; internal Hom from it is canonically the strict total
derived inverse limit of tensor with its finite duals. The supplied normalized comparison
is natural on the derived category, compatible with every representative and slice, and
is identity for the empty sequence under the constant-tower and unit identifications.

Source: Stacks Project, More on Algebra, Tag 0913; Cohomology on Sites, Tags 0A0A, 0941,
08JB; Derived Categories, Tag 0949
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-limit).

Proof:
1. Expand the positive factors in degrees zero and one. In degree q the summands are
   indexed by q-element subsets I, with differential given by insertion of j with sign
   (-1)^(number of earlier indices) times b_j^(m+1). The transition on I multiplies by
   the product t_I. Dualizing gives factors in degrees minus one and zero and maps (b_j,1).
   Evaluation identifies Hom(P_m,N) with the finite total tensor N tensor Q_m, naturally
   in both variables; the Hom differential gives the total-tensor sign.
2. Send the I-coordinate a at level m to a/t_I^(m+1), then sheafify. The fraction equivalence
   relation is precisely eventual equality in the diagram. This identifies the differential
   with alternating localization and the degree-zero projection with the augmentation.
3. Apply lem-pc-complex-hocolim-colimit to the canonical telescope map, and compose with
   the colimit isomorphism. Hom from this quasi-isomorphism into a functorial K-injective
   replacement I computes derived internal Hom (def-pur-derived-internal-hom).
4. Hom from the telescope is the fibre of 1-shift on the product of Hom(P_m,I).
   The finite split-perfect tensor theorem lem-weil-pbc-split-perfect-tensor-kinjective
   makes those complexes K-injective, and lem-pc-ringed-space-product-kinjective computes
   the derived product without exactness of products of sheaves. The ordinary Hom-cone
   sign identification gives the Roos fibre, with the degree-zero family sent to (0,(x)_m).
5. Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit. Resolve the strict tower by a
   K-injective tower with injective terms; its evaluations are K-injective. Comparison
   gives homotopy equivalences at each level and hence on their products. On injective
   towers the transitions split, so 1-shift is sectionwise surjective with inverse-limit
   kernel. The inverse limit is therefore quasi-isomorphic to the Roos fibre.
6. Each finite dual is K-flat by its finite filtration with finite free graded pieces.
   Thus replacing N by I gives a levelwise quasi-isomorphism of actual strict tensor
   towers. Localization and total right derived inverse limit give the asserted natural
   comparison on the derived category, including its representative independence.
7. The compatible positive projections dualize to the actual degree-zero units of the
   strict tensor tower. In the fibre they send x to (0,(x)_m), agreeing with the map obtained
   from the compatible maps into the K-injective tower resolution and its ordinary limit.
   Unit normalization uniquely specifies the natural comparison: both functors are the
   derived-completion reflector, so precomposition with its unit determines every map
   into a complete object. This also proves uniqueness of normalized restriction maps.
8. Restriction is exact and preserves K-injectives, products, finite totalizations and
   cones (lem-pur-site-restriction-module-adjunction-exact and
   lem-pur-kinjective-restrict-localized). Hence it restricts the actual Roos calculation
   to that on the slice. All maps agree after further restriction; alternatively use
   uniqueness of the normalized comparisons to obtain their composition coherence.
9. For the empty list the positive diagram is constant O[0], the dual is canonically
   O[0] by evaluation at one, and 1-shift on the product of I is split surjective by the
   recursion x_0=0, x_(m+1)=x_m-y_m. Its kernel is the diagonal I. The strict unit is thus
   an isomorphism, and the normalized comparison is identity under these identifications. -/
theorem ringed_cech_koszul_dual_limit :
    (∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) ∧
      ∃ t : CochainComplex.mappingCone
          (CochainComplex.telescopeColimitShift O (ringedKoszulDiagram O r b)) ⟶
            (ringedExtendedCech O r b).1,
        CochainComplex.mappingCone.inr _ ≫ t =
          CochainComplex.telescopeToColimit O (ringedKoszulDiagram O r b) ≫ alpha.hom ∧
        QuasiIso t) ∧
    (∀ m : ℕ, CochainComplex.IsAcyclicTensorKFlat ((ringedKoszulDualTower O r b).obj (op m))) ∧
    Nonempty (RingedKoszulCechComparison O r b) := by
  have halpha := exists_ringed_cech_koszul_colimit_iso O r b
  rcases halpha with ⟨alpha, halpha⟩
  have ht := CochainComplex.quasiIso_telescopeColimit O (ringedKoszulDiagram O r b)
  rcases ht with ⟨t0, ht0, _, hq⟩
  have hq' : QuasiIso (t0 ≫ alpha.hom) := quasiIso_comp t0 alpha.hom
  have hta : CochainComplex.mappingCone.inr _ ≫ (t0 ≫ alpha.hom) =
      CochainComplex.telescopeToColimit O (ringedKoszulDiagram O r b) ≫ alpha.hom := by
    rw [← Category.assoc, ht0]
  refine ⟨⟨alpha, halpha, t0 ≫ alpha.hom, hta, hq'⟩, ?_, ?_⟩
  · exact ringed_cech_koszul_dual_tower_isKFlat O r b
  · exact exists_ringed_koszul_cech_comparison O r b

end CategoryTheory
