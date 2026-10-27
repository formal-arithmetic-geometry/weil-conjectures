/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Paper.CoefficientDuality
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral

/-! # Descent of scalar dual maps to perfect derived objects -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open DerivedCategory DerivedCategory.PerfectScalar WeilConjectures Opposite
open scoped TensorProduct

namespace CochainComplex.PerfectDualScalar

section

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- The named scalar data satisfies all its recorded coherence equations. -/
private theorem transportNormalized : coherenceData.{u, u}.Normalized := by
  unfold coherenceData
  exact perfect_scalar_tensor_coherence_data.exists.choose_spec

/-- Perfectness as an existing object property. -/
private abbrev transportPerfectProperty (R : CommRingCat.{u}) : ObjectProperty (D.{u, u} R) :=
  IsPerfectRingComplex

/-- Closure of the perfect subcategory uses the recorded scalar coherence data. -/
private instance transportPerfectProperty_monoidal (R : CommRingCat.{u}) :
    (transportPerfectProperty R).IsMonoidal where
  prop_unit := coherenceData.{u, u}.unitPerfect R
  prop_tensor P Q hP hQ := coherenceData.{u, u}.tensorPerfect R P Q hP hQ

/-- Restrict the actual scalar functor to the full perfect source subcategory. -/
private noncomputable def transportPerfectFunctor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (transportPerfectProperty R).FullSubcategory ⥤ D.{u, u} S :=
  (transportPerfectProperty R).ι ⋙ B f

/-- The full perfect subcategory has the underlying associator.
Source: full monoidal subcategories (blueprint: lem-sf-perfect-scalar-monoidal-functor). -/
private theorem transportAssociator (R : CommRingCat.{u})
    (P Q Z : (transportPerfectProperty R).FullSubcategory) :
    ((α_ P Q Z).hom).hom = (α_ P.obj Q.obj Z.obj).hom := by
  rfl

/-- The full perfect subcategory has the underlying left unitor.
Source: full monoidal subcategories (blueprint: lem-sf-perfect-scalar-monoidal-functor). -/
private theorem transportLeftUnitor (R : CommRingCat.{u})
    (P : (transportPerfectProperty R).FullSubcategory) :
    ((λ_ P).inv).hom = (λ_ P.obj).inv := by
  rfl

/-- The canonical balanced tensor and unit maps form an oplax monoidal functor. -/
@[instance_reducible] private noncomputable def transportPerfectFunctorOplax
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (transportPerfectFunctor f).OplaxMonoidal where
  η := (coherenceData.{u, u}.unit f).hom
  δ P Q := (coherenceData.{u, u}.tensor f P.obj Q.obj P.property Q.property).hom
  δ_natural_left := by
    intro P Q a Z
    have hn := transportNormalized.{u}.1 f P.obj Z.obj Q.obj Z.obj
      P.property Z.property Q.property Z.property a.hom (𝟙 Z.obj)
    change _ ≫ (B.{u, u} f).map a.hom ▷ (B.{u, u} f).obj Z.obj =
      (B.{u, u} f).map (a.hom ▷ Z.obj) ≫ _
    rw [(B.{u, u} f).map_id, tensorHom_id, tensorHom_id] at hn
    exact hn.symm
  δ_natural_right := by
    intro P Q Z a
    have hn := transportNormalized.{u}.1 f Z.obj P.obj Z.obj Q.obj
      Z.property P.property Z.property Q.property (𝟙 Z.obj) a.hom
    change _ ≫ (B.{u, u} f).obj Z.obj ◁ (B.{u, u} f).map a.hom =
      (B.{u, u} f).map (Z.obj ◁ a.hom) ≫ _
    rw [(B.{u, u} f).map_id, id_tensorHom, id_tensorHom] at hn
    exact hn.symm
  oplax_associativity P Q Z := by
    have hn := transportNormalized.{u}.2.2.2.2.2.2.2.1 f P.obj Q.obj Z.obj
      P.property Q.property Z.property
    dsimp only [transportPerfectFunctor, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
    erw [transportAssociator]
    convert hn using 1 <;> rfl
  oplax_left_unitality P := by
    dsimp only [transportPerfectFunctor, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
    rw [transportLeftUnitor]
    have hu := transportNormalized.{u}.2.2.2.2.2.2.2.2.2.1 f P.obj P.property
    have hunit : (𝟙_ (transportPerfectProperty R).FullSubcategory).obj = 𝟙_ (D.{u, u} R) := rfl
    try simp_rw [hunit]
    apply (cancel_mono (λ_ ((B.{u, u} f).obj P.obj)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    have hu' := congrArg (fun t ↦ (B.{u, u} f).map (λ_ P.obj).inv ≫ t) hu
    simp only [← Functor.map_comp, Iso.inv_hom_id] at hu'
    convert hu'.symm using 1 <;> first | rfl | exact ((B f).map_id _).symm
  oplax_right_unitality P := by
    dsimp only [transportPerfectFunctor, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
    have hu := transportNormalized.{u}.2.2.2.2.2.2.2.2.2.2.1 f P.obj P.property
    have he : ((ρ_ P).inv).hom = (ρ_ P.obj).inv := rfl
    rw [he]
    have hunit : (𝟙_ (transportPerfectProperty R).FullSubcategory).obj = 𝟙_ (D.{u, u} R) := rfl
    try simp_rw [hunit]
    apply (cancel_mono (ρ_ ((B.{u, u} f).obj P.obj)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    have hu' := congrArg (fun t ↦ (B.{u, u} f).map (ρ_ P.obj).inv ≫ t) hu
    simp only [← Functor.map_comp, Iso.inv_hom_id] at hu'
    convert hu'.symm using 1 <;> first | rfl | exact ((B f).map_id _).symm

attribute [local instance] transportPerfectFunctorOplax

/-- Invertibility of the balanced maps yields the canonical strong tensor structure. -/
private noncomputable def transportPerfectFunctorCore {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (transportPerfectFunctor f).CoreMonoidal := by
  refine Functor.CoreMonoidal.mk' (coherenceData.{u, u}.unit f).symm
    (fun P Q ↦ (coherenceData.{u, u}.tensor f P.obj Q.obj P.property Q.property).symm)
    ?_ ?_ ?_ ?_ ?_
  · intro P Q a Z
    exact Functor.OplaxMonoidal.δ_natural_left (transportPerfectFunctor f) a Z
  · intro P Q Z a
    exact Functor.OplaxMonoidal.δ_natural_right (transportPerfectFunctor f) Z a
  · intro P Q Z
    exact Functor.OplaxMonoidal.oplax_associativity (transportPerfectFunctor f) P Q Z
  · intro P
    exact Functor.OplaxMonoidal.oplax_left_unitality (transportPerfectFunctor f) P
  · intro P
    exact Functor.OplaxMonoidal.oplax_right_unitality (transportPerfectFunctor f) P



end

private lemma transportDualPerfect
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R : CommRingCat.{u}} (P : D R) (hP : IsPerfectRingComplex P) :
    IsPerfectRingComplex ((ihom P).obj (𝟙_ (D R))) :=
  DerivedCategory.IsPerfect.ihom_unit hP

private noncomputable def derivedDeltaMap
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R) (hP : IsPerfectRingComplex P) :
    (B f).obj ((ihom P).obj (𝟙_ (D R))) ⟶
      (ihom ((B f).obj P)).obj (𝟙_ (D S)) :=
  MonoidalClosed.curry
    ((coherenceData.tensor f P ((ihom P).obj (𝟙_ (D R))) hP
      (transportDualPerfect P hP)).inv ≫
      (B f).map ((ihom.ev P).app (𝟙_ (D R))) ≫ (coherenceData.unit f).hom)

private lemma derivedDeltaMap_evaluation
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R) (hP : IsPerfectRingComplex P) :
    (B f).obj P ◁ derivedDeltaMap f P hP ≫
        (ihom.ev ((B f).obj P)).app (𝟙_ (D S)) =
      (coherenceData.tensor f P ((ihom P).obj (𝟙_ (D R))) hP
        (transportDualPerfect P hP)).inv ≫
        (B f).map ((ihom.ev P).app (𝟙_ (D R))) ≫ (coherenceData.unit f).hom := by
  exact MonoidalClosed.uncurry_curry _

private lemma derivedDeltaMap_isIso
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R) (hP : IsPerfectRingComplex P) :
    IsIso (derivedDeltaMap f P hP) := by
  let DP := (ihom P).obj (𝟙_ (D R))
  let PP : (transportPerfectProperty R).FullSubcategory := ⟨P, hP⟩
  let DD : (transportPerfectProperty R).FullSubcategory :=
    ⟨DP, transportDualPerfect P hP⟩
  let := DerivedCategory.IsPerfect.isIso_ihomUnitTensorToIhom hP P
  let : ExactPairing DP P := MonoidalClosed.exactPairingOfIsIso P
  let : ExactPairing DD PP :=
    { coevaluation' := ObjectProperty.homMk (η_ DP P)
      evaluation' := ObjectProperty.homMk (ε_ DP P)
      coevaluation_evaluation' := by
        apply ObjectProperty.hom_ext
        exact ExactPairing.coevaluation_evaluation DP P
      evaluation_coevaluation' := by
        apply ObjectProperty.hom_ext
        exact ExactPairing.evaluation_coevaluation DP P }
  let := (transportPerfectFunctorCore f).toMonoidal
  let := ExactPairing.map (transportPerfectFunctor f) DD PP
  have hi := MonoidalClosed.isIso_curry_evaluation
    ((transportPerfectFunctor f).obj DD) ((transportPerfectFunctor f).obj PP)
  have he : derivedDeltaMap f P hP =
      MonoidalClosed.curry (ε_ ((transportPerfectFunctor f).obj DD)
        ((transportPerfectFunctor f).obj PP)) := by
    apply congrArg MonoidalClosed.curry
    change _ = Functor.LaxMonoidal.μ (transportPerfectFunctor f) PP DD ≫
      (B f).map ((ihom.ev P).app (𝟙_ (D R))) ≫
        Functor.OplaxMonoidal.η (transportPerfectFunctor f)
    have hμ : Functor.LaxMonoidal.μ (transportPerfectFunctor f) PP DD =
        (coherenceData.tensor f P DP hP (transportDualPerfect P hP)).inv := by
      rfl
    have hη : Functor.OplaxMonoidal.η (transportPerfectFunctor f) =
        (coherenceData.unit f).hom := by
      rfl
    rw [hμ, hη]
  rw [he]
  exact hi

private lemma transportModelMap_naturality
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (v : P ⟶ Q) :
    (B f).map (DerivedCategory.Q.map v) ≫ modelMap f Q =
      modelMap f P ≫ DerivedCategory.Q.map ((E f).map v) := by
  unfold modelMap
  unfold B at *
  let F := (ModuleCat.mixedTensor f.hom).flip
  let unit : (ModuleCat.mixedTensor f.hom).obj (ModuleCat.of S S) ≅
      ModuleCat.extendScalars f.hom :=
    isoWhiskerLeft (ModuleCat.extendScalars f.hom) (leftUnitorNatIso (ModuleCat S)) ≪≫
      Functor.rightUnitor _
  let e (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
    mapBifunctorSingle₂Iso F (ModuleCat.of S S) K ≪≫
      (NatIso.mapHomologicalComplex unit (.up ℤ)).app K
  have he : HomologicalComplex.mapBifunctorMap v (𝟙 (coefficient S)) F (.up ℤ) ≫
        (e Q).hom = (e P).hom ≫ (E f).map v := by
    dsimp only [e, Iso.trans_hom]
    rw [← Category.assoc, mapBifunctorSingle₂Iso_hom_naturality]
    simp only [Category.assoc]
    exact congrArg (fun t ↦ (mapBifunctorSingle₂Iso F (ModuleCat.of S S) P).hom ≫ t)
      ((NatIso.mapHomologicalComplex unit (.up ℤ)).hom.naturality v)
  let τ := Classical.choose (Classical.choose_spec
    (exists_derivedTensor_second_factor_functor f.hom).2) (coefficient S)
  have hn := τ.naturality v
  change ((Classical.choose (exists_derivedTensor_second_factor_functor f.hom).2).obj
      (coefficient S)).map (DerivedCategory.Q.map v) ≫ τ.app Q =
    τ.app P ≫ DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap v (𝟙 (coefficient S)) F (.up ℤ)) at hn
  simp only [Category.assoc]
  change ((Classical.choose (exists_derivedTensor_second_factor_functor f.hom).2).obj
      (coefficient S)).map (DerivedCategory.Q.map v) ≫ τ.app Q ≫
      DerivedCategory.Q.map (e Q).hom =
    τ.app P ≫ DerivedCategory.Q.map (e P).hom ≫ DerivedCategory.Q.map ((E f).map v)
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [he]

private lemma transportDualTermZero (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) (h : IsZero (P.X (-j))) :
    IsZero ((moduleHomComplex P (coefficient R)).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.2
  refine ⟨fun z w ↦ ?_⟩
  apply (HomComplex.Cochain.toSingleEquiv (K := P)
    (X := ModuleCat.of R R) (show -j + j = 0 by omega)).injective
  exact h.eq_of_src _ _

private lemma transportDualBounds (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hlo : P.IsStrictlyGE a) (hhi : P.IsStrictlyLE b) :
    (moduleHomComplex P (coefficient R)).IsStrictlyGE (-b) ∧
      (moduleHomComplex P (coefficient R)).IsStrictlyLE (-a) := by
  constructor
  · apply ((moduleHomComplex P (coefficient R)).isStrictlyGE_iff (-b)).2
    intro j hj
    exact transportDualTermZero R P j ((P.isStrictlyLE_iff b).1 hhi (-j) (by omega))
  · apply ((moduleHomComplex P (coefficient R)).isStrictlyLE_iff (-a)).2
    intro j hj
    exact transportDualTermZero R P j ((P.isStrictlyGE_iff a).1 hlo (-j) (by omega))

private lemma transportQUnit_isIso
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (R : CommRingCat.{u}) :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R))) := by
  let := DerivedCategory.isIso_ε_Qh (ModuleCat R)
  change IsIso ((Functor.LaxMonoidal.ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map
    (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance

private lemma transportEvaluationModel
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hhi : P.IsStrictlyLE b) (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (ev : P ⊗ moduleHomComplex P (coefficient R) ⟶ coefficient R)
    (hev : ∀ (p j : ℤ) (x : P.X p)
      (z : (moduleHomComplex P (coefficient R)).X j),
      ev.f (p + j) (HomologicalComplex.ιTensorObj P
        (moduleHomComplex P (coefficient R)) p j (p + j) rfl (x ⊗ₜ[R] z)) =
        (p * j).negOnePow • (z.v p (p + j) rfl) x) :
    ∃ k : DerivedCategory.Q.obj (moduleHomComplex P (coefficient R)) ≅
        (ihom (DerivedCategory.Q.obj P)).obj (𝟙_ (D R)),
      Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P (coefficient R)) ≫
          DerivedCategory.Q.map ev =
        DerivedCategory.Q.obj P ◁ k.hom ≫
          (ihom.ev (DerivedCategory.Q.obj P)).app (𝟙_ (D R)) ≫
            Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R)) := by
  obtain ⟨H, ev₀, hH, he₀, e, he, hn⟩ := projective_hom_evaluation_model R
  have hv : ev = ev₀ P (coefficient R) := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p j h
    subst n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x z
    exact (hev p j x z).trans (he₀ P (coefficient R) p j x z).symm
  let hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨b, (P.isStrictlyLE_iff b).1 hhi⟩
  let := transportQUnit_isIso R
  let k := e P hb hp (coefficient R) ≪≫
    (ihom (DerivedCategory.Q.obj P)).mapIso
      (asIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R)))).symm
  refine ⟨k, ?_⟩
  clear H hH hn he₀
  rw [hv, (he P hb hp (coefficient R)).2]
  simp only [k, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [ihom.ev_naturality_assoc]
  simp

private lemma transport_tensor_inv_natural
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q P' Q' : D R)
    (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q)
    (hP' : IsPerfectRingComplex P') (hQ' : IsPerfectRingComplex Q')
    (a : P ⟶ P') (b : Q ⟶ Q') :
    ((B f).map a ⊗ₘ (B f).map b) ≫ (coherenceData.tensor f P' Q' hP' hQ').inv =
      (coherenceData.tensor f P Q hP hQ).inv ≫ (B f).map (a ⊗ₘ b) := by
  apply (cancel_epi (coherenceData.tensor f P Q hP hQ).hom).1
  rw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc,
    ← transportNormalized.1 f P Q P' Q' hP hQ hP' hQ' a b]
  simp

private lemma derivedDeltaMap_naturality
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D R)
    (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q) (v : P ⟶ Q) :
    (B f).map ((MonoidalClosed.pre v).app (𝟙_ (D R))) ≫ derivedDeltaMap f P hP =
      derivedDeltaMap f Q hQ ≫
        (MonoidalClosed.pre ((B f).map v)).app (𝟙_ (D S)) := by
  apply MonoidalClosed.uncurry_injective
  dsimp only [derivedDeltaMap]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  have hr := transport_tensor_inv_natural f P ((ihom Q).obj (𝟙_ (D R)))
    P ((ihom P).obj (𝟙_ (D R))) hP (transportDualPerfect Q hQ)
    hP (transportDualPerfect P hP) (𝟙 P)
    ((MonoidalClosed.pre v).app (𝟙_ (D R)))
  have hl := transport_tensor_inv_natural f P ((ihom Q).obj (𝟙_ (D R)))
    Q ((ihom Q).obj (𝟙_ (D R))) hP (transportDualPerfect Q hQ)
    hQ (transportDualPerfect Q hQ) v (𝟙 _)
  rw [(B f).map_id] at hr hl
  simp only [id_tensorHom, tensorHom_id] at hr hl
  simp only [← Category.assoc]
  rw [hr, hl]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [MonoidalClosed.id_tensor_pre_app_comp_ev]

private lemma derivedDeltaMap_identity
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (R : CommRingCat.{u}) (P : D R) (hP : IsPerfectRingComplex P) :
    derivedDeltaMap (𝟙 R) P hP =
      (coherenceData.identity R ((ihom P).obj (𝟙_ (D R)))
        (transportDualPerfect P hP)).hom ≫
        (MonoidalClosed.pre (coherenceData.identity R P hP).hom).app (𝟙_ (D R)) := by
  apply MonoidalClosed.uncurry_injective
  dsimp only [derivedDeltaMap]
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_eq]
  have hin := transportNormalized.{u}.2.2.1
  have hit := transportNormalized.{u}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hiu := transportNormalized.{u}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [hiu]
  rw [hin R _ _ (coherenceData.tensorPerfect R P _ hP
    (transportDualPerfect P hP)) (coherenceData.unitPerfect R)
    ((ihom.ev P).app (𝟙_ (D R)))]
  rw [← hit R P _ hP (transportDualPerfect P hP)]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]

private lemma derivedDeltaMap_comp
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (P : D R) (hP : IsPerfectRingComplex P) :
    (B g).map (derivedDeltaMap f P hP) ≫
        derivedDeltaMap g ((B f).obj P) (coherenceData.preserves f P hP) =
      (coherenceData.comp f g ((ihom P).obj (𝟙_ (D R)))
        (transportDualPerfect P hP)).hom ≫
        derivedDeltaMap (f ≫ g) P hP ≫
        (MonoidalClosed.pre (coherenceData.comp f g P hP).hom).app (𝟙_ (D T)) := by
  let DP := (ihom P).obj (𝟙_ (D R))
  have hD : IsPerfectRingComplex DP := transportDualPerfect P hP
  have hPf := coherenceData.preserves f P hP
  have hDf := coherenceData.preserves f DP hD
  have hcn := transportNormalized.{u}.2.1 (R := R) (S := S) (T := T)
  have hct := transportNormalized.{u}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := R) (S := S) (T := T)
  have hcu := transportNormalized.{u}.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := R) (S := S) (T := T)
  have ht := congrArg
    (fun w ↦ (coherenceData.tensor g ((B f).obj P) ((B f).obj DP) hPf hDf).inv ≫
      (B g).map (coherenceData.tensor f P DP hP hD).inv ≫ w ≫
        (coherenceData.tensor (f ≫ g) P DP hP hD).inv)
    (hct f g P DP hP hD)
  simp only [Category.assoc,
    ← (B g).map_comp_assoc, Iso.inv_hom_id, (B g).map_id, Category.id_comp] at ht
  simp only [Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at ht
  have he := hcn f g (P ⊗ DP) (𝟙_ (D R))
    (coherenceData.tensorPerfect R P DP hP hD) (coherenceData.unitPerfect R)
    ((ihom.ev P).app (𝟙_ (D R)))
  have hu := hcu f g
  clear hct hcn hcu
  have hd := derivedDeltaMap_evaluation f P hP
  have hnat := transport_tensor_inv_natural g ((B f).obj P) ((B f).obj DP)
    ((B f).obj P) ((ihom ((B f).obj P)).obj (𝟙_ (D S))) hPf hDf hPf
    (transportDualPerfect _ hPf) (𝟙 _) (derivedDeltaMap f P hP)
  rw [(B g).map_id] at hnat
  simp only [id_tensorHom] at hnat
  apply MonoidalClosed.uncurry_injective
  simp only [← Category.assoc]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_natural_left]
  change (B g).obj ((B f).obj P) ◁ (B g).map (derivedDeltaMap f P hP) ≫
      (B g).obj ((B f).obj P) ◁ derivedDeltaMap g ((B f).obj P) hPf ≫
        (ihom.ev ((B g).obj ((B f).obj P))).app (𝟙_ (D T)) = _
  rw [derivedDeltaMap_evaluation]
  simp only [← Category.assoc]
  rw [hnat]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hd]
  rw [show MonoidalClosed.uncurry (derivedDeltaMap (f ≫ g) P hP) =
      (coherenceData.tensor (f ≫ g) P DP hP hD).inv ≫
        (B (f ≫ g)).map ((ihom.ev P).app (𝟙_ (D R))) ≫
          (coherenceData.unit (f ≫ g)).hom from MonoidalClosed.uncurry_curry _]
  rw [← tensorHom_def_assoc]
  simp only [← Category.assoc]
  rw [← ht]
  simp only [Category.assoc, Functor.map_comp]
  rw [← hu, reassoc_of% he]

private lemma transportModelSquare
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hlo : P.IsStrictlyGE a) (hhi : P.IsStrictlyLE b)
    (ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
    (hDterms : ∀ n : ℤ, Module.Projective R
      ((moduleHomComplex P (coefficient R)).X n) ∧
      Module.Finite R ((moduleHomComplex P (coefficient R)).X n))
    (hP : IsPerfectRingComplex (DerivedCategory.Q.obj P))
    (evR : P ⊗ moduleHomComplex P (coefficient R) ⟶ coefficient R)
    (evS : (E f).obj P ⊗ moduleHomComplex ((E f).obj P) (coefficient S) ⟶ coefficient S)
    (beta : (E f).obj (moduleHomComplex P (coefficient R)) ⟶
      moduleHomComplex ((E f).obj P) (coefficient S))
    (hev : ((ModuleCat.extendScalars f.hom).mapCochainComplexμIso P
        (moduleHomComplex P (coefficient R))).hom ≫
        (E f).map evR ≫ (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
      (E f).obj P ◁ beta ≫ evS)
    (k : DerivedCategory.Q.obj (moduleHomComplex P (coefficient R)) ≅
      (ihom (DerivedCategory.Q.obj P)).obj (𝟙_ (D R)))
    (l : DerivedCategory.Q.obj (moduleHomComplex ((E f).obj P) (coefficient S)) ≅
      (ihom (DerivedCategory.Q.obj ((E f).obj P))).obj (𝟙_ (D S)))
    (hk : Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P (coefficient R)) ≫
        DerivedCategory.Q.map evR =
      DerivedCategory.Q.obj P ◁ k.hom ≫
        (ihom.ev (DerivedCategory.Q.obj P)).app (𝟙_ (D R)) ≫
          Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R)))
    (hl : Functor.LaxMonoidal.μ DerivedCategory.Q ((E f).obj P)
        (moduleHomComplex ((E f).obj P) (coefficient S)) ≫ DerivedCategory.Q.map evS =
      DerivedCategory.Q.obj ((E f).obj P) ◁ l.hom ≫
        (ihom.ev (DerivedCategory.Q.obj ((E f).obj P))).app (𝟙_ (D S)) ≫
          Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat S))) :
    (B f).map k.inv ≫ modelMap f (moduleHomComplex P (coefficient R)) ≫
      DerivedCategory.Q.map beta ≫ l.hom ≫
      (MonoidalClosed.pre (modelMap f P)).app (𝟙_ (D S)) =
        derivedDeltaMap f (DerivedCategory.Q.obj P) hP := by
  let := transportQUnit_isIso S
  let DP := moduleHomComplex P (coefficient R)
  have hd := transportDualBounds R P a b hlo hhi
  have hDP : IsPerfectRingComplex (DerivedCategory.Q.obj DP) :=
    ⟨DP, -b, -a, hd.1, hd.2, hDterms, ⟨Iso.refl _⟩⟩
  have htm := transportNormalized.{u}.2.2.2.1 (R := R) (S := S)
  have hum := transportNormalized.{u}.2.2.2.2.1 (R := R) (S := S)
  have htensor := htm f P DP a b (-b) (-a) hlo hhi hd.1 hd.2 ht hDterms hP hDP
  have htensor' := congrArg
    (fun w ↦ (coherenceData.tensor f (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj DP) hP hDP).inv ≫ w) htensor
  simp only [Iso.inv_hom_id_assoc] at htensor'
  have hunit := hum f
  clear htm hum htensor
  have hnat := transportModelMap_naturality f evR
  have he := congrArg DerivedCategory.Q.map hev
  simp only [Functor.map_comp] at he
  apply (cancel_epi ((B f).map k.hom)).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
  rw [(B f).map_id, Category.id_comp]
  apply MonoidalClosed.uncurry_injective
  simp only [← Category.assoc]
  rw [MonoidalClosed.uncurry_pre_app]
  simp only [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_eq]
  dsimp only [derivedDeltaMap]
  rw [MonoidalClosed.uncurry_curry]
  apply (cancel_mono (Functor.LaxMonoidal.ε
    (DerivedCategory.Q (C := ModuleCat S)))).1
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← hl]
  rw [← whisker_exchange_assoc]
  rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, Category.comp_id]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← he]
  simp only [← Category.assoc]
  rw [← htensor']
  dsimp only [DP]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp_assoc,
    Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hnat]
  simp only [← (B f).map_comp_assoc]
  rw [hk]
  simp only [(B f).map_comp, Category.assoc]
  have hunit' : (B f).map (Functor.LaxMonoidal.ε
      (DerivedCategory.Q (C := ModuleCat R))) ≫ modelMap f (coefficient R) ≫
      DerivedCategory.Q.map (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
      (coherenceData.unit f).hom ≫ Functor.LaxMonoidal.ε
        (DerivedCategory.Q (C := ModuleCat S)) := by
    exact hunit
  rw [hunit']
  have hkn := transport_tensor_inv_natural f (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj (moduleHomComplex P (coefficient R)))
    (DerivedCategory.Q.obj P) ((ihom (DerivedCategory.Q.obj P)).obj (𝟙_ (D R)))
    hP hDP hP (transportDualPerfect _ hP) (𝟙 _) k.hom
  rw [(B f).map_id] at hkn
  simp only [id_tensorHom] at hkn
  rw [reassoc_of% hkn]

/-- Transport of signed scalar-dual comparisons to perfect derived objects.
Source: the coefficient-ring computation in the point-duality proof, Stacks Project
Tags 0A66 and 0FNG (blueprint: lem-pod-perfect-dual-derived-transport).

Proof: Define the comparison by currying scalar extension of derived evaluation,
using the inverse tensor comparison and the unit comparison. Perfect objects have
exact dual pairings. Restrict scalar extension to the full perfect subcategory;
the normalized tensor and unit comparisons make it monoidal, hence it preserves
these pairings and the curried comparison is invertible. Uncurrying reduces
naturality to naturality of the tensor comparison and evaluation. The normalized
identity and composition tensor/unit equations similarly prove identity and tower
compatibility. For a bounded finite-projective model, the projective Hom evaluation
model gives the two internal-Hom identifications. Its signed formula determines the
assumed evaluation, so the assumed chain evaluation square, the normalized tensor
and unit model equations, and naturality of modelMap prove the model square.
No choice of chain representatives and no flatness assumption on the map are needed. -/
theorem perfect_dual_derived_transport
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (ev : ∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ),
        P ⊗ (moduleHomComplex P (coefficient R)) ⟶ coefficient R)
    (beta : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
        (P : CochainComplex (ModuleCat.{u} R) ℤ),
        (E f).obj (moduleHomComplex P (coefficient R)) ⟶ (moduleHomComplex ((E f).obj P)
          (coefficient S)))
    (dualPerfect : ∀ (R : CommRingCat.{u}) (P : D.{u, u} R),
        IsPerfectRingComplex P → IsPerfectRingComplex ((coefficientDerivedDual R).obj (op P)))
    (hev : (∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)
          (p j : ℤ) (x : P.X p) (z : (moduleHomComplex P (coefficient R)).X j),
        (ev R P).f (p + j)
          (HomologicalComplex.ιTensorObj P (moduleHomComplex P (coefficient R)) p j (p + j) rfl
            (x ⊗ₜ[R] z)) =
            (p * j).negOnePow • (z.v p (p + j) rfl) x))
    (heval : (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : CochainComplex (ModuleCat.{u} R) ℤ),
        ((ModuleCat.extendScalars f.hom).mapCochainComplexμIso P (moduleHomComplex P (coefficient
          R))).hom ≫
            (E f).map (ev R P) ≫
            (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
          (E f).obj P ◁ beta f P ≫ ev S ((E f).obj P)))
    (scalarTerms : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
      (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)) →
      ∀ n : ℤ, Module.Projective S (((E f).obj P).X n) ∧
        Module.Finite S (((E f).obj P).X n))
    (dualTerms : ∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)) →
      ∀ n : ℤ, Module.Projective R ((moduleHomComplex P (coefficient R)).X n) ∧
        Module.Finite R ((moduleHomComplex P (coefficient R)).X n)) :
    ∃ delta : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, u} R),
        IsPerfectRingComplex P →
          ((B f).obj ((coefficientDerivedDual R).obj (op P)) ≅ ((coefficientDerivedDual S).obj
            (op ((B f).obj P)))),
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, u} R)
          (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q) (v : P ⟶ Q),
        (B f).map ((MonoidalClosed.pre v).app (𝟙_ (D R))) ≫ (delta f P hP).hom =
          (delta f Q hQ).hom ≫
            (MonoidalClosed.pre ((B f).map v)).app (𝟙_ (D S))) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
          (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
          (_ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
          (hP : IsPerfectRingComplex (DerivedCategory.Q.obj P)),
        ∃ (k : DerivedCategory.Q.obj (moduleHomComplex P (coefficient R)) ≅
            ((coefficientDerivedDual R).obj (op (DerivedCategory.Q.obj P))))
          (l : DerivedCategory.Q.obj (moduleHomComplex ((E f).obj P) (coefficient S)) ≅
            ((coefficientDerivedDual S).obj (op (DerivedCategory.Q.obj ((E f).obj P))))),
          (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P (coefficient R)) ≫
              DerivedCategory.Q.map (ev R P) =
            DerivedCategory.Q.obj P ◁ k.hom ≫
              (ihom.ev (DerivedCategory.Q.obj P)).app (𝟙_ (D R)) ≫
                Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R))) ∧
          (Functor.LaxMonoidal.μ DerivedCategory.Q ((E f).obj P)
              (moduleHomComplex ((E f).obj P) (coefficient S)) ≫ DerivedCategory.Q.map (ev S ((E
                f).obj P)) =
            DerivedCategory.Q.obj ((E f).obj P) ◁ l.hom ≫
              (ihom.ev (DerivedCategory.Q.obj ((E f).obj P))).app (𝟙_ (D S)) ≫
                Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat S))) ∧
          (B f).map k.inv ≫ modelMap f (moduleHomComplex P (coefficient R)) ≫
              DerivedCategory.Q.map (beta f P) ≫ l.hom ≫
              (MonoidalClosed.pre (modelMap f P)).app (𝟙_ (D S)) =
            (delta f (DerivedCategory.Q.obj P) hP).hom) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : D.{u, u} R) (hP : IsPerfectRingComplex P),
        (B f).map ((ihom.ev P).app (𝟙_ (D R))) ≫ (coherenceData.unit f).hom =
          (coherenceData.tensor f P ((coefficientDerivedDual R).obj (op P))
            hP (dualPerfect R P hP)).hom ≫
              (B f).obj P ◁ (delta f P hP).hom ≫
                (ihom.ev ((B f).obj P)).app (𝟙_ (D S))) ∧
      (∀ (R : CommRingCat.{u}) (P : D.{u, u} R) (hP : IsPerfectRingComplex P),
        (delta (𝟙 R) P hP).hom =
          (coherenceData.identity R ((coefficientDerivedDual R).obj (op P)) (dualPerfect R P
            hP)).hom ≫
            (MonoidalClosed.pre (coherenceData.identity R P hP).hom).app (𝟙_ (D R))) ∧
      (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
          (P : D.{u, u} R) (hP : IsPerfectRingComplex P),
        (B g).map (delta f P hP).hom ≫
            (delta g ((B f).obj P) (coherenceData.preserves f P hP)).hom =
          (coherenceData.comp f g ((coefficientDerivedDual R).obj (op P)) (dualPerfect R P
            hP)).hom ≫
            (delta (f ≫ g) P hP).hom ≫
            (MonoidalClosed.pre (coherenceData.comp f g P hP).hom).app (𝟙_ (D T))) := by
  classical
  let delta {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D R)
      (hP : IsPerfectRingComplex P) :
      (B f).obj ((coefficientDerivedDual R).obj (op P)) ≅
        (coefficientDerivedDual S).obj (op ((B f).obj P)) := by
    haveI := derivedDeltaMap_isIso f P hP
    exact asIso (derivedDeltaMap f P hP)
  refine ⟨delta, ?_, ?_, ?_, ?_, ?_⟩
  · intro R S f P Q hP hQ v
    exact derivedDeltaMap_naturality f P Q hP hQ v
  · intro R S f P a b hlo hhi ht hP
    have hEPhi : CochainComplex.IsStrictlyLE ((E f).obj P) b := by
      let := hhi
      infer_instance
    obtain ⟨k, hk⟩ := transportEvaluationModel R P b hhi
      (fun n ↦ (ht n).1) (ev R P) (hev R P)
    obtain ⟨l, hl⟩ := transportEvaluationModel S ((E f).obj P) b hEPhi
      (fun n ↦ (scalarTerms f P ht n).1) (ev S ((E f).obj P)) (hev S ((E f).obj P))
    refine ⟨k, l, hk, hl, ?_⟩
    exact transportModelSquare f P a b hlo hhi ht (dualTerms R P ht) hP
      (ev R P) (ev S ((E f).obj P)) (beta f P) (heval f P) k l hk hl
  · intro R S f P hP
    change _ = (coherenceData.tensor f P ((ihom P).obj (𝟙_ (D R))) hP
      (transportDualPerfect P hP)).hom ≫
      (B f).obj P ◁ derivedDeltaMap f P hP ≫ _
    rw [derivedDeltaMap_evaluation]
    simp
  · intro R P hP
    exact derivedDeltaMap_identity R P hP
  · intro R S T f g P hP
    exact derivedDeltaMap_comp f g P hP

end CochainComplex.PerfectDualScalar
