/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.PointProjectiveDualTensorModels
public import Sheaf.Paper.PointFibreDerivedTensorModels
import Sheaf.Paper.PointHomComplexAdjunction
import Sheaf.Paper.PointSheafHomMaps
import all Sheaf.SecSmoothPurity.CochainInverseComparison
import Sheaf.Paper.ModuleHomSignedEvaluation

/-! # Ordinary evaluation on normalized perfect point models

Source: blueprint point-dualizing proof, second sentence; Stacks 0A8X and 08J7.
(blueprint: lem-pod-point-perfect-ordinary-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction PresheafOfModules.sheafification
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings
open WeilConjectures.PointProjectiveDualTensorModels
namespace WeilConjectures.PointPerfectOrdinaryEvaluation

private def homPost {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    {V W : CochainComplex (ModuleCat.{u} A) ℤ} (e : V ≅ W) :
    CochainComplex.moduleHomComplex P V ≅ CochainComplex.moduleHomComplex P W := by
  let f (j : ℤ) : (CochainComplex.moduleHomComplex P V).X j ≃ₗ[A]
      (CochainComplex.moduleHomComplex P W).X j :=
    { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom e.hom) (add_zero j)
      invFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom e.inv) (add_zero j)
      left_inv := by
        intro z
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc,
          ← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f,
          Category.comp_id]
      right_inv := by
        intro z
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc,
          ← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f,
          Category.comp_id]
      map_add' := fun z w ↦ CochainComplex.HomComplex.Cochain.add_comp z w _ _
      map_smul' := fun a z ↦ CochainComplex.HomComplex.Cochain.smul_comp a z _ _ }
  exact HomologicalComplex.Hom.isoOfComponents (fun j ↦ (f j).toModuleIso) (by
    intro i j _
    apply ModuleCat.hom_ext
    ext z
    exact CochainComplex.HomComplex.δ_comp_ofHom z e.hom j)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Termwise extension, with the given additive law.
Source: Stacks 0A8X (blueprint: lem-pod-point-perfect-ordinary-evaluation). -/
abbrev ordinaryModel
    (L : ModuleCat.{u + 1} (R l E) ⥤ Modules D l E) [L.Additive]
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  (L.mapHomologicalComplex (.up ℤ)).obj P

/-- The six explicit unit, Hom and ordinary evaluation formulas, grouped unchanged.
Source: parent proof step 3 (blueprint: lem-pod-point-perfect-ordinary-evaluation). -/
@[irreducible] def Normalized
    (L : ModuleCat.{u + 1} (R l E) ⥤ Modules D l E) [hL : L.Additive]
    (hobj : ∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u}
      D.k (B D l E) (alpha D l E) M)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (unit : P ≅ (pointIntegralComplexSections D l E).obj (ordinaryModel D l E L P))
    (homIso : ordinaryModel D l E L (dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (B D l E)
        (ordinaryModel D l E L P) (coefficient D l E))
    (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E))
    (q : (pointIntegralComplexSections D l E).obj (ordinaryModel D l E L (dual l E P)) ≅ dual l E P)
    (evaluation : PointDerivedHom.total.{u, u} D.k (B D l E) (ordinaryModel D l E L P)
    (ordinaryModel D l E L (dual l E P)) ⟶ coefficient D l E)
    (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E) : Prop :=
  (∀ (p : ℤ) (x : P.X p), (unit.hom.f p).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
        (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x) ∧
  (∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
    (sheafValue D l E (p + j) h).val.app U
      (PointDerivedHom.homValue.{u, u} D.k (B D l E) (ordinaryModel D l E L P) (coefficient D l E)
        j p U ((homIso.hom.f j).val.app U
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E)
            L hobj ((dual l E P).X j) U b f))
        (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p) U b' x)) =
      b * b' * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
        ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))) ∧
  (∀ x : (ringComplex l E).X 0,
    (sheafValue D l E 0 rfl).val.app (op (PointDerivedHom.finalObject D.k))
      ((coefficientUnit.hom.f 0).hom x) =
        pointIntegralSectionMap l E D.k ((moduleValue l E 0 rfl).hom x)) ∧
  (∀ (p j : ℤ) (h : p + j = 0)
      (f : ((pointIntegralComplexSections D l E).obj
        (ordinaryModel D l E L (dual l E P))).X j) (x : P.X p),
    pointIntegralSectionMap l E D.k
      ((moduleValue l E (p + j) h).hom ((((q.hom.f j).hom f).v p (p + j) rfl).hom x)) =
      (sheafValue D l E (p + j) h).val.app (op (PointDerivedHom.finalObject D.k))
        (PointDerivedHom.homValue.{u, u} D.k (B D l E) (ordinaryModel D l E L P) (coefficient D l E)
          j p (op (PointDerivedHom.finalObject D.k))
          ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f)
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p)
            (op (PointDerivedHom.finalObject D.k)) 1 x))) ∧
  (∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (x : P.X p) (f : (dual l E P).X j),
    (sheafValue D l E (p + j) h).val.app U
      ((evaluation.f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
          (ordinaryModel D l E L P) (ordinaryModel D l E L (dual l E P)) p j U
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p) U b x)
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E)
            L hobj ((dual l E P).X j) U b' f))) =
      (p * j).negOnePow • (b * b' *
        PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
          ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)))) ∧
  (∀ (p j : ℤ) (h : p + j = 0) (x : P.X p)
      (f : (dual l E P).X j),
    (moduleValue l E (p + j) h).hom ((ringEvaluation.f (p + j)).hom
      ((HomologicalComplex.ιTensorObj P (dual l E P) p j (p + j) rfl).hom
        (x ⊗ₜ[R l E] f))) =
        (p * j).negOnePow •
          (moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))

/-- Ordinary evaluation through the normalized finite-projective Hom identification.
Source: point-completed-evaluation proof step 3; Stacks 0A8X, 08J7
(blueprint: lem-pod-point-perfect-ordinary-evaluation).

Proof: the bijective scalar map identifies the coefficient complex's sections with R[0].
Apply the Hom-complex adjunction to P and B[0], and postcompose each cochain with
this coefficient isomorphism's inverse. Composing with sections of homIso gives q.
Its component formula is evaluation on the unit 1 tensor x. Compose ordinary signed
sheaf evaluation with 1 tensor homIso to define evaluation; define ringEvaluation
by the module signed evaluation construction. Their formulas on bidegree (p,j)
have the common sign (-1)^(pj), also in negative degrees. To prove the square for
any beta with the displayed formula, precompose with each total summand and each
pure module tensor. If p+j=0, use the normalization of q and the coefficient unit;
otherwise the target single complex is zero. Tensor and coproduct extensionality
then prove equality of chain maps. This assertion uses no completion or Roos model. -/
theorem point_perfect_ordinary_evaluation
    (L : ModuleCat.{u + 1} (R l E) ⥤ Modules D l E)
    (hobj : ∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u}
      D.k (B D l E) (alpha D l E) M)
    (adj : L ⊣ PointDerivedHom.sections.{u, u} D.k (B D l E) (alpha D l E))
    (hex : PointDerivedHom.ExplicitAdjunction.{u, u} D.k (B D l E) (alpha D l E) L hobj adj)
    (hscalar : Function.Bijective (pointIntegralSectionMap l E D.k))
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (unit : P ≅ (pointIntegralComplexSections D l E).obj (model D l E L adj P))
    (hunit : ∀ (p : ℤ) (x : P.X p), (unit.hom.f p).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
        (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x)
    (homIso : model D l E L adj (dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (B D l E)
        (model D l E L adj P) (coefficient D l E))
    (hhom : ∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
    (sheafValue D l E (p + j) h).val.app U
      (PointDerivedHom.homValue.{u, u} D.k (B D l E) (model D l E L adj P) (coefficient D l E)
        j p U ((homIso.hom.f j).val.app U
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E)
            L hobj ((dual l E P).X j) U b f))
        (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj (P.X p) U b' x)) =
      b * b' * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
        ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))) :
  letI := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  letI := adj.left_adjoint_additive
  ∃ (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E)),
  ∃ (q : (pointIntegralComplexSections D l E).obj (model D l E L adj (dual l E P)) ≅ dual l E P),
  ∃ (evaluation : PointDerivedHom.total.{u, u} D.k (B D l E) (model D l E L adj P)
    (model D l E L adj (dual l E P)) ⟶ coefficient D l E),
  ∃ (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E),
    Normalized D l E L hobj P unit homIso coefficientUnit q evaluation ringEvaluation ∧
    ∀ (beta : P ⊗ (pointIntegralComplexSections D l E).obj
        (model D l E L adj (dual l E P)) ⟶
      (pointIntegralComplexSections D l E).obj
        (PointDerivedHom.total.{u, u} D.k (B D l E) (model D l E L adj P)
          (model D l E L adj (dual l E P)))),
      (∀ (p j : ℤ) (x : P.X p)
        (f : ((pointIntegralComplexSections D l E).obj
          (model D l E L adj (dual l E P))).X j),
        (beta.f (p + j)).hom
          ((HomologicalComplex.ιTensorObj P ((pointIntegralComplexSections D l E).obj
            (model D l E L adj (dual l E P))) p j (p + j) rfl).hom (x ⊗ₜ[R l E] f)) =
        PointDerivedHom.totalElement.{u, u} D.k (B D l E) (model D l E L adj P)
          (model D l E L adj (dual l E P)) p j (op (PointDerivedHom.finalObject D.k))
            ((unit.hom.f p).hom x) f) →
      beta ≫ (pointIntegralComplexSections D l E).map evaluation ≫ coefficientUnit.inv =
        (MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 P) q.hom) ≫ ringEvaluation := by
  let := PointDerivedHom.sections_additive.{u, u} D.k (B D l E) (alpha D l E)
  let := adj.left_adjoint_additive
  have hcoefIso : IsIso (PointDerivedHom.coefficientSections.{u, u} D.k
      (B D l E) (alpha D l E)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hscalar
  let F := PointDerivedHom.sections.{u, u} D.k (B D l E) (alpha D l E)
  let coeffUnit : ringComplex l E ≅
      (pointIntegralComplexSections D l E).obj (coefficient D l E) :=
    (CochainComplex.singleFunctor _ 0).mapIso
      (asIso (PointDerivedHom.coefficientSections.{u, u} D.k (B D l E) (alpha D l E))) ≪≫
        (F.mapCochainComplexSingleFunctor 0).symm.app _
  obtain ⟨hcomp, hhcomp⟩ := PointDerivedHom.point_hom_complex_adjunction.{u, u}
    D.k (B D l E) (alpha D l E) L hobj adj P (coefficient D l E) hex
  let q := (pointIntegralComplexSections D l E).mapIso homIso ≪≫ hcomp ≪≫
    homPost P coeffUnit.symm
  obtain ⟨eB, _, heB, _⟩ := PointDerivedHom.point_sheaf_hom_maps.{u, u}
    D.k (B D l E) (alpha D l E) L hobj adj P hex (coefficient D l E)
  let evaluation : PointDerivedHom.total.{u, u} D.k (B D l E)
      (model D l E L adj P) (model D l E L adj (dual l E P)) ⟶ coefficient D l E :=
    ((IntegralHom.totalTensor.{u, u} (Spec (.of D.k)) (B D l E)).obj
      (model D l E L adj P)).map homIso.hom ≫ eB
  obtain ⟨ringEval, hringEval⟩ := CochainComplex.module_hom_signed_evaluation P (ringComplex l E)
  have hcoeff (x : (ringComplex l E).X 0) :
      (sheafValue D l E 0 rfl).val.app (op (PointDerivedHom.finalObject D.k))
        ((coeffUnit.hom.f 0).hom x) =
      pointIntegralSectionMap l E D.k ((moduleValue l E 0 rfl).hom x) := by
    dsimp only [coeffUnit, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
    simp only [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor]
    rfl
  have hcoeffinv (n : ℤ) (hn : n = 0)
      (y : ((pointIntegralComplexSections D l E).obj (coefficient D l E)).X n) :
      pointIntegralSectionMap l E D.k
        ((moduleValue l E n hn).hom ((coeffUnit.inv.f n).hom y)) =
      (sheafValue D l E n hn).val.app (op (PointDerivedHom.finalObject D.k)) y := by
    subst n
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom coeffUnit.inv_hom_id 0) y
    change (coeffUnit.hom.f 0).hom ((coeffUnit.inv.f 0).hom y) = y at hi
    exact (hcoeff _).symm.trans (congrArg
      ((sheafValue D l E 0 rfl).val.app (op (PointDerivedHom.finalObject D.k))) hi)
  have hq (p j : ℤ) (hpj : p + j = 0)
      (f : ((pointIntegralComplexSections D l E).obj (model D l E L adj (dual l E P))).X j)
      (x : P.X p) :
      pointIntegralSectionMap l E D.k
        ((moduleValue l E (p + j) hpj).hom ((((q.hom.f j).hom f).v p (p + j) rfl).hom x)) =
      (sheafValue D l E (p + j) hpj).val.app (op (PointDerivedHom.finalObject D.k))
        (PointDerivedHom.homValue.{u, u} D.k (B D l E) (model D l E L adj P)
          (coefficient D l E) j p (op (PointDerivedHom.finalObject D.k))
          ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f)
          (PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) L hobj
            (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x)) := by
    change pointIntegralSectionMap l E D.k
      ((moduleValue l E (p + j) hpj).hom ((coeffUnit.inv.f (p + j)).hom
        ((((hcomp.hom.f j).hom
          ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f)).v
            p (p + j) rfl).hom x))) = _
    rw [hcoeffinv]
    exact congrArg
      ((sheafValue D l E (p + j) hpj).val.app (op (PointDerivedHom.finalObject D.k)))
      (hhcomp j p ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f) x)
  have heval (p j : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (x : ((model D l E L adj P).X p).val.obj U)
      (f : ((model D l E L adj (dual l E P)).X j).val.obj U) :
      (evaluation.f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
          (model D l E L adj P) (model D l E L adj (dual l E P)) p j U x f) =
      (p * j).negOnePow • PointDerivedHom.homValue.{u, u} D.k (B D l E)
        (model D l E L adj P) (coefficient D l E) j p U
          ((homIso.hom.f j).val.app U f) x := by
    let : EssentiallySmall.{u + 1} (Spec (.of D.k)).ProEt := essentiallySmallSelf.{0} _
    let := IntegralHom.tensorLocalization.{u, u} (Spec (.of D.k)) (B D l E)
    let : MonoidalCategory (Modules D l E) :=
      SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (B D l E)
    let := IntegralHom.countableColimits.{u, u} (Spec (.of D.k)) (B D l E)
    let := IntegralHom.ordinaryTensorZero.{u, u} (Spec (.of D.k)) (B D l E)
    let : ∀ M : Modules D l E,
        Functor.PreservesZeroMorphisms
          ((IntegralHom.ordinaryTensor.{u, u} (Spec (.of D.k)) (B D l E)).obj M) :=
      fun M ↦ IntegralHom.ordinaryTensorObjZero.{u, u} (Spec (.of D.k)) (B D l E) M
    let : ∀ (P' Q' : CochainComplex (Modules D l E) ℤ),
        HomologicalComplex.HasMapBifunctor P' Q'
          (IntegralHom.ordinaryTensor.{u, u} (Spec (.of D.k)) (B D l E)) (.up ℤ) :=
      fun P' Q' n ↦ by
        let : HasColimitsOfShape
            (Discrete {ij : ℤ × ℤ // ij.1 + ij.2 = n}) (Modules D l E) :=
          (IntegralHom.countableColimits.{u, u}
            (Spec (.of D.k)) (B D l E)).has_colimits_of_shape _
        exact HasColimitsOfShape.has_colimit _
    have hi := HomologicalComplex.ι_mapBifunctorMap (𝟙 (model D l E L adj P)) homIso.hom
      (IntegralHom.ordinaryTensor.{u, u} (Spec (.of D.k)) (B D l E)) (.up ℤ)
      p j (p + j) rfl
    simp only [HomologicalComplex.id_f, IntegralHom.ordinaryTensor,
      curriedTensor_map_app, curriedTensor_obj_map, ← Category.assoc, ← tensorHom_def] at hi
    have ht := congrArg (fun z ↦ z.val.app U
      (IntegralHom.pair.{u, u} (Spec (.of D.k)) (B D l E)
        ((model D l E L adj P).X p) ((model D l E L adj (dual l E P)).X j) U x f)) hi
    dsimp only [evaluation, HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    change (eB.f (p + j)).val.app U
      (((HomologicalComplex.mapBifunctorMap (𝟙 (model D l E L adj P)) homIso.hom
        (IntegralHom.ordinaryTensor.{u, u} (Spec (.of D.k)) (B D l E))
        (.up ℤ)).f (p + j)).val.app U _) = _
    change ((HomologicalComplex.mapBifunctorMap (𝟙 (model D l E L adj P)) homIso.hom
      (IntegralHom.ordinaryTensor.{u, u} (Spec (.of D.k)) (B D l E))
      (.up ℤ)).f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E) _ _ p j U x f) = _ at ht
    rw [ht]
    change (eB.f (p + j)).val.app U
      ((HomologicalComplex.ιMapBifunctor _ _
        (IntegralHom.ordinaryTensor.{u, u} (Spec (.of D.k)) (B D l E)) (.up ℤ)
        p j (p + j) rfl).val.app U
        (((𝟙 ((model D l E L adj P).X p) ⊗ₘ homIso.hom.f j)).val.app U
          (IntegralHom.pair.{u, u} (Spec (.of D.k)) (B D l E) _ _ U x f))) = _
    have hpure :
        ((𝟙 ((model D l E L adj P).X p) ⊗ₘ homIso.hom.f j)).val.app U
          (IntegralHom.pair.{u, u} (Spec (.of D.k)) (B D l E) _ _ U x f) =
        IntegralHom.pair.{u, u} (Spec (.of D.k)) (B D l E) _ _ U x
          ((homIso.hom.f j).val.app U f) :=
      @SheafOfModules.CochainScalarConstruction.pure_map.{u + 1, u + 1, u}
        (Spec (.of D.k)).ProEt inferInstance (essentiallySmallSelf.{0} _)
        (Scheme.ProEt.topology (Spec (.of D.k))) inferInstance (B D l E) _ _ _ _
        (𝟙 ((model D l E L adj P).X p)) (homIso.hom.f j) U x f
    rw [hpure]
    exact heB p j U x ((homIso.hom.f j).val.app U f)
  refine ⟨coeffUnit, q, evaluation, ringEval, ?_, ?_⟩
  · unfold Normalized
    refine ⟨hunit, hhom, hcoeff, hq, ?_, ?_⟩
    · intro p j hpj U b b' x f
      erw [heval]
      simp only [Units.smul_def, map_zsmul]
      rw [hhom, mul_comm b' b]
    · intro p j hpj x f
      have hh := hringEval p j x f
      have hh' := congrArg (moduleValue l E (p + j) hpj).hom hh
      exact hh'.trans (map_zsmul (moduleValue l E (p + j) hpj).hom _ _)
  · intro beta hbeta
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p j hpj
    change p + j = n at hpj
    subst n
    by_cases hpj0 : p + j = 0
    · apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x f
      have ht := congrArg (fun z ↦ z.hom (x ⊗ₜ[R l E] f))
        (HomologicalComplex.ι_mapBifunctorMap (𝟙 P) q.hom (curriedTensor _)
          (.up ℤ) p j (p + j) rfl)
      change (((MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 P) q.hom)).f
        (p + j)).hom
          ((HomologicalComplex.ιTensorObj P _ p j (p + j) rfl).hom (x ⊗ₜ[R l E] f)) =
        (HomologicalComplex.ιTensorObj P _ p j (p + j) rfl).hom
          (x ⊗ₜ[R l E] (q.hom.f j).hom f) at ht
      change (coeffUnit.inv.f (p + j)).hom
        ((((pointIntegralComplexSections D l E).map evaluation).f (p + j)).hom
          ((beta.f (p + j)).hom
            ((HomologicalComplex.ιTensorObj P _ p j (p + j) rfl).hom
              (x ⊗ₜ[R l E] f)))) =
        (ringEval.f (p + j)).hom
          ((((MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 P) q.hom)).f
            (p + j)).hom
              ((HomologicalComplex.ιTensorObj P _ p j (p + j) rfl).hom
                (x ⊗ₜ[R l E] f)))
      rw [hbeta, ht]
      apply (ConcreteCategory.bijective_of_isIso
        (moduleValue l E (p + j) hpj0)).1
      apply hscalar.1
      have hright := congrArg (moduleValue l E (p + j) hpj0).hom
        (hringEval p j x ((q.hom.f j).hom f))
      rw [hcoeffinv]
      change (sheafValue D l E (p + j) hpj0).val.app (op (PointDerivedHom.finalObject D.k))
        ((evaluation.f (p + j)).val.app (op (PointDerivedHom.finalObject D.k))
          (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
            (model D l E L adj P) (model D l E L adj (dual l E P)) p j
            (op (PointDerivedHom.finalObject D.k)) ((unit.hom.f p).hom x) f)) = _
      rw [heval, hunit]
      simp only [HomologicalComplex.ιTensorObj]
      erw [hright]
      simp only [Units.smul_def, map_zsmul]
      rw [hq]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ModuleCat.of (R l E) (R l E)) (p + j) hpj0).eq_of_tgt _ _

attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules

end WeilConjectures.PointPerfectOrdinaryEvaluation
