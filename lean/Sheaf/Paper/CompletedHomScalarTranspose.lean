/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointCompletedEvaluation
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.Paper.FiniteTorAmplitudeSites
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence
import all Sheaf.Paper.IntegralScalarExtensionConstructible
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Completed Hom scalar transposition on perfect point models

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence, coefficient-ring computation;
Stacks Tags 0A8X, 08J9 and 0FPT
(blueprint: lem-pod-completed-hom-scalar-transpose).

All models are the recorded constant-module extension models. The two implementations
of ordinary scalar extension are compared by their tensor generators. No statement
about taking sections is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.CompletedHomScalarTranspose

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The scalar-first implementation of the specified ordinary extension.
Source: node's ordinary-model formula
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
abbrev F := (integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex (.up ℤ)

/-- The coefficient inclusion with only the universe lift used by the point models.
Source: node's R to S inclusion
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def integerMap : PointCompletedEvaluation.R l E →+* PointCompletedEvaluation.R l L :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)

/-- P_L, using the recorded ordinary module tensor construction, with scalar first.
Source: node's definition of P_L
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
abbrev PL (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ) :=
  ((ModuleCat.extendScalars (integerMap l E L ι)).mapHomologicalComplex (.up ℤ)).obj P

/-- A homogeneous sheaf-model functional evaluated in degree zero.
Source: Stacks 0A8X and the node's local formula
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def value (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
    (h : PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E))
    (j p : ℤ) (hpj : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (f : ((PointCompletedEvaluation.model D l E
      (PointCompletedEvaluation.dual l E P)).X j).val.obj U)
    (z : ((PointCompletedEvaluation.model D l E P).X p).val.obj U) :=
  (PointCompletedEvaluation.sheafValue D l E (p + j) hpj).val.app U
    (PointDerivedHom.homValue.{u, u} D.k (PointCompletedEvaluation.B D l E)
      (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E)
      j p U ((h.hom.f j).val.app U f) z)

/-- The canonical ordinary-Hom-to-derived-Hom identification attached to the supplied model.
Source: Stacks 08J9 and node proof step 1
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def homMap (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
    (h : PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E)) :=
  DerivedCategory.Q.map h.hom ≫
    IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (PointCompletedEvaluation.B D l E)
      (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E)

/-- Normalization of the supplied ordinary finite-projective Hom identification.
Source: node hypothesis and PointCompletedEvaluation.Result
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def HomNormalized
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
    (h : PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E)) :
    Prop :=
  ∀ (p j : ℤ) (hpj : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (b c : (PointCompletedEvaluation.B D l E).obj.obj U)
    (f : (PointCompletedEvaluation.dual l E P).X j) (x : P.X p),
    value D l E P h j p hpj U
      (PointCompletedEvaluation.generator D l E _ U b f)
      (PointCompletedEvaluation.generator D l E _ U c x) =
      b * c * PointDerivedHom.scalar.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.alpha D l E) U
        ((PointCompletedEvaluation.moduleValue l E (p + j) hpj).hom
          ((f.v p (p + j) rfl).hom x))

/-- The balancing identification is fixed on generators, including its inverse.
Source: node statement and proof step 2
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: reassociate both balanced tensors, sending a tensor (b tensor x) to
image(b)*a tensor (1 tensor x). Its inverse sends c tensor (a tensor x) to
image(a)*c tensor (1 tensor x). Balancing proves both inverse identities.
Sheafification preserves them. Degree-zero coefficients commute with the differential.
The pure tensors generate after sheafification, giving uniqueness. -/
theorem modelBaseChange_existsUnique
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ) :
    ∃! k : (F D l E L ι).obj (PointCompletedEvaluation.model D l E P) ≅
        PointCompletedEvaluation.model D l L (PL l E L ι P),
      (∀ (p : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (b : (PointCompletedEvaluation.B D l E).obj.obj U)
        (a : (PointCompletedEvaluation.B D l L).obj.obj U) (x : P.X p),
        (k.hom.f p).val.app U
          (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
            ((PointCompletedEvaluation.model D l E P).X p) U a
            (PointCompletedEvaluation.generator D l E _ U b x)) =
          PointCompletedEvaluation.generator D l L _ U
            (((integralCompletedScalarMap l E L ι (Spec (.of D.k))).hom.app U b)*a)
            ((1 : PointCompletedEvaluation.R l L) ⊗ₜ[PointCompletedEvaluation.R l E,
              integerMap l E L ι] x)) ∧
      (∀ (p : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (b : (PointCompletedEvaluation.B D l L).obj.obj U)
        (a : PointCompletedEvaluation.R l L) (x : P.X p),
        (k.inv.f p).val.app U
          (PointCompletedEvaluation.generator D l L _ U b
            (a ⊗ₜ[PointCompletedEvaluation.R l E, integerMap l E L ι] x)) =
          integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
            ((PointCompletedEvaluation.model D l E P).X p) U
            (PointDerivedHom.scalar.{u, u} D.k (PointCompletedEvaluation.B D l L)
              (PointCompletedEvaluation.alpha D l L) U a * b)
            (PointCompletedEvaluation.generator D l E _ U 1 x)) := by
  sorry

/-- The uniquely generator-normalized model identification, with actual data.
Source: node proof step 2 (blueprint: lem-pod-completed-hom-scalar-transpose). -/
def modelBaseChange
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ) :=
  (modelBaseChange_existsUnique D l E L ι P).exists.choose

section OrdinaryTransportProof

attribute [local irreducible] ordinaryScalarModelIso
  completedScalarTensorSection integralOrdinaryTensorSection
  completedOrdinaryScalarExtension integralOrdinaryScalar
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem ordinaryTransport_model_spec :
    let a := (NatIso.mapHomologicalComplex
      (ordinaryScalarModelIso l E L ι (Spec (.of D.k))) (.up ℤ)).symm;
    ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (p : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b : (PointCompletedEvaluation.B D l L).obj.obj U) (x : (P.X p).val.obj U),
      ((a.hom.app P).f p).val.app U
        (completedScalarTensorSection l E L ι (Spec (.of D.k)) (P.X p) U b x) =
      integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (P.X p) U b x := by
  let W := Spec (.of D.k)
  let e := ordinaryScalarModelIso l E L ι W
  let a := (NatIso.mapHomologicalComplex e (.up ℤ)).symm
  dsimp only
  intro P p U b x
  have ht : (e.hom.app (P.X p)).val.app U
      (integralOrdinaryTensorSection l E L ι W (P.X p) U b x) =
      completedScalarTensorSection l E L ι W (P.X p) U b x := by
    simpa only [integralOrdinaryTensorSection] using
      ordinaryScalarModelIso_transport l E L ι W (P.X p) U b x
  have hc := congrArg (fun f ↦ f.val.app U
    (integralOrdinaryTensorSection l E L ι W (P.X p) U b x))
    (e.hom_inv_id_app (P.X p))
  exact (congrArg (fun z ↦ (e.inv.app (P.X p)).val.app U z) ht).symm.trans hc

/-- The two ordinary scalar implementations have a unique tensor-normalized transport.
Source: node's F and chi and proof steps 1--2
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: both functors are sheafified tensor extension along the unique completed-ring
map fixed by the finite quotient projections. The map on generators is the identity
balanced tensor. Sheafification and termwise extension give the chain isomorphism;
the same generators prove uniqueness. -/
theorem ordinaryTransport_existsUnique :
    ∃! a : completedOrdinaryScalarComplex l E L ι (Spec (.of D.k)) ≅ F D l E L ι,
      ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (p : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (b : (PointCompletedEvaluation.B D l L).obj.obj U) (x : (P.X p).val.obj U),
        ((a.hom.app P).f p).val.app U
          (completedScalarTensorSection l E L ι (Spec (.of D.k)) (P.X p) U b x) =
        integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (P.X p) U b x := by
  let W := Spec (.of D.k)
  let e := ordinaryScalarModelIso l E L ι W
  let a := (NatIso.mapHomologicalComplex e (.up ℤ)).symm
  have ha := ordinaryTransport_model_spec D l E L ι
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext P
  ext p : 1
  apply completedScalar_tensor_ext l E L ι W (P.X p)
  intro U s x
  exact (hb P p U s x).trans (ha P p U s x).symm


end OrdinaryTransportProof

/-- The ordinary tensor transport, selected only from its uniqueness characterization.
Source: node's F (blueprint: lem-pod-completed-hom-scalar-transpose). -/
def ordinaryTransport := (ordinaryTransport_existsUnique D l E L ι).exists.choose

section OrdinaryTransportModelProof

attribute [local irreducible] ordinaryScalarModelIso
  completedScalarTensorSection integralOrdinaryTensorSection
  completedOrdinaryScalarExtension integralOrdinaryScalar
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem unique_exists_choice_eq {α : Sort*} {p : α → Prop}
    (h : ∃! a, p a) (a : α) (ha : p a) : h.exists.choose = a :=
  h.unique h.exists.choose_spec ha

private theorem ordinaryTransport_model :
    ordinaryTransport D l E L ι =
      (NatIso.mapHomologicalComplex
        (ordinaryScalarModelIso l E L ι (Spec (.of D.k))) (.up ℤ)).symm := by
  unfold ordinaryTransport
  exact unique_exists_choice_eq (ordinaryTransport_existsUnique D l E L ι) _
    (ordinaryTransport_model_spec D l E L ι)

end OrdinaryTransportModelProof


/-- Scalar extension of the coefficient unit is multiplication, on the actual models.
Source: node's analogous model identifications
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: in degree zero multiply the two coefficients. The inverse sends b to b tensor 1.
Balancing proves the inverse equations and restrictions commute with multiplication.
In all other degrees the single complexes are zero. Generators give uniqueness. -/
theorem coefficientBaseChange_existsUnique :
    ∃! c : (F D l E L ι).obj (PointCompletedEvaluation.coefficient D l E) ≅
        PointCompletedEvaluation.coefficient D l L,
      ∀ (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (a : (PointCompletedEvaluation.B D l L).obj.obj U)
        (x : ((PointCompletedEvaluation.coefficient D l E).X 0).val.obj U),
        (PointCompletedEvaluation.sheafValue D l L 0 rfl).val.app U
          ((c.hom.f 0).val.app U
            (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
              ((PointCompletedEvaluation.coefficient D l E).X 0) U a x)) =
        ((integralCompletedScalarMap l E L ι (Spec (.of D.k))).hom.app U
          ((PointCompletedEvaluation.sheafValue D l E 0 rfl).val.app U x)) * a := by
  let W := Spec (.of D.k)
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} W
  let : (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} W
  let G := integralOrdinaryScalar l E L ι W
  let A := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)
  let A' := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L W)
  let φ := integralCompletedScalarMap l E L ι W
  let hA : G.obj A = SheafOfModules.changeOfRings φ A :=
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose A
  let e : G.obj A ≅ A' := eqToIso hA ≪≫ SheafOfModules.comparisonUnitIso φ
  let c : (F D l E L ι).obj (PointCompletedEvaluation.coefficient D l E) ≅
      PointCompletedEvaluation.coefficient D l L :=
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).app A ≪≫
      (CochainComplex.singleFunctor _ 0).mapIso e
  have hc : c.hom.f 0 ≫ PointCompletedEvaluation.sheafValue D l L 0 rfl =
      G.map (PointCompletedEvaluation.sheafValue D l E 0 rfl) ≫ e.hom := by
    change (((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app A).f 0 ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).map e.hom).f 0) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom =
      G.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ e.hom
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have he (U : W.ProEtᵒᵖ) (a : (PointCompletedEvaluation.B D l L).obj.obj U)
      (x : A.val.obj U) :
      e.hom.val.app U (integralOrdinaryTensorSection l E L ι W A U a x) =
        φ.hom.app U x * a := by
    dsimp only [e, Iso.trans_hom, eqToIso.hom]
    change (SheafOfModules.comparisonUnitIso φ).hom.val.app U
      ((eqToHom hA).val.app U
        ((eqToHom hA.symm).val.app U _)) = _
    rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl]
    simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
    have hv := SheafOfModules.unitForward_tmul φ U a x
    change (SheafOfModules.comparisonUnitIso φ).hom.val.app U
      ((toSheafify (Scheme.ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf φ A).presheaf).app U
          (a ⊗ₜ[(PointCompletedEvaluation.B D l E).obj.obj U, (φ.hom.app U).hom] x)) =
      a * φ.hom.app U x at hv
    simpa only [mul_comm] using hv
  have hc' : ∀ (U : W.ProEtᵒᵖ)
      (a : (PointCompletedEvaluation.B D l L).obj.obj U)
      (x : ((PointCompletedEvaluation.coefficient D l E).X 0).val.obj U),
      (PointCompletedEvaluation.sheafValue D l L 0 rfl).val.app U
        ((c.hom.f 0).val.app U
          (integralOrdinaryTensorSection l E L ι W _ U a x)) =
        φ.hom.app U ((PointCompletedEvaluation.sheafValue D l E 0 rfl).val.app U x) * a := by
    intro U a x
    have h := congrArg (fun f ↦ f.val.app U
      (integralOrdinaryTensorSection l E L ι W _ U a x)) hc
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at h
    refine h.trans ?_
    have hn : (G.map (PointCompletedEvaluation.sheafValue D l E 0 rfl)).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U a x) =
      integralOrdinaryTensorSection l E L ι W A U a
        ((PointCompletedEvaluation.sheafValue D l E 0 rfl).val.app U x) :=
      witnessTensor_naturality φ G
        (fun M ↦ (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M)
        (fun f ↦ (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose f)
        (PointCompletedEvaluation.sheafValue D l E 0 rfl) U a x
    exact (congrArg (e.hom.val.app U) hn).trans (he U a _)
  refine ⟨c, hc', ?_⟩
  intro c' hc''
  apply Iso.ext
  apply HomologicalComplex.to_single_hom_ext
  change c'.hom.f 0 = c.hom.f 0
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom).1
  apply tensorPresentation_hom_ext W φ _ _ _
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose _)
  intro U a x
  exact (hc'' U a x).trans (hc' U a x).symm

/-- The normalized coefficient-unit identification.
Source: node's coefficient identification
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def coefficientBaseChange := (coefficientBaseChange_existsUnique D l E L ι).exists.choose

/-- The conjugate of the scalar Hom transpose on the actual ordinary representatives.
All localization factors and input/output model identifications are fixed.
Source: node's delta conjugation and proof step 6
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def identifiedTranspose
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
    (h : PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E)) :=
  (integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapDerivedCategoryFactors.inv.app
      (PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P)) ≫
    (integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).map (homMap D l E P h) ≫
    scalarHomOrdinary l E L ι (Spec (.of D.k))
      (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))
      (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)) ≫
    (integralDerivedInternalHom l L (Spec (.of D.k))).map (Prod.mkHom
      (DerivedCategory.Q.map (modelBaseChange D l E L ι P).inv ≫
        (integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapDerivedCategoryFactors.inv.app
          (PointCompletedEvaluation.model D l E P)).op
      ((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapDerivedCategoryFactors.hom.app
          (PointCompletedEvaluation.coefficient D l E) ≫
        DerivedCategory.Q.map (coefficientBaseChange D l E L ι).hom))

/-- Equality in the strict quotient cones with both coordinates prescribed.
Source: node statement and proof step 5
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def CompletionSquare (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (f : C ⟶ J) : Prop :=
  ((F D l E E (AlgHom.id ℚ_[l] E)).map f ≫
      (integralScalarCompletionChain l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).app J =
    (integralScalarCompletionChain l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).app C ≫
      (integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).map f) ∧
  (∀ (i : ℤ) (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a : (PointCompletedEvaluation.B D l E).obj.obj U) (x : (C.X i).val.obj U),
    ((((F D l E E (AlgHom.id ℚ_[l] E)).map f ≫
        (integralScalarCompletionChain l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).app J ≫
        CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) J) ≫
        Pi.π (fun n ↦ (integralScalarLevel l E E (AlgHom.id ℚ_[l] E)
          (Spec (.of D.k)) n).obj J) n).f i).val.app U)
      (integralOrdinaryTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))
        (C.X i) U a x) =
      integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n (J.X i) U
        (((completedIntegralCommRingProjectionUnrestricted l E
          (Spec (.of D.k)) n).hom.app U) a) ((f.f i).val.app U x)) ∧
  ∀ (i j : ℤ) (hij : i + -1 = j),
    ((F D l E E (AlgHom.id ℚ_[l] E)).map f ≫
        (integralScalarCompletionChain l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).app J).f i ≫
      (CochainComplex.mappingCocone.snd
        (integralScalarRoosBoundary l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) J)).v i j hij = 0

/-- The precise ordinary sheaf-model statement, including the signed uncurrying.
Source: node statement and proof steps 1--6
(blueprint: lem-pod-completed-hom-scalar-transpose). -/
def ModelResult
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
    (h : PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E))
    (hL : PointCompletedEvaluation.model D l L
        (PointCompletedEvaluation.dual l L (PL l E L ι P)) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l L)
        (PointCompletedEvaluation.model D l L (PL l E L ι P))
        (PointCompletedEvaluation.coefficient D l L)) : Prop :=
  ∃ gamma : (F D l E L ι).obj
      (PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P)) ⟶
      PointCompletedEvaluation.model D l L
        (PointCompletedEvaluation.dual l L (PL l E L ι P)),
    (∀ (p j : ℤ) (hpj : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (f : ((PointCompletedEvaluation.model D l E
        (PointCompletedEvaluation.dual l E P)).X j).val.obj U)
      (z : ((PointCompletedEvaluation.model D l E P).X p).val.obj U)
      (a b : (PointCompletedEvaluation.B D l L).obj.obj U),
      value D l L (PL l E L ι P) hL j p hpj U
        ((gamma.f j).val.app U
          (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
            ((PointCompletedEvaluation.model D l E
              (PointCompletedEvaluation.dual l E P)).X j) U a f))
        (((modelBaseChange D l E L ι P).hom.f p).val.app U
          (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
            ((PointCompletedEvaluation.model D l E P).X p) U b z)) =
      (integralCompletedScalarMap l E L ι (Spec (.of D.k))).hom.app U
        (value D l E P h j p hpj U f z) * a * b) ∧
    (DerivedCategory.Q.map gamma ≫ homMap D l L (PL l E L ι P) hL =
      identifiedTranspose D l E L ι P h) ∧
    CompletionSquare D l L _ _ gamma ∧
    ∃ ev : PointCompletedEvaluation.total D l L
        (PointCompletedEvaluation.model D l L (PL l E L ι P))
        ((F D l E L ι).obj
          (PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P))) ⟶
        PointCompletedEvaluation.coefficient D l L,
      (∀ (p j : ℤ) (hpj : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (f : ((PointCompletedEvaluation.model D l E
          (PointCompletedEvaluation.dual l E P)).X j).val.obj U)
        (z : ((PointCompletedEvaluation.model D l E P).X p).val.obj U)
        (a b : (PointCompletedEvaluation.B D l L).obj.obj U),
        (PointCompletedEvaluation.sheafValue D l L (p + j) hpj).val.app U
          ((ev.f (p + j)).val.app U
            (PointDerivedHom.totalElement.{u, u} D.k (PointCompletedEvaluation.B D l L)
              (PointCompletedEvaluation.model D l L (PL l E L ι P))
              ((F D l E L ι).obj (PointCompletedEvaluation.model D l E
                (PointCompletedEvaluation.dual l E P))) p j U
              (((modelBaseChange D l E L ι P).hom.f p).val.app U
                (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
                  ((PointCompletedEvaluation.model D l E P).X p) U b z))
              (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
                ((PointCompletedEvaluation.model D l E
                  (PointCompletedEvaluation.dual l E P)).X j) U a f))) =
          (p * j).negOnePow •
            ((integralCompletedScalarMap l E L ι (Spec (.of D.k))).hom.app U
              (value D l E P h j p hpj U f z) * a * b)) ∧
      CompletionSquare D l L _ _ ev

/-- The actual chain-model scalar transpose, with no K-injectivity assumption on B[0].
Source: node statement and proof steps 1--6
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: finite-projective splittings show that the displayed models and evaluation
products are bounded flat, hence K-flat (bounded-above-flat-site and derived change
of rings). Balance gamma(h tensor a)(z tensor b)=h(z)ab. Its Hom differential is
-(-1)^j h d, so gamma commutes with the differential. The ordinary Hom identifications
place it in J_L. Uncurry after the fixed K-injective resolution, using the one-K-flat
chain transpose; swapping the two homogeneous factors introduces (-1)^(pj).
At each finite quotient the normalized tensor map gives the same signed product.
The strict completion augmentations have quotient product and zero shifted product
coordinates. Strict tower maps act diagonally, so both routes agree as actual maps
into the shifted cone. Thus the uncurried maps agree in D(B'). Injectivity of the
closed transpose identifies gamma with the conjugated delta, as displayed. -/
theorem completed_hom_scalar_transpose (_hl : l ≠ D.p)
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
    (lo hi : ℤ) (_hlo : P.IsStrictlyGE lo) (_hhi : P.IsStrictlyLE hi)
    (_hP : ∀ n : ℤ, Module.Projective (PointCompletedEvaluation.R l E) (P.X n) ∧
      Module.Finite (PointCompletedEvaluation.R l E) (P.X n))
    (_hmodelsE : ∀ C ∈ [PointCompletedEvaluation.model D l E P,
        PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P),
        PointCompletedEvaluation.total D l E (PointCompletedEvaluation.model D l E P)
          (PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P))],
      finiteTorConstructibleIntegral l E (Spec (.of D.k)) (DerivedCategory.Q.obj C))
    (_hmodelsL : ∀ C ∈ [PointCompletedEvaluation.model D l L (PL l E L ι P),
        PointCompletedEvaluation.model D l L
          (PointCompletedEvaluation.dual l L (PL l E L ι P)),
        PointCompletedEvaluation.total D l L
          (PointCompletedEvaluation.model D l L (PL l E L ι P))
          (PointCompletedEvaluation.model D l L
            (PointCompletedEvaluation.dual l L (PL l E L ι P)))],
      finiteTorConstructibleIntegral l L (Spec (.of D.k)) (DerivedCategory.Q.obj C))
    (h : PointCompletedEvaluation.model D l E (PointCompletedEvaluation.dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l E)
        (PointCompletedEvaluation.model D l E P) (PointCompletedEvaluation.coefficient D l E))
    (_hh : HomNormalized D l E P h) (_hd : IsIso (homMap D l E P h))
    (hL : PointCompletedEvaluation.model D l L
        (PointCompletedEvaluation.dual l L (PL l E L ι P)) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (PointCompletedEvaluation.B D l L)
        (PointCompletedEvaluation.model D l L (PL l E L ι P))
        (PointCompletedEvaluation.coefficient D l L))
    (_hhL : HomNormalized D l L (PL l E L ι P) hL)
    (_hdL : IsIso (homMap D l L (PL l E L ι P) hL)) :
    ModelResult D l E L ι P h hL := by
  sorry


section CompletionTransportProof

attribute [local irreducible] DerivedCategory.Q ordinaryScalarModelIso
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

section ModelEquations

private local instance modelSiteSmall :
    EssentiallySmall.{u + 1} (Spec (.of D.k)).ProEt := essentiallySmallSelf.{0} _

private local instance modelSheafify :
    HasSheafify (Scheme.ProEt.topology (Spec (.of D.k))) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} (Spec (.of D.k))

private local instance modelLocallyBijective :
    (Scheme.ProEt.topology (Spec (.of D.k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} (Spec (.of D.k))

attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

private def scalarModel :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (completedCoefficientMap l E L ι (Spec (.of D.k))) :=
  completedScalarCochainModel.{u, u} l E L ι (Spec (.of D.k))

private def cochainCounit :
    DerivedCategory.Q ⋙ completedDerivedScalarExtension l E L ι (Spec (.of D.k)) ⟶
      completedOrdinaryScalarComplex l E L ι (Spec (.of D.k)) ⋙ DerivedCategory.Q :=
  (scalarModel D l E L ι).ε

private theorem cochainCounit_universal :
    (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).IsLeftDerivedFunctor
      (cochainCounit D l E L ι)
      (HomologicalComplex.quasiIso (integralTowerModules l E (Spec (.of D.k))) (.up ℤ)) := by
  exact (scalarModel D l E L ι).universal

private theorem cochainCounit_app
    (C : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (cochainCounit D l E L ι).app C = completedScalarCounit l E L ι (Spec (.of D.k)) C := by
  exact completedScalarCochainModel_counit l E L ι (Spec (.of D.k)) C

end ModelEquations

attribute [local irreducible] scalarModel completedScalarCochainModel cochainCounit
  completedDerivedScalarExtension completedScalarCounit

attribute [local irreducible] integralOrdinaryScalar
  completedScalarChainComparison
  integralScalarCompletionChain completedScalarComparison scalarCompletion

/-- The specified strict completion map is unchanged by the ordinary tensor transport.
Source: node statement and proof steps 2, 5--6
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: after the tensor-normalized ordinary transport, both maps have the same finite
quotient maps as their product components and zero shifted components. The two cone
coordinates determine the chain maps. Universal localization of good representatives
then gives unique ordinary and completed derived transports with the displayed counit
and representative squares. Those squares and the strict chain equality determine the
comparison equality on good representatives, hence on every derived object. -/
theorem completion_implementation_transport :
    (∀ C : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
      (completedScalarChainComparison l E L ι (Spec (.of D.k))).app C =
        (ordinaryTransport D l E L ι).hom.app C ≫
          (integralScalarCompletionChain l E L ι (Spec (.of D.k))).app C) ∧
    ∃! ed :
      (completedDerivedScalarExtension l E L ι (Spec (.of D.k)) ≅
        integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))) ×
      (integralScalarExtensionOfUniverses l E L ι (Spec (.of D.k)) ≅
        integralScalarExtension l E L ι (Spec (.of D.k))),
      (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        ed.1.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapDerivedCategoryFactors.hom.app
              P.obj =
          completedScalarCounit l E L ι (Spec (.of D.k)) P.obj ≫
            DerivedCategory.Q.map ((ordinaryTransport D l E L ι).hom.app P.obj)) ∧
      (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        ed.2.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι (Spec (.of D.k))).hom.app P =
          (integralScalarExtensionComparisonOfUniverses l E L ι (Spec (.of D.k))).hom.app P) ∧
      ∀ M : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
        ed.1.hom.app M ≫ (scalarCompletion l E L ι (Spec (.of D.k))).app M =
          (completedScalarComparison l E L ι (Spec (.of D.k))).app M ≫ ed.2.hom.app M := by
  let W := Spec (.of D.k)
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} W
  let : (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} W
  let A := integralTowerModules l E W
  let G := integralOrdinaryScalar l E L ι W
  let t := ordinaryTransport D l E L ι
  have hchain : completedScalarChainComparison l E L ι W =
      t.hom ≫ integralScalarCompletionChain l E L ι W := by
    rw [integralScalarCompletionChain_model]
    change _ = (ordinaryTransport D l E L ι).hom ≫ _
    rw [ordinaryTransport_model]
    exact (Iso.inv_hom_id_assoc _ _).symm
  have hchain_app (C : CochainComplex A ℤ) :
      (completedScalarChainComparison l E L ι W).app C =
        t.hom.app C ≫ (integralScalarCompletionChain l E L ι W).app C :=
    NatTrans.congr_app hchain C
  refine ⟨hchain_app, ?_⟩
  let q := HomologicalComplex.quasiIso A (.up ℤ)
  let T := completedDerivedScalarExtension l E L ι W
  let ε := cochainCounit D l E L ι
  let : T.IsLeftDerivedFunctor ε q := cochainCounit_universal D l E L ι
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ G.mapDerivedCategoryFactors
  let e₁ : completedDerivedScalarExtension l E L ι W ≅
      integralOrdinaryDerivedScalar l E L ι W :=
    Functor.leftDerivedNatIso T G.mapDerivedCategory ε
      G.mapDerivedCategoryFactors.hom q (Functor.isoWhiskerRight t DerivedCategory.Q)
  let e₂ : integralScalarExtensionOfUniverses l E L ι W ≅
      integralScalarExtension l E L ι W := Iso.refl _
  have h₁ (C : CochainComplex A ℤ) :
      e₁.hom.app (DerivedCategory.Q.obj C) ≫ G.mapDerivedCategoryFactors.hom.app C =
        completedScalarCounit l E L ι W C ≫ DerivedCategory.Q.map (t.hom.app C) := by
    have h := Functor.leftDerivedNatTrans_app T G.mapDerivedCategory ε
      G.mapDerivedCategoryFactors.hom q (Functor.isoWhiskerRight t DerivedCategory.Q).hom C
    exact h.trans (congrArg (· ≫ DerivedCategory.Q.map (t.hom.app C))
      (cochainCounit_app D l E L ι C))
  have h₂ (C : (integralOperationsGoodComplex l E W).FullSubcategory) :
      e₂.hom.app (DerivedCategory.Q.obj C.obj) ≫
          (integralScalarExtensionComparison l E L ι W).hom.app C =
        (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app C := by
    exact Category.id_comp _
  let Λ := integralOperationsGoodLocalization l E W
  let qg := q.inverseImage (integralOperationsGoodComplex l E W).ι
  let : Λ.IsLocalization qg := integralOperationsGoodLocalization_isLocalization l E W
  have hcomp : e₁.hom ≫ scalarCompletion l E L ι W =
      completedScalarComparison l E L ι W := by
    apply Localization.natTrans_ext Λ qg
    intro C
    apply (cancel_mono ((integralScalarExtensionComparison l E L ι W).hom.app C)).1
    change (e₁.hom.app (DerivedCategory.Q.obj C.obj) ≫
      (scalarCompletion l E L ι W).app (DerivedCategory.Q.obj C.obj)) ≫ _ = _
    have hs : (scalarCompletion l E L ι W).app (DerivedCategory.Q.obj C.obj) ≫
        (integralScalarExtensionComparison l E L ι W).hom.app C =
      G.mapDerivedCategoryFactors.hom.app C.obj ≫
        DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app C.obj) := by
      simpa only [scalarCompletion] using
        (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 C
    calc
      _ = e₁.hom.app (DerivedCategory.Q.obj C.obj) ≫
          ((scalarCompletion l E L ι W).app (DerivedCategory.Q.obj C.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app C) := Category.assoc _ _ _
      _ = e₁.hom.app (DerivedCategory.Q.obj C.obj) ≫
          (G.mapDerivedCategoryFactors.hom.app C.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app C.obj)) :=
        congrArg (e₁.hom.app (DerivedCategory.Q.obj C.obj) ≫ ·) hs
      _ = (e₁.hom.app (DerivedCategory.Q.obj C.obj) ≫
          G.mapDerivedCategoryFactors.hom.app C.obj) ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app C.obj) :=
        (Category.assoc _ _ _).symm
      _ = (completedScalarCounit l E L ι W C.obj ≫ DerivedCategory.Q.map (t.hom.app C.obj)) ≫
          DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app C.obj) :=
        congrArg (· ≫ DerivedCategory.Q.map
          ((integralScalarCompletionChain l E L ι W).app C.obj)) (h₁ C.obj)
      _ = completedScalarCounit l E L ι W C.obj ≫
          DerivedCategory.Q.map
            (t.hom.app C.obj ≫ (integralScalarCompletionChain l E L ι W).app C.obj) := by
        rw [Category.assoc, ← DerivedCategory.Q.map_comp]
      _ = completedScalarCounit l E L ι W C.obj ≫
          DerivedCategory.Q.map ((completedScalarChainComparison l E L ι W).app C.obj) := by
        rw [← hchain_app C.obj]
      _ = _ := (completedScalarComparison_spec l E L ι W C).symm
  refine ⟨(e₁, e₂), ⟨fun C ↦ h₁ C.obj, h₂, ?_⟩, ?_⟩
  · intro M
    have h : e₁.hom.app M ≫ (scalarCompletion l E L ι W).app M =
        (completedScalarComparison l E L ι W).app M := NatTrans.congr_app hcomp M
    exact h.trans (Category.comp_id ((completedScalarComparison l E L ι W).app M)).symm
  · intro d hd
    apply Prod.ext
    · apply Iso.ext
      apply Localization.natTrans_ext Λ qg
      intro C
      apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app C.obj)).1
      exact (hd.1 C).trans (h₁ C.obj).symm
    · apply Iso.ext
      apply Localization.natTrans_ext Λ qg
      intro C
      change d.2.hom.app (DerivedCategory.Q.obj C.obj) =
        e₂.hom.app (DerivedCategory.Q.obj C.obj)
      have h' : d.2.hom.app (DerivedCategory.Q.obj C.obj) ≫
          (integralScalarExtensionComparison l E L ι W).hom.app C =
        e₂.hom.app (DerivedCategory.Q.obj C.obj) ≫
          (integralScalarExtensionComparison l E L ι W).hom.app C :=
        (hd.2.1 C).trans (h₂ C).symm
      have h := congrArg (· ≫ (integralScalarExtensionComparison l E L ι W).inv.app C) h'
      simp only [Category.assoc, Iso.hom_inv_id_app] at h
      change d.2.hom.app (DerivedCategory.Q.obj C.obj) ≫ 𝟙 _ =
        e₂.hom.app (DerivedCategory.Q.obj C.obj) ≫ 𝟙 _ at h
      simpa only [Category.comp_id] using h

end CompletionTransportProof

/-- The completed transpose, conjugated by the specified completion units, is ordinary.
Specialize M to K and N to B[0], and use the fixed Hom-model maps in ModelResult.
Source: node statement and proof steps 5--6
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: the prescribed completed Hom map is the ordinary transpose conjugated by the
three specified completion maps. The completion implementation transport identifies
these with chi. Cancel the Hom-output inverse and both input comparison inverses.
On representatives this cancellation is the equality of quotient product coordinates
and zero shifted coordinates established before localization; no detection assertion
about arbitrary derived maps after finite reduction is used. -/
theorem completed_conjugation
    (M N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hM : IsSfDerivedComplete l E (Spec (.of D.k)) M)
    (hN : IsSfDerivedComplete l E (Spec (.of D.k)) N) :
    (scalarCompletion l E L ι (Spec (.of D.k))).app
        ((integralDerivedInternalHom l E (Spec (.of D.k))).obj (op M, N)) ≫
      (scalarHomCompleteInputs l E L ι (Spec (.of D.k)) M N hM hN).hom ≫
      (integralDerivedInternalHom l L (Spec (.of D.k))).map (Prod.mkHom
        ((scalarCompletionIso l E L ι (Spec (.of D.k)) M hM).hom.op)
        ((scalarCompletionIso l E L ι (Spec (.of D.k)) N hN).inv)) =
      scalarHomOrdinary l E L ι (Spec (.of D.k)) M N := by
  let W := Spec (.of D.k)
  let H := integralDerivedInternalHom l L W
  let cM := scalarCompletionIso l E L ι W M hM
  let cN := scalarCompletionIso l E L ι W N hN
  let cH := scalarCompletionIso l E L ι W
    ((integralDerivedInternalHom l E W).obj (op M, N))
    (scalarInternalHom_complete l E W M N hN)
  change cH.hom ≫ (cH.inv ≫ scalarHomOrdinary l E L ι W M N ≫
    H.map (Prod.mkHom cM.inv.op cN.hom)) ≫
    H.map (Prod.mkHom cM.hom.op cN.inv) = _
  simp only [← Category.assoc]
  rw [Category.assoc, ← H.map_comp]
  simp only [Iso.hom_inv_id, Category.id_comp, prod_comp, cancelIso, Bifunctor.map_id]
  exact Category.comp_id _


/-- Derived naturality of the model transpose, identity normalization and the integral
coefficient-tower equation after conjugation by chi. The ordinary associator here is
exactly the one whose conjugate specifies the integral associator in the node.
Source: node statement and proof steps 7--9
(blueprint: lem-pod-completed-hom-scalar-transpose).
Proof: naturality of the scalar operation and completion map extends to every derived
morphism, including inverses of quasi-isomorphisms; conjugate by the fixed model maps.
For the identity coefficient map multiplication identifies h tensor a with ah, and
both input and output identifications cancel. For a tower, the successive formula
on ((h tensor a) tensor c) evaluated at ((z tensor b) tensor d) is
image(h(z))*image(a)*image(b)*c*d. The direct formula after balanced associators is
the same product, with the same sign (-1)^(pj). The same equality holds at every
quotient and commutes with transitions. Strict diagonal maps preserve both product
coordinates and zero shifted coordinates. Substitute the specified integral associator
as the conjugate by chi: adjacent inverse comparisons cancel, leaving that ordinary
associator equation. Thus all assertions concern the specified maps. -/
theorem derived_coherence
    (P : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ) :
    (∀ (Q : CochainComplex (ModuleCat.{u + 1} (PointCompletedEvaluation.R l E)) ℤ)
      (v : DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E Q) ⟶
        DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P)),
      (integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).map
        ((integralDerivedInternalHom l E (Spec (.of D.k))).map
          (Prod.mkHom v.op (𝟙 (DerivedCategory.Q.obj
            (PointCompletedEvaluation.coefficient D l E))))) ≫
        scalarHomOrdinary l E L ι (Spec (.of D.k))
          (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E Q))
          (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)) =
      scalarHomOrdinary l E L ι (Spec (.of D.k))
          (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))
          (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)) ≫
        (integralDerivedInternalHom l L (Spec (.of D.k))).map (Prod.mkHom
          ((integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).map v).op
          (𝟙 ((integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).obj
            (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)))))) ∧
    ((integralDerivedInternalHom l E (Spec (.of D.k))).map (Prod.mkHom
        (((integralOrdinaryDerivedScalarUnit l E (Spec (.of D.k))).inv.app
          (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))).op)
        (𝟙 (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)))) ≫
      (integralOrdinaryDerivedScalarUnit l E (Spec (.of D.k))).inv.app
        ((integralDerivedInternalHom l E (Spec (.of D.k))).obj
          (op (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P)),
            DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E))) ≫
      scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)) =
      (integralDerivedInternalHom l E (Spec (.of D.k))).map (Prod.mkHom
        (𝟙 (op ((integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E)
          (Spec (.of D.k))).obj (DerivedCategory.Q.obj
            (PointCompletedEvaluation.model D l E P)))))
        ((integralOrdinaryDerivedScalarUnit l E (Spec (.of D.k))).inv.app
          (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E))))) ∧
    ∀ (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
      (j : L →ₐ[ℚ_[l]] M),
      (integralOrdinaryDerivedScalar l L M j (Spec (.of D.k))).map
        (scalarHomOrdinary l E L ι (Spec (.of D.k))
          (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))
          (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E))) ≫
      scalarHomOrdinary l L M j (Spec (.of D.k))
        ((integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).obj
          (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P)))
        ((integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).obj
          (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E))) ≫
      (integralDerivedInternalHom l M (Spec (.of D.k))).map (Prod.mkHom
        (((integralOrdinaryDerivedScalarComp l E L ι (Spec (.of D.k)) M j).inv.app
          (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))).op)
        ((integralOrdinaryDerivedScalarComp l E L ι (Spec (.of D.k)) M j).hom.app
          (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)))) =
      (integralOrdinaryDerivedScalarComp l E L ι (Spec (.of D.k)) M j).hom.app
        ((integralDerivedInternalHom l E (Spec (.of D.k))).obj
          (op (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P)),
            DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E))) ≫
      scalarHomOrdinary l E M (j.comp ι) (Spec (.of D.k))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q v
    have hv := scalarHomOrdinary_naturality l E L ι (Spec (.of D.k))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E P))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.model D l E Q))
        (DerivedCategory.Q.obj (PointCompletedEvaluation.coefficient D l E)) v (𝟙 _)
    rw [(integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).map_id] at hv
    exact hv
  · exact (scalarOperationsOrdinary_unit l E
      (𝟙 (Spec (.of D.k))) (Spec (.of D.k))).2.2 _ _
  · intro M _ _ _ j
    exact (scalarOperationsOrdinary_tower l E L ι M j
      (𝟙 (Spec (.of D.k))) (Spec (.of D.k))).2.2 _ _


attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules

end WeilConjectures.CompletedHomScalarTranspose
