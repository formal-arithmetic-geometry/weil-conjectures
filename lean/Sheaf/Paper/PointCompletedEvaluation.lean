/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Paper.PointFibreDerivedTensor
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.PointProjectiveDualTensorModels
public import Sheaf.Paper.PointPerfectOrdinaryEvaluation
public import Sheaf.Paper.PointEvaluationCompletionNormalization
import Sheaf.Paper.IntegralPointCoefficientAdjunction
import all Sheaf.Paper.PointEvaluationCompletionNormalization
import Sheaf.Paper.PointIntegralCompletedTensorComparisons
import Sheaf.Paper.PointFiniteProjectiveAdjunctionUnits
import Mathlib.RingTheory.Noetherian.Basic
import all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Perfect point evaluation and the specified strict-cone completion

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence, and
thm-pod-identification-of-the-comparison, third paragraph
(blueprint: lem-pod-point-completed-evaluation).

The extension objects are the existing sheafified constant modules followed by
change of rings. The tensor tower is identified with the quotient tower of the
ordinary tensor by its balancing formula. Completed evaluation is the completion
of ordinary evaluation through that identification and the specified coefficient
completion unit. The final equation uses the recorded canonical point tensorator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian SheafOfModules.monoidalCategory
  WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.PointProjectiveDualTensorModels.unit
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.PointCompletedEvaluation

private theorem unit_iso_of_comparison {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} {W : B} (f : X ⟶ Y) (e : Y ≅ Z) (b : F.obj Z ≅ W)
    (h : IsIso (F.map (f ≫ e.hom) ≫ b.hom)) : IsIso (F.map f) := by
  have hh : IsIso (F.map (f ≫ e.hom)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ b.hom inferInstance h
  rw [Functor.map_comp] at hh
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (F.map e.hom) inferInstance hh

private theorem map_comp_congr {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y : A} {Z W : B} (a : F.obj Y ⟶ Z) (b : Z ⟶ W)
    {f g : X ⟶ Y} (h : f = g) : F.map f ≫ a ≫ b = F.map g ≫ a ≫ b :=
  congrArg (fun m ↦ F.map m ≫ a ≫ b) h

private theorem tensor_transport_cancel {A : Type*} [Category A] [MonoidalCategory A]
    {X Y Z T W : A} (a : X ≅ Y) (b : Y ≅ Z) (c : Z ⊗ T ≅ W) :
    (MonoidalCategory.tensor A).map (Prod.mkHom (a.hom ≫ b.hom) (𝟙 T)) ≫
      c.hom ≫ c.inv ≫
      (MonoidalCategory.tensor A).map (Prod.mkHom (b.inv ≫ a.inv) (𝟙 T)) = 𝟙 _ := by
  change ((a.hom ≫ b.hom) ⊗ₘ 𝟙 T) ≫ c.hom ≫ c.inv ≫
    ((b.inv ≫ a.inv) ⊗ₘ 𝟙 T) = 𝟙 _
  rw [Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.id_comp, id_tensorHom_id]

private theorem evaluation_from_inverse
    {A B C D : Type*} [Category A] [MonoidalCategory A] [Category B]
    [Category C] [Category D] [MonoidalCategory D]
    (F : B ⥤ A) (H : B ⥤ C) (G : C ⥤ D) (Q : A ⥤ D) [Q.LaxMonoidal]
    (α : H ⋙ G ≅ F ⋙ Q) {P V R : A} {J T K : B} {Z : C}
    (q : F.obj J ≅ V) (b : R ≅ F.obj K)
    (β : P ⊗ F.obj J ⟶ F.obj T) (e : T ⟶ K)
    (v : P ⊗ V ⟶ R) (χ : H.obj T ⟶ Z) (w : Z ⟶ H.obj K)
    (i : Q.obj P ⊗ G.obj (H.obj J) ⟶ G.obj Z) [IsIso i]
    (τ : G.obj Z ⟶ Q.obj P ⊗ G.obj (H.obj J))
    (hi : i ≫ τ = 𝟙 _)
    (hχ : χ ≫ w = H.map e)
    (hβ : β ≫ F.map e ≫ b.inv =
      (MonoidalCategory.tensor A).map (Prod.mkHom (𝟙 P) q.hom) ≫ v)
    (hcomparison : Functor.LaxMonoidal.μ Q P (F.obj J) ≫ Q.map β ≫
      α.inv.app T ≫ G.map χ =
        (MonoidalCategory.tensor D).map (Prod.mkHom (𝟙 (Q.obj P)) (α.inv.app J)) ≫ i) :
    G.map w ≫ α.hom.app K ≫ Q.map b.inv =
      τ ≫ (MonoidalCategory.tensor D).map
        (Prod.mkHom (𝟙 (Q.obj P)) (α.hom.app J ≫ Q.map q.hom)) ≫
        Functor.LaxMonoidal.μ Q P V ≫ Q.map v := by
  change β ≫ F.map e ≫ b.inv = (𝟙 P ⊗ₘ q.hom) ≫ v at hβ
  change Functor.LaxMonoidal.μ Q P (F.obj J) ≫ Q.map β ≫
    α.inv.app T ≫ G.map χ = (𝟙 (Q.obj P) ⊗ₘ α.inv.app J) ≫ i at hcomparison
  change G.map w ≫ α.hom.app K ≫ Q.map b.inv =
    τ ≫ (𝟙 (Q.obj P) ⊗ₘ (α.hom.app J ≫ Q.map q.hom)) ≫
      Functor.LaxMonoidal.μ Q P V ≫ Q.map v
  apply (cancel_epi i).mp
  rw [← Category.assoc i τ, hi, Category.id_comp]
  have hleft : i = (𝟙 (Q.obj P) ⊗ₘ α.hom.app J) ≫
      Functor.LaxMonoidal.μ Q P (F.obj J) ≫ Q.map β ≫ α.inv.app T ≫ G.map χ := by
    have hh := congrArg ((𝟙 (Q.obj P) ⊗ₘ α.hom.app J) ≫ ·) hcomparison
    simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Iso.hom_inv_id_app, id_tensorHom_id] using hh.symm
  rw [hleft]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hχ]
  have hn := α.inv.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]
  have hlocalized := congrArg Q.map hβ
  simp only [Functor.map_comp] at hlocalized
  rw [hlocalized, ← Functor.LaxMonoidal.μ_natural_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Q.map_id, Category.id_comp]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing lifted valuation ring. Source: blueprint coefficient conventions
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev R := PointEvaluationCompletion.R l E

/-- The completed coefficient sheaf on the original small pro-etale site.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev B := PointEvaluationCompletion.B D l E

/-- The recorded standard localization of completed-coefficient sheaf complexes.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev sheafQ := PointEvaluationCompletion.Q D l E

/-- The same small-Hom localization of ordinary modules used by the point fibre.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev moduleQ := PointEvaluationCompletion.QR l E

/-- The existing constant-to-completed coefficient map.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev alpha := PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true

/-- The ordinary coefficient complex R[0]. Source: Stacks 0A8H
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev ringComplex := PointProjectiveDualTensorModels.ringComplex l E

/-- The completed coefficient complex B[0]. Source: blueprint point coefficients
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev coefficient := PointEvaluationCompletion.coefficient D l E

/-- The functor is uniquely specified on objects and maps by the existing tensor construction.
Source: Stacks 03CY, 03EK; node proof step 1
(blueprint: lem-pod-point-completed-evaluation).
Proof: use the functoriality of constant-module sheafification and of change of rings.
Their identity, composition and additive laws hold on the sheafification generators,
by the corresponding laws for constant linear maps and tensoring with the identity.
The displayed object and morphism equations determine the functor uniquely. -/
theorem extension_existsUnique :
    ∃! L : ModuleCat.{u + 1} (R l E) ⥤ integralTowerModules l E (Spec (.of D.k)),
      (∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E)
        (alpha D l E) M) ∧
      L.Additive ∧
      (∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
        HEq (L.map f) (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E)
          (alpha D l E) f)) := by
  let := PointDerivedHom.abSheafify.{u, u} D.k
  let := PointDerivedHom.abLocallyBijective.{u, u} D.k
  let T := SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u}
    (alpha D l E)
  let L := PointDerivedHom.constantModules.{u, u} D.k (CommRingCat.of (R l E)) ⋙ T
  have : T.Additive :=
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction (alpha D l E)).left_adjoint_additive
  have : (PointDerivedHom.constantPresheaf.{u, u} D.k
      (CommRingCat.of (R l E))).Additive := ⟨by intros; rfl⟩
  have : (PresheafOfModules.sheafification
      (PointDerivedHom.constantUnit.{u, u} D.k (CommRingCat.of (R l E)))).Additive :=
    (PresheafOfModules.sheafificationAdjunction
      (PointDerivedHom.constantUnit.{u, u} D.k (CommRingCat.of (R l E)))).left_adjoint_additive
  have : (PointDerivedHom.constantModules.{u, u} D.k (CommRingCat.of (R l E))).Additive := by
    dsimp only [PointDerivedHom.constantModules]
    infer_instance
  refine ⟨L, ⟨fun _ ↦ rfl, inferInstance, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro L' hL'
  exact Functor.hext hL'.1 (fun M N f ↦ hL'.2.2 M N f)

/-- Actual constant-module extension, uniquely fixed by its existing object and map formulas.
Source: node proof step 1 (blueprint: lem-pod-point-completed-evaluation). -/
def extension := (extension_existsUnique D l E).exists.choose

/-- Additivity supplied by the canonical functor construction.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
instance extension_additive : (extension D l E).Additive :=
  (extension_existsUnique D l E).exists.choose_spec.2.1

/-- Apply the canonical extension termwise.
Source: Stacks 0A8X (blueprint: lem-pod-point-completed-evaluation). -/
def extensionComplex := (extension D l E).mapHomologicalComplex (.up ℤ)

/-- The construction's object, additive and morphism specifications, stated for extension.
Source: the unique construction in step 1
(blueprint: lem-pod-point-completed-evaluation). -/
theorem extension_spec :
    (∀ M, (extension D l E).obj M = PointDerivedHom.extensionObject.{u, u}
      D.k (B D l E) (alpha D l E) M) ∧
    (extension D l E).Additive ∧
    (∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
      HEq ((extension D l E).map f)
        (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E) (alpha D l E) f)) := by
  exact (extension_existsUnique D l E).exists.choose_spec

attribute [local irreducible] extension

/-- The same tensor generator transported through the uniquely fixed object equality.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
def generator (M : ModuleCat.{u + 1} (R l E))
    (U : (Spec (.of D.k)).ProEtᵒᵖ) (b : (B D l E).obj.obj U) (x : M) :=
  PointDerivedHom.generator.{u, u} D.k (B D l E) (alpha D l E) (extension D l E)
    (extension_spec D l E).1 M U b x

/-- The ordinary derived dual's bounded-projective chain model, with the recorded differential.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
abbrev dual (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  PointProjectiveDualTensorModels.dual l E P

/-- The specified ordinary sheaf tensor model.
Source: Stacks 06YL (blueprint: lem-pod-point-completed-evaluation). -/
abbrev total (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  PointEvaluationCompletion.total D l E C J

/-- The balancing identification of the two strict towers, uniquely on local generators.
Source: Bhatt--Scholze 3.4.10 and node proof step 6
(blueprint: lem-pod-point-completed-evaluation).
Proof: in every degree reassociate the balanced tensor products and total sums.
Send (x tensor a) tensor (y tensor b) to (x tensor y) tensor ab; the inverse sends
(x tensor y) tensor a to (x tensor 1) tensor (y tensor a). Balancing and the
signed differential give inverse chain maps. The quotient formulas commute with
all transitions. Sheafification and the total injections make the maps unique. -/
theorem towerBalancing_existsUnique
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! rho : ((integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J)) ≅
        ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
          (total D l E C J)),
      PointEvaluationCompletion.Balanced D l E C J rho := by
  sorry

/-- Balancing of the specified strict towers, with no arbitrary cone filler.
Source: node proof step 6 (blueprint: lem-pod-point-completed-evaluation). -/
@[irreducible] def towerBalancing
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  Classical.choose (towerBalancing_existsUnique D l E C J)

/-- Completed evaluation is the strict-cone completion of ordinary evaluation, followed
by the inverse of the specified coefficient completion unit. Both cone coordinates
are therefore fixed before localization. Source: node proof steps 6--7
(blueprint: lem-pod-point-completed-evaluation). -/
@[irreducible] def completedEvaluation
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (e : total D l E C.obj J.obj ⟶ coefficient D l E)
    (b : (sheafQ D l E).obj (coefficient D l E) ≅
      (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj (coefficient D l E))) :=
  PointEvaluationCompletion.completedPairing D l E C J
    (towerBalancing D l E C.obj J.obj) e b

/-- Reading the coefficient in a degree identified with zero uses the existing single-complex
isomorphism. Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def moduleValue (n : ℤ) (h : n = 0) :=
  PointProjectiveDualTensorModels.moduleValue l E n h

/-- The same single-complex isomorphism for the coefficient sheaf.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def sheafValue (n : ℤ) (h : n = 0) :=
  PointProjectiveDualTensorModels.sheafValue D l E n h

/-- The actual model B tensor underline P, rather than an arbitrary equivalent complex.
Source: node statement (blueprint: lem-pod-point-completed-evaluation). -/
abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  PointEvaluationCompletion.model D l E (extension D l E) P

/-- The tensor comparison after identifying sections of C with P by its canonical unit.
Source: node proof step 8 and lem-sf-point-fibre-derived-tensor
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose, irreducible] def tau (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :=
  (pointIntegralTensorComparison D l hl E S
    ⟨(sheafQ D l E).obj C, hC⟩ ⟨(sheafQ D l E).obj J, hJ⟩).hom ≫
    (MonoidalCategory.tensor _).map
      (Prod.mkHom ((pointIntegralDerivedFactors D l E).hom.app C ≫
        (moduleQ l E).map unit.inv) (𝟙 _))


private theorem inverse_comparison_isIso (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :
    IsIso (PointEvaluationCompletion.inverseTensorComparison D l E hl S P C J hC hJ
      unit.hom) := by
  dsimp [PointEvaluationCompletion.inverseTensorComparison]
  infer_instance

private theorem inverse_tau (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :
    PointEvaluationCompletion.inverseTensorComparison D l E hl S P C J hC hJ unit.hom ≫
      tau D l E hl S P C J hC hJ unit = 𝟙 _ := by
  unfold tau
  dsimp only [PointEvaluationCompletion.inverseTensorComparison]
  simp only [Category.assoc]
  exact tensor_transport_cancel ((moduleQ l E).mapIso unit)
    ((pointIntegralDerivedFactors D l E).symm.app C)
    (pointIntegralTensorComparison D l hl E S
      ⟨(sheafQ D l E).obj C, hC⟩ ⟨(sheafQ D l E).obj J, hJ⟩).symm

private theorem completion_unit_isIso
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅
        (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
          (total D l E C.obj J.obj))
    (h : IsIso (PointEvaluationCompletion.chi D l E C J rho)) :
    IsIso ((sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (total D l E C.obj J.obj))) := by
  dsimp only [PointEvaluationCompletion.chi] at h
  exact unit_iso_of_comparison (PointEvaluationCompletion.Q D l E)
    ((PointEvaluationCompletion.unit D l E).app (total D l E C.obj J.obj))
    (integralOperationsRoosFunctor.mapIso rho).symm
    (PointEvaluationCompletion.tensorModelIso D l E C J) h

attribute [local irreducible] PointEvaluationCompletion.inverseTensorComparison
  PointEvaluationCompletion.completedPairing PointEvaluationCompletion.chi

/-- All assertions concern the fixed perfect models and normalized canonical maps.
Source: node statement and proof steps 3--8
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose, irreducible] def Result (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) : Prop :=
  ∃ (good_C : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E P)),
  ∃ (good_J : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E (dual l E P))),
  ∃ (_constructible_tensor : sfIntegralConstructible l E (Spec (.of D.k))
    ((sheafQ D l E).obj (total D l E (model D l E P) (model D l E (dual l E P))))),
  ∃ (ctf_C : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E P))),
  ∃ (ctf_J : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E (dual l E P)))),
  ∃ (homIso : model D l E (dual l E P) ≅
    PointDerivedHom.sheafHom.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)),
  ∃ (_derivedHom_isIso : IsIso ((sheafQ D l E).map homIso.hom ≫
    IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
      (model D l E P) (coefficient D l E))),
  ∃ (unit : P ≅ (pointIntegralComplexSections D l E).obj (model D l E P)),
  ∃ (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E)),
  ∃ (q : (pointIntegralComplexSections D l E).obj (model D l E (dual l E P)) ≅ dual l E P),
  ∃ (evaluation : total D l E (model D l E P) (model D l E (dual l E P)) ⟶ coefficient D l E),
  ∃ (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E),
  ∃ (_ordinary_normalized : PointPerfectOrdinaryEvaluation.Normalized D l E
    (extension D l E) (hL := extension_additive D l E)
    (extension_spec D l E).1 P unit homIso
    coefficientUnit q evaluation ringEvaluation),
  ∃ (coefficientCompletion : (sheafQ D l E).obj (coefficient D l E) ≅
    (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).obj (coefficient D l E))),
  ∃ (_coefficientCompletion_normalized : coefficientCompletion.hom =
    (sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (coefficient D l E))),
  ∃ (_tensorCompletion_isIso : IsIso ((sheafQ D l E).map
    ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (total D l E (model D l E P) (model D l E (dual l E P)))))),
    (pointFibreIntegralAmbient D l E).map
      (completedEvaluation D l E ⟨model D l E P, good_C⟩
        ⟨model D l E (dual l E P), good_J⟩ evaluation coefficientCompletion) ≫
      (pointIntegralDerivedFactors D l E).hom.app (coefficient D l E) ≫
      (moduleQ l E).map coefficientUnit.inv =
    tau D l E hl S P (model D l E P) (model D l E (dual l E P)) ctf_C ctf_J unit ≫
      (MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 ((moduleQ l E).obj P))
        ((pointIntegralDerivedFactors D l E).hom.app (model D l E (dual l E P)) ≫
          (moduleQ l E).map q.hom)) ≫
      Functor.LaxMonoidal.μ (moduleQ l E) P (dual l E P) ≫
      (moduleQ l E).map ringEvaluation

private theorem result_of_models (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (good_C : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E P))
    (good_J : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E (dual l E P)))
    (_constructible_tensor : sfIntegralConstructible l E (Spec (.of D.k))
      ((sheafQ D l E).obj (total D l E (model D l E P) (model D l E (dual l E P)))))
    (ctf_C : finiteTorConstructibleIntegral l E (Spec (.of D.k))
      ((sheafQ D l E).obj (model D l E P)))
    (ctf_J : finiteTorConstructibleIntegral l E (Spec (.of D.k))
      ((sheafQ D l E).obj (model D l E (dual l E P))))
    (homIso : model D l E (dual l E P) ≅
      PointDerivedHom.sheafHom.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E))
    (_derivedHom_isIso : IsIso ((sheafQ D l E).map homIso.hom ≫
      IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
        (model D l E P) (coefficient D l E)))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj (model D l E P))
    (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E))
    (q : (pointIntegralComplexSections D l E).obj (model D l E (dual l E P)) ≅ dual l E P)
    (evaluation : total D l E (model D l E P) (model D l E (dual l E P)) ⟶ coefficient D l E)
    (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E)
    (_ordinary_normalized : PointPerfectOrdinaryEvaluation.Normalized D l E
      (extension D l E) (hL := extension_additive D l E)
    (extension_spec D l E).1 P unit homIso
      coefficientUnit q evaluation ringEvaluation)
    (coefficientCompletion : (sheafQ D l E).obj (coefficient D l E) ≅
      (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj (coefficient D l E)))
    (_coefficientCompletion_normalized : coefficientCompletion.hom =
      (sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
        (coefficient D l E)))
    (_tensorCompletion_isIso : IsIso ((sheafQ D l E).map
      ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
        (total D l E (model D l E P) (model D l E (dual l E P))))))
    (comparison :
      (pointFibreIntegralAmbient D l E).map
        (completedEvaluation D l E ⟨model D l E P, good_C⟩
          ⟨model D l E (dual l E P), good_J⟩ evaluation coefficientCompletion) ≫
        (pointIntegralDerivedFactors D l E).hom.app (coefficient D l E) ≫
        (moduleQ l E).map coefficientUnit.inv =
      tau D l E hl S P (model D l E P) (model D l E (dual l E P)) ctf_C ctf_J unit ≫
        (MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 ((moduleQ l E).obj P))
          ((pointIntegralDerivedFactors D l E).hom.app (model D l E (dual l E P)) ≫
            (moduleQ l E).map q.hom)) ≫
        Functor.LaxMonoidal.μ (moduleQ l E) P (dual l E P) ≫
        (moduleQ l E).map ringEvaluation) : Result D l E hl S P := by
  unfold Result
  exact ⟨good_C, good_J, _constructible_tensor, ctf_C, ctf_J, homIso,
    _derivedHom_isIso, unit, coefficientUnit,
    q, evaluation, ringEvaluation,
    _ordinary_normalized,
    coefficientCompletion, _coefficientCompletion_normalized, _tensorCompletion_isIso, comparison⟩



/-- Perfect-model evaluation respects the specified strict-cone derived completion.
Source: main-20261015 blueprint, point-dualizing proof second sentence, and comparison
identification third paragraph (blueprint: lem-pod-point-completed-evaluation).

Proof, following the node's eight steps:
1. The valuation-ring DVR/PID lemmas make R Noetherian. Constant sheafification is exact
and B is flat over the constant ring, so extension is exact. Point sections is exact.
The extension/sections adjunction sends h to x mapped to h(1 tensor x); its inverse
sends t to b tensor x mapped to b t(x) after restriction.
2. Connected constant H0 and sectionwise limits identify Gamma(B) with the quotient
limit of R, which is R by the integers-profinite-tower lemma. The actual unit is the
constant-value map, so the point reconstruction and ordinary evaluation hypotheses hold.
3. Duals and tensors of finite-projective summands remain finite projective. Boundedness
and Noetherianity give finite cohomology. Point reconstruction proves the three
constructible-complete assertions, including uniform reduction bounds. Bounded flat
complexes are K-flat, and their degree intervals give finite Tor amplitude.
4. The bounded-free RHom model identifies the ambient derived Hom with the ordinary
Hom complex. On finite free modules the displayed map b tensor f is the identity;
passing to summands proves homIso. Its formula commutes with the signed Hom differential.
5. The ordinary Hom adjunction gives q by evaluation at 1 tensor x, followed by the
coefficient-sections isomorphism. The signed sheaf and module evaluations agree on
every pure tensor: in bidegree (p,j) both composites are (-1)^(pj)h(1 tensor x).
6. Balance the two finite reductions to the reduction of the ordinary tensor, compatibly
with every quotient transition. Apply the functorial shifted cone. The identity-extension
comparison supplies precisely the displayed completion units: quotient-product component
and zero shifted-product component.
7. The reductions of ordinary evaluation form a strict tower morphism. Its two product
maps commute with 1 minus shift. Hence its cone map composed with the tensor completion
unit equals the coefficient completion unit composed with evaluation. Invert the latter
unit to obtain exactly completedEvaluation, the canonical completed evaluation.
8. The canonical point tensorator has inverse the sections balancing map followed by this
same tensor completion unit, as specified by PointIntegralTensorCanonical. Apply sections
to step 7, substitute the evaluation square from step 5, and compose with that tensorator.
The displayed equality is therefore an equality in D(R), with the same Koszul sign and
both specified cone coordinates. Zero complexes, negative degrees and degree-zero models
are included throughout. -/
theorem point_completed_evaluation (hl : l ≠ D.p) :
    ∃ S : PointIntegralTensorData D l hl E,
      Nonempty (PointIntegralTensorCanonical D l hl E S) ∧
      ∀ (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) (a b : ℤ),
        P.IsStrictlyGE a → P.IsStrictlyLE b →
        (∀ i : ℤ, Module.Projective (R l E) (P.X i) ∧ Module.Finite (R l E) (P.X i)) →
        Result D l E hl S P := by
  classical
  obtain ⟨I, canonical, _⟩ := pointIntegralCompletedTensorComparisons D l hl
  refine ⟨I E, ⟨canonical E⟩, ?_⟩
  intro P a b ha hb hP
  obtain ⟨hnoeth, _, _, _, hscalar, _, hsections,
      L, hobj, hmap, hexact, adj, hexplicit, _hunit, _, _, _⟩ :=
    IntegralPointCoefficientAdjunction.integral_point_coefficient_adjunction l E D hl
  have hLeq : L = extension D l E := by
    apply (extension_existsUnique D l E).unique
    · refine ⟨hobj, adj.left_adjoint_additive, ?_⟩
      intro M N f
      exact (conj_eqToHom_iff_heq' _ _ (hobj M) (hobj N).symm).mp (hmap M N f)
    · exact (extension_spec D l E)
  subst L
  have hobj_eq : hobj = (extension_spec D l E).1 :=
    Subsingleton.elim _ _
  subst hobj
  have : IsNoetherianRing (Padic.coefficientExtensionIntegers l E) := hnoeth
  have : IsNoetherianRing (R l E) :=
    isNoetherianRing_of_ringEquiv (Padic.coefficientExtensionIntegers l E) ULift.ringEquiv.symm
  have : PreservesFiniteLimits (extension D l E) := hexact.1
  have : PreservesFiniteColimits (extension D l E) := hexact.2
  have : PreservesFiniteLimits (PointDerivedHom.sections D.k (B D l E) (alpha D l E)) :=
    hsections.1
  have : PreservesFiniteColimits (PointDerivedHom.sections D.k (B D l E) (alpha D l E)) :=
    hsections.2
  have : PreservesFiniteLimits (PointDerivedHom.sections.{u, u} D.k
      (PointProjectiveDualTensorModels.B D l E)
      (PointProjectiveDualTensorModels.alpha D l E)) := hsections.1
  have : PreservesFiniteColimits (PointDerivedHom.sections.{u, u} D.k
      (PointProjectiveDualTensorModels.B D l E)
      (PointProjectiveDualTensorModels.alpha D l E)) := hsections.2
  have hm := PointProjectiveDualTensorModels.point_projective_dual_tensor_models
    D l E (extension D l E) (extension_spec D l E).1
      adj hl (fun f ↦ hmap _ _ f) hexplicit hscalar
      P a b ha hb hP
  rcases hm with ⟨_, _, hsheaf, _, _, hctf, _, _,
    homIso, hhom, hderived⟩
  have hu := PointDerivedHom.point_finiteProjective_adjunction_units D.k (B D l E)
    (alpha D l E) (extension D l E) (extension_spec D l E).1
      adj hexplicit hscalar
  have : IsIso (PointProjectiveDualTensorModels.unit D l E (extension D l E) adj P) :=
    PointProjectiveDualTensorModels.unit_isIso D l E
      (extension D l E) adj P (fun i ↦ @hu.1 (P.X i) (hP i).2 (hP i).1)
  let unitIso : P ≅ (pointIntegralComplexSections D l E).obj (model D l E P) :=
    PointProjectiveDualTensorModels.unitIso D l E (extension D l E) adj P
  have heta (i : ℤ) (x : P.X i) : (unitIso.hom.f i).hom x =
      generator D l E (P.X i) (op (PointDerivedHom.finalObject D.k)) 1 x := by
    exact PointProjectiveDualTensorModels.unitIso_apply D l E (extension D l E)
      (extension_spec D l E).1 adj hexplicit P i x
  have hC := hctf (model D l E P) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hJ := hctf (model D l E (dual l E P))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hT := hctf (total D l E (model D l E P) (model D l E (dual l E P)))
    (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hB := hctf (PointProjectiveDualTensorModels.coefficient D l E) List.mem_cons_self
  have hCflat := (hsheaf (model D l E P) List.mem_cons_self).2.2
  have hJmodel := hsheaf (model D l E (dual l E P))
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have hJflat := hJmodel.2.2
  have hJbounded := hJmodel.1
  have hextobj := (extension_spec D l E).1
  have hextmap := (extension_spec D l E).2.2
  have hhom' : ∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
    (sheafValue D l E (p + j) h).val.app U
      (PointDerivedHom.homValue D.k (B D l E) (model D l E P) (coefficient D l E)
        j p U ((homIso.hom.f j).val.app U
          (generator D l E ((dual l E P).X j) U b f))
        (generator D l E (P.X p) U b' x)) =
      b * b' * PointDerivedHom.scalar D.k (B D l E) (alpha D l E) U
        ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)) := hhom
  have hscalar' : Function.Bijective (pointIntegralSectionMap l E D.k) := by
    rw [← PointProjectiveDualTensorModels.scalar_eq D l E]
    exact hscalar
  obtain ⟨coeffUnit, q, evaluation, ringEvaluation, hnormalized, hsquare⟩ :=
    PointPerfectOrdinaryEvaluation.point_perfect_ordinary_evaluation D l E
      (extension D l E) (extension_spec D l E).1
      adj hexplicit hscalar' P unitIso heta homIso hhom'
  obtain ⟨goodC, goodJ, rho, hrho, hchi, _, _, _, _,
      completionUnit, hcompletionUnit, _, hpair, beta, hbeta, _,
      hinverse⟩ := PointEvaluationCompletion.point_evaluation_completion_normalization
        D l E hl (I E) (canonical E) (extension D l E) hextobj hextmap P
        ⟨a, b, ha, hb⟩ hP (model D l E (dual l E P)) hJbounded
        (fun i ↦ (hJflat i).1) (fun i ↦ (hCflat i).1) unitIso.hom heta
        hscalar' hB.1 hC hJ hT.1 evaluation
  change integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E P) at goodC
  have hrhoeq : rho = towerBalancing D l E (model D l E P) (model D l E (dual l E P)) :=
    by
      unfold towerBalancing
      exact (towerBalancing_existsUnique D l E _ _).unique hrho
        (Classical.choose_spec (towerBalancing_existsUnique D l E _ _)).1
  have hordinary := hsquare beta hbeta
  refine result_of_models D l E hl (I E) P goodC goodJ hT.1 hC hJ homIso hderived
    unitIso coeffUnit q evaluation ringEvaluation hnormalized
    completionUnit hcompletionUnit ?_ ?_
  · exact completion_unit_isIso D l E ⟨model D l E P, goodC⟩
      ⟨model D l E (dual l E P), goodJ⟩ rho hchi
  · have hevaleq : completedEvaluation D l E ⟨model D l E P, goodC⟩
        ⟨model D l E (dual l E P), goodJ⟩ evaluation completionUnit =
        PointEvaluationCompletion.completedPairing D l E ⟨model D l E P, goodC⟩
          ⟨model D l E (dual l E P), goodJ⟩ rho evaluation completionUnit :=
      by
        unfold completedEvaluation
        exact congrArg (fun r ↦ PointEvaluationCompletion.completedPairing D l E
          ⟨model D l E P, goodC⟩ ⟨model D l E (dual l E P), goodJ⟩
          r evaluation completionUnit) hrhoeq.symm
    refine (map_comp_congr (pointFibreIntegralAmbient D l E)
      ((pointIntegralDerivedFactors D l E).hom.app (coefficient D l E))
      ((moduleQ l E).map coeffUnit.inv) hevaleq).trans ?_
    let inverse := PointEvaluationCompletion.inverseTensorComparison D l E hl (I E)
      P (model D l E P) (model D l E (dual l E P)) hC hJ unitIso.hom
    have hi : IsIso inverse := by
      exact inverse_comparison_isIso D l E hl (I E) P
        (model D l E P) (model D l E (dual l E P)) hC hJ unitIso
    have hinvtau : inverse ≫ tau D l E hl (I E) P (model D l E P)
        (model D l E (dual l E P)) hC hJ unitIso = 𝟙 _ := by
      exact inverse_tau D l E hl (I E) P
        (model D l E P) (model D l E (dual l E P)) hC hJ unitIso
    exact evaluation_from_inverse (pointIntegralComplexSections D l E) (sheafQ D l E)
      (pointFibreIntegralAmbient D l E) (moduleQ l E) (pointIntegralDerivedFactors D l E)
      (P := P) (V := dual l E P) (R := ringComplex l E)
      (J := model D l E (dual l E P))
      (T := total D l E (model D l E P) (model D l E (dual l E P)))
      (K := coefficient D l E)
      (Z := (integralCompletedTensor l E (Spec (.of D.k))).obj
        ((sheafQ D l E).obj (model D l E P),
          (sheafQ D l E).obj (model D l E (dual l E P))))
      q coeffUnit beta evaluation ringEvaluation
      (PointEvaluationCompletion.chi D l E ⟨model D l E P, goodC⟩
        ⟨model D l E (dual l E P), goodJ⟩ rho)
      (PointEvaluationCompletion.completedPairing D l E ⟨model D l E P, goodC⟩
        ⟨model D l E (dual l E P), goodJ⟩ rho evaluation completionUnit)
      inverse (tau D l E hl (I E) P (model D l E P) (model D l E (dual l E P))
        hC hJ unitIso) hinvtau hpair hordinary hinverse

attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules

end WeilConjectures.PointCompletedEvaluation
