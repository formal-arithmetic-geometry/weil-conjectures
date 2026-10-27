module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import Sheaf.CategoryTheory.SemilinearScalarLocalization
import all Sheaf.Paper.PointSectionsScalarExtension
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison
import all Sheaf.Paper.PointFiniteReductionSectionAlgebra
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Transport of completed coefficient models through point sections

Source: blueprint, lem-pod-point-dualizing-complex.proof.md, coefficient-ring sentence
(blueprint: lem-pod-completed-model-sections-transport).

## Main definitions and statements

* `model`, `unit`, `Realizes`, and `transport` specify the completed model and its maps.
* `completedModelSectionsTransport` states the integral and rational map equalities.
* `chainTransport_spec` gives the equivalent cochain and pure-tensor calculation.
* `transport_naturality`, `transport_identity`, and `transport_tower` give coherence.
* `scalarLocalizedNaturality`, `scalarLocalizedContravariant`, and
  `scalarLocalizedCoherence` give all raw-localization clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local irreducible] CategoryTheory.Limits.limit HasDerivedCategory.standard

universe u v w r s
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ChangeOfRings
namespace WeilConjectures.CompletedModelSections

attribute [-instance] WeilConjectures.coefficientComplexModuleDerived
  WeilConjectures.coefficientComplexIntegralAdditive
  WeilConjectures.coefficientComplexIntegralLimits
  WeilConjectures.coefficientComplexIntegralColimits
  WeilConjectures.coefficientComplexRationalAdditive
  WeilConjectures.coefficientComplexRationalLimits
  WeilConjectures.coefficientComplexRationalColimits
  WeilConjectures.coefficientComplexFieldAdditive
  WeilConjectures.coefficientComplexFieldLimits
  WeilConjectures.coefficientComplexFieldColimits
  WeilConjectures.pointFiniteFreeModuleTensor_additive

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The commutative-ring version of the recorded constant-to-completion map.
Source: completed integral coefficients (blueprint: lem-pod-completed-model-sections-transport).
-/
def coefficient :
    (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ⟶
        completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)) :=
  (sheafCompose (Scheme.ProEt.topology (Spec (.of D.k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
      (integralConstantToCompletionOfUniverses l E (Spec (.of D.k)))

/-- The existing ordinary change-of-rings witness, whose object and map are prescribed
by sheafified tensor; no arbitrary functor is chosen.
Source: Stacks 06YY (blueprint: lem-pod-completed-model-sections-transport). -/
abbrev scalarData :=
  letI : EssentiallySmall.{u + 1} (Spec (.of D.k)).ProEt := essentiallySmallSelf.{u + 1, u, u + 1} _
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (coefficient D l E)

/-- The recorded constant module sheaf, exposed functorially in its module argument.
The objects are proEtaleConstantModuleSheafOfUniverses; the maps are sheafified
constant presheaf maps. Only the coefficient action is transported through ULift.
Source: def-weil-proetale-locally-constant-sheaf
(blueprint: lem-pod-completed-model-sections-transport). -/
def constant : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
    SheafOfModules.{u + 1} (integralConstantRingOfUniverses l E (Spec (.of D.k))) :=
  letI := (Scheme.proEtaleConstantRingUnit_locallyBijectiveOfUniverses
    (Spec (.of D.k)) (Padic.coefficientExtensionIntegers l E)).1
  letI := (Scheme.proEtaleConstantRingUnit_locallyBijectiveOfUniverses
    (Spec (.of D.k)) (Padic.coefficientExtensionIntegers l E)).2
  ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E) ≃+* _).toRingHom ⋙
    siteConstantModulePresheafGeneral (C := (Spec (.of D.k)).ProEt)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⋙
    PresheafOfModules.sheafification
      (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
        ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))

/-- Constant sheafification followed by ordinary extension to completed coefficients.
Source: the model formula in the node (blueprint: lem-pod-completed-model-sections-transport).
-/
def realization : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
    integralTowerModules l E (Spec (.of D.k)) :=
  constant D l E ⋙ (scalarData D l E).choose

/-- The local generator b tensor x uses both existing sheafification units and the
normalized object identification of the existing scalar functor.
Source: the model formula in the node (blueprint: lem-pod-completed-model-sections-transport).
-/
def generator (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))).obj.obj U)
    (x : N) : ((realization D l E).obj N).val.obj U :=
  (eqToHom ((scalarData D l E).choose_spec.choose _).symm).val.app U
    (SheafOfModules.scalarExtensionRingIsoTmul.{u + 1, u, u + 1, u + 1}
      (coefficient D l E) ((constant D l E).obj N) U
      ((toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
        (Scheme.proEtaleConstantModulePresheafOfUniverses (Spec (.of D.k)).ProEt
          (Padic.coefficientExtensionIntegers l E)
          ((ModuleCat.restrictScalars
            (ULift.ringEquiv : ULift.{u + 1}
              (Padic.coefficientExtensionIntegers l E) ≃+* _).toRingHom).obj N)).presheaf).app U x)
      b)

private instance scalarSheafification_additive
    {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {R₀ : Tᵒᵖ ⥤ RingCat.{u + 1}} {R₁ : Sheaf J RingCat.{u + 1}}
    (a : R₀ ⟶ R₁.obj) [Presheaf.IsLocallyInjective J a]
    [Presheaf.IsLocallySurjective J a] :
    (PresheafOfModules.sheafification.{u + 1} a).Additive :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1} a).left_adjoint_additive

/-- Additivity of the specified completed constant model.
Source: model functoriality (blueprint: lem-pod-completed-model-sections-transport).
Proof: the constant presheaf and its sheafification add maps sectionwise; on tensors
extension sends b tensor x to b tensor f(x), which adds in f. The normalized
object transports preserve this identity. -/
theorem realization_additive : (realization D l E).Additive := by
  have : (scalarData D l E).choose.Additive :=
    (scalarData D l E).choose_spec.choose_spec.choose_spec.choose
  have : (siteConstantModulePresheafGeneral (C := (Spec (.of D.k)).ProEt)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).Additive := ⟨by intros; rfl⟩
  unfold realization constant
  infer_instance

/-- The additive structure just asserted.
Source: model functoriality (blueprint: lem-pod-completed-model-sections-transport). -/
instance realizationAdditive : (realization D l E).Additive := realization_additive D l E

/-- The termwise completed coefficient model.
Source: the model formula in the node (blueprint: lem-pod-completed-model-sections-transport).
-/
abbrev model := (realization D l E).mapHomologicalComplex (.up ℤ)

/-- Bounded finite-projective representatives, rather than a choice of a perfect object.
Source: def-pc-perfect-ring-complex (blueprint: lem-pod-completed-model-sections-transport).
-/
def IsModel (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    : Prop :=
  (∃ a b : ℤ, A.IsStrictlyGE a ∧ A.IsStrictlyLE b) ∧
    ∀ i : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (A.X i) ∧
      Module.Finite (Padic.coefficientExtensionIntegers l E) (A.X i)

private theorem generator_natural
    {M N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)} (f : M ⟶ N)
    (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))).obj.obj U)
    (x : M) :
    ((realization D l E).map f).val.app U (generator D l E M U b x) =
      generator D l E N U b (f x) := by
  dsimp only [generator, realization, Functor.comp_map]
  let a := coefficient D l E
  let F := (scalarData D l E).choose
  let hobj := (scalarData D l E).choose_spec.choose
  let g := (constant D l E).map f
  let x₀ := ((toSheafify (Scheme.ProEt.topology (Spec (.of D.k)))
    (Scheme.proEtaleConstantModulePresheafOfUniverses (Spec (.of D.k)).ProEt
      (Padic.coefficientExtensionIntegers l E)
      ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{u + 1}
          (Padic.coefficientExtensionIntegers l E) ≃+* _).toRingHom).obj M)).presheaf).app U x)
  have ht := witnessTensor_naturality a F hobj
    (scalarData D l E).choose_spec.choose_spec.choose g U b x₀
  let G := ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E) ≃+* _).toRingHom ⋙
    siteConstantModulePresheafGeneral (C := (Spec (.of D.k)).ProEt)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  have hn := toSheafify_naturality (Scheme.ProEt.topology (Spec (.of D.k)))
    ((PresheafOfModules.toPresheaf _).map (G.map f))
  exact ht.trans (congrArg (fun z ↦ (eqToHom (hobj _).symm).val.app U
    (SheafOfModules.ScalarComparisonProof.tensorSection a _ U b z))
      (ConcreteCategory.congr_hom (NatTrans.congr_app hn U) x).symm)

private theorem coefficient_normalization :
    (sheafCompose (Scheme.ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficient D l E) =
        integralConstantToCompletion l E (Spec (.of D.k)) := by
  change (sheafCompose _ _).map ((sheafCompose _ _).preimage _) = _
  rw [Functor.map_preimage]
  rfl

private theorem tensorUnit_apply
    {A : Type u} {R S : Type (u + 1)}
    [CommRing A] [CommRing R] [CommRing S]
    (g : R →+* S) (en : A ≃+* R) (ej : A ≃+* S)
    (hs : ∀ a, ej ((RingHom.id A) a) = g (en a))
    (N : ModuleCat.{u + 1} R)
    (x : (ModuleCat.restrictScalars en.toRingHom).obj N) :
    ((ModuleCat.extendScalarsId.{u, u + 1} A).symm.app _ ≪≫
      pointTensorSquareIso (RingHom.id A) g en ej hs N).hom x =
        (ej 1 ⊗ₜ[R, g] x) := by
  rfl

private theorem sheafificationFinal_apply (k : Type u) [Field k] [IsAlgClosed k]
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) RingCat.{u + 1})
    (P : PresheafOfModules.{u + 1} R.obj)
    (x : P.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :
    (sheafificationFinalIso k R P).hom x =
      (toSheafify (Scheme.ProEt.topology (Spec (.of k))) P.presheaf).app
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x := by
  rfl

attribute [local irreducible] pointTensorSquareIso sheafificationFinalIso

private theorem termUnit_exists (N : ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E)) :
    ∃ e : N ≅ (pointCompletedSections D.k l E).obj ((realization D l E).obj N),
      ∀ x : N, e.hom x = generator D l E N
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x := by
  dsimp only [generator, realization, Functor.comp_obj]
  let Y := Spec (.of D.k)
  let U := op (Scheme.ProEt.mk (𝟙 Y))
  let A := Padic.coefficientExtensionIntegers l E
  let C := (constant D l E).obj N
  let en : A ≃+* (integralConstantRingOfUniverses l E Y).obj.obj U :=
    ULift.ringEquiv.symm.trans (constantSectionEquiv D.k A)
  let ej := RingEquiv.ofBijective (pointCompletedConstant D.k l E)
    (pointCompletedConstant_bijective D.k l E)
  let a := coefficient D l E
  have hs (x : A) : ej ((RingHom.id A) x) = (a.hom.app U).hom (en x) := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (coefficient_normalization D l E)) U)
      (en x)
    exact h.symm
  let := (Scheme.proEtaleConstantRingUnit_locallyBijectiveOfUniverses Y A).1
  let := (Scheme.proEtaleConstantRingUnit_locallyBijectiveOfUniverses Y A).2
  let α := Functor.whiskerRight (toSheafify (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let P := Scheme.proEtaleConstantModulePresheafOfUniverses Y.ProEt A
    ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom).obj N)
  let η := ((PresheafOfModules.sheafificationAdjunction
    (J := Scheme.ProEt.topology Y) (R := integralConstantRingOfUniverses l E Y) α).unit.app P).app U
  let f : N ⟶ (ModuleCat.restrictScalars en.toRingHom).obj (C.val.obj U) :=
    ModuleCat.ofHom (X := N)
      (Y := (ModuleCat.restrictScalars en.toRingHom).obj (C.val.obj U))
      { toFun := fun x ↦ η x
        map_add' := fun x y ↦ η.hom.map_add x y
        map_smul' := fun x y ↦ η.hom.map_smul (ULift.up x) y }
  have hf : Function.Bijective f :=
    AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _)
      (Scheme.proEtaleConstantModulePresheafOfUniverses Y.ProEt A
        ((ModuleCat.restrictScalars
          (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom).obj N)).presheaf
  let e₀ := (LinearEquiv.ofBijective f.hom hf).toModuleIso
  let e := e₀ ≪≫ (ModuleCat.extendScalarsId.{u, u + 1} A).symm.app _ ≪≫
    pointTensorSquareIso (RingHom.id A) (a.hom.app U).hom en ej hs (C.val.obj U) ≪≫
    (ModuleCat.restrictScalars ej.toRingHom).mapIso
      (sheafificationFinalIso D.k
        (completedIntegralCoefficientSheafUnrestricted l E Y)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C)) ≪≫
    (pointCompletedSections D.k l E).mapIso
      (eqToIso ((scalarData D l E).choose_spec.choose C)).symm
  refine ⟨e, ?_⟩
  intro x
  calc
    e.hom x = (eqToHom ((scalarData D l E).choose_spec.choose C).symm).val.app U
        ((sheafificationFinalIso D.k
          (completedIntegralCoefficientSheafUnrestricted l E Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C)).hom
          (((ModuleCat.extendScalarsId.{u, u + 1} A).symm.app _ ≪≫
            pointTensorSquareIso (RingHom.id A) (a.hom.app U).hom en ej hs
              (C.val.obj U)).hom (η x))) := rfl
    _ = (eqToHom ((scalarData D l E).choose_spec.choose C).symm).val.app U
        ((sheafificationFinalIso D.k
          (completedIntegralCoefficientSheafUnrestricted l E Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C)).hom
          (ej 1 ⊗ₜ[_, (a.hom.app U).hom] (η x))) :=
      congrArg (fun z ↦
        (eqToHom ((scalarData D l E).choose_spec.choose C).symm).val.app U
          ((sheafificationFinalIso D.k
            (completedIntegralCoefficientSheafUnrestricted l E Y)
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C)).hom z))
        (tensorUnit_apply (a.hom.app U).hom en ej hs (C.val.obj U) (η x))
    _ = (eqToHom ((scalarData D l E).choose_spec.choose C).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C).presheaf).app U
          (ej 1 ⊗ₜ[_, (a.hom.app U).hom] (η x))) :=
      congrArg ((eqToHom ((scalarData D l E).choose_spec.choose C).symm).val.app U)
        (sheafificationFinal_apply D.k
          (completedIntegralCoefficientSheafUnrestricted l E Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C)
          (ej 1 ⊗ₜ[_, (a.hom.app U).hom] (η x)))
    _ = _ := by
      exact congrArg (fun b ↦
        (eqToHom ((scalarData D l E).choose_spec.choose C).symm).val.app U
          ((toSheafify (Scheme.ProEt.topology Y)
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a C).presheaf).app U
            (b ⊗ₜ[_, (a.hom.app U).hom] (η x)))) (map_one ej)

/-- The unit is the unique chain isomorphism sending x to 1 tensor x.
Source: completed model sections, Step 1
(blueprint: lem-pod-completed-model-sections-transport).
Proof: sheafification preserves the value at the final algebraically closed point.
The constant coefficient and completed coefficient section rings both identify with
the integral coefficient ring. Their commuting tensor square therefore identifies
sections of each realized term with that term, sending x to 1 tensor x. Naturality
makes these component isomorphisms commute with differentials. Their prescribed
values on every element determine the resulting chain isomorphism uniquely. -/
theorem unit_existsUnique
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (_hA : IsModel l E A) :
    ∃! e : A ≅ ((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ)).obj
        ((model D l E).obj A),
      ∀ (i : ℤ) (x : A.X i), (e.hom.f i) x = generator D l E (A.X i)
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x := by
  classical
  choose e he using fun i : ℤ ↦ termUnit_exists D l E (A.X i)
  let eA : A ≅ ((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ)).obj
      ((model D l E).obj A) :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((realization D l E).map (A.d i j)).val.app _ ((e i).hom x) =
        (e j).hom ((A.d i j) x)
      rw [he i x, he j ((A.d i j) x), generator_natural])
  refine ⟨eA, ?_, ?_⟩
  · intro i x
    exact he i x
  · intro e' he'
    apply Iso.ext
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (he' i x).trans (he i x).symm

/-- The specified unit, chosen only from its unique normalized characterization.
Source: completed model sections, Step 1
(blueprint: lem-pod-completed-model-sections-transport). -/
def unit
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A) := (unit_existsUnique D l E A hA).exists.choose

/-- The very same unit in the derived category, with the standard exact-functor factors.
Source: completed model sections, Step 1
(blueprint: lem-pod-completed-model-sections-transport). -/
def unitD
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A) :
    DerivedCategory.Q.obj A ≅ (pointCompletedDerivedSections D.k l E).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) :=
  DerivedCategory.Q.mapIso (unit D l E A hA) ≪≫
    ((pointCompletedSections D.k l E).mapDerivedCategoryFactors.app ((model D l E).obj A)).symm

private theorem unit_natural
    (A B : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A) (hB : IsModel l E B) (p : A ⟶ B) :
    p ≫ (unit D l E B hB).hom = (unit D l E A hA).hom ≫
      ((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ)).map
        ((model D l E).map p) := by
  have heA := (unit_existsUnique D l E A hA).exists.choose_spec
  have heB := (unit_existsUnique D l E B hB).exists.choose_spec
  change ∀ (i : ℤ) (x : A.X i), (unit D l E A hA).hom.f i x =
    generator D l E (A.X i) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x at heA
  change ∀ (i : ℤ) (x : B.X i), (unit D l E B hB).hom.f i x =
    generator D l E (B.X i) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x at heB
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (unit D l E B hB).hom.f i (p.f i x) =
    ((realization D l E).map (p.f i)).val.app _ ((unit D l E A hA).hom.f i x)
  rw [heA, heB, generator_natural]

private theorem unitD_natural
    (A B : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A) (hB : IsModel l E B) (p : A ⟶ B) :
    DerivedCategory.Q.map p ≫ (unitD D l E B hB).hom =
      (unitD D l E A hA).hom ≫ (pointCompletedDerivedSections D.k l E).map
        (DerivedCategory.Q.map ((model D l E).map p)) := by
  simp only [unitD, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
  rw [← DerivedCategory.Q.map_comp_assoc, unit_natural D l E A B hA hB p,
    DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (pointCompletedSections D.k l E).mapDerivedCategoryFactors.inv.naturality
    ((model D l E).map p)

private theorem realized_map_eq
    (A B : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    [A.IsKProjective] (f g : A ⟶ B)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    DerivedCategory.Q.map ((model D l E).map f) =
      DerivedCategory.Q.map ((model D l E).map g) := by
  have hh : Nonempty (Homotopy f g) := by
    refine ⟨HomotopyCategory.homotopyOfEq f g
      ((CochainComplex.IsKProjective.Qh_map_bijective A _).1 ?_)⟩
    have hf := (DerivedCategory.quotientCompQhIso
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).hom.naturality f
    have hg := (DerivedCategory.quotientCompQhIso
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).hom.naturality g
    dsimp at hf hg
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).hom.app B), hf, hg, h]
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((realization D l E).mapHomotopy hh.some)

/-- Every derived map of perfect representatives has a unique realized derived map,
independently of its chain representative; its sections commute with the actual units.
Source: completed model transport, Step 5
(blueprint: lem-pod-completed-model-sections-transport).
Proof: bounded projectives are K-projective, so the recorded derived-map-representative
lemma supplies a chain map unique up to homotopy. The additive realization preserves
homotopies termwise. Thus localization gives one uniquely specified map. The unit
formula is natural for chain maps; applying localization gives the displayed equation. -/
theorem derivedMap_existsUnique
    (A A' : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A) (hA' : IsModel l E A')
    (p : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj A') :
    ∃! f : DerivedCategory.Q.obj ((model D l E).obj A) ⟶
        DerivedCategory.Q.obj ((model D l E).obj A'),
      (∃ p₀ : A ⟶ A', DerivedCategory.Q.map p₀ = p ∧
        DerivedCategory.Q.map ((model D l E).map p₀) = f) ∧
      p ≫ (unitD D l E A' hA').hom =
        (unitD D l E A hA).hom ≫ (pointCompletedDerivedSections D.k l E).map f := by
  obtain ⟨_, b, _, hb⟩ := hA.1
  let : A.IsStrictlyLE b := hb
  let (i : ℤ) : Module.Projective (Padic.coefficientExtensionIntegers l E) (A.X i) :=
    (hA.2 i).1
  let (i : ℤ) : CategoryTheory.Projective (A.X i) := inferInstance
  let : A.IsKProjective := CochainComplex.isKProjective_of_projective A b
  obtain ⟨p₀, hp₀⟩ := CochainComplex.IsKProjective.exists_Q_map_eq A A' p
  refine ⟨DerivedCategory.Q.map ((model D l E).map p₀), ?_, ?_⟩
  · refine ⟨⟨p₀, hp₀, rfl⟩, ?_⟩
    rw [← hp₀]
    exact unitD_natural D l E A A' hA hA' p₀
  · rintro f ⟨⟨q, hq, hqf⟩, _⟩
    rw [← hqf]
    exact realized_map_eq D l E A A' q p₀ (hq.trans hp₀.symm)

/-- The unique realized derived map; no chain representative is selected as data.
Source: completed model transport, Step 5
(blueprint: lem-pod-completed-model-sections-transport). -/
def derivedMap
    (A A' : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A) (hA' : IsModel l E A')
    (p : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj A') :=
  (derivedMap_existsUnique D l E A A' hA hA' p).exists.choose

attribute [local irreducible] realization generator constant coefficient unitD

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The local-generator characterization of the coefficient-sheaf realization of v.
All opens of the small pro-etale site and all local scalar factors are quantified.
Source: completed model transport, hypothesis on g
(blueprint: lem-pod-completed-model-sections-transport). -/
def Realizes
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (v : ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
    (g : (completedOrdinaryScalarComplex l E L ι (Spec (.of D.k))).obj
      ((model D l E).obj A) ⟶ (model D l L).obj C) : Prop :=
  ∀ (i : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))).obj.obj U)
    (b' : (completedIntegralCommRingSheafUnrestricted l L (Spec (.of D.k))).obj.obj U)
    (x : A.X i),
    (g.f i).val.app U
      (completedScalarTensorSection l E L ι (Spec (.of D.k))
        (((model D l E).obj A).X i) U b' (generator D l E (A.X i) U b x)) =
      generator D l L (C.X i) U
        ((completedCoefficientMap l E L ι (Spec (.of D.k))).hom.app U b * b')
        ((v.f i) ((1 : Padic.coefficientExtensionIntegers l L)
          ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] x))

/-- Passage from the specified cochain realization to its actual derived map, using
exactly the counit of the ordinary derived extension.
Source: completed model transport, Step 2
(blueprint: lem-pod-completed-model-sections-transport). -/
def realizedMap
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (g : (completedOrdinaryScalarComplex l E L ι (Spec (.of D.k))).obj
      ((model D l E).obj A) ⟶ (model D l L).obj C) :=
  completedScalarCounit l E L ι (Spec (.of D.k)) ((model D l E).obj A) ≫
    DerivedCategory.Q.map g

/-- The left side of the displayed transport equality, in Mathlib's scalar-first order.
Source: completed model transport, displayed equality
(blueprint: lem-pod-completed-model-sections-transport). -/
def transport (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (g : (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) ⟶
        DerivedCategory.Q.obj ((model D l L).obj C)) :
    (pointIntegralModuleDerivedTensor l E L ι).obj (DerivedCategory.Q.obj A) ⟶
      DerivedCategory.Q.obj C :=
  (pointIntegralModuleDerivedTensor l E L ι).map (unitD D l E A hA).hom ≫
    (pointSectionsScalarExtensionIso l E L ι D hl _ hK).inv ≫
      (pointCompletedDerivedSections D.k l L).map
        ((pointConstructibleCompletionIso l E L ι D hl _ hK).inv ≫ g) ≫
          (unitD D l L C hC).inv

/-- Transport through the specified rational sections comparison, with the rationalized
model units. This uses the field scalar functor on the source, rather than merely
applying rationalization to an integral equality.
Source: completed model transport, Step 7
(blueprint: lem-pod-completed-model-sections-transport). -/
def rationalTransport (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (g : (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) ⟶
        DerivedCategory.Q.obj ((model D l L).obj C)) :=
  (pointCoefficientFieldDerivedTensor l E L ι).map
      ((pointModuleDerivedRationalization l E).map (unitD D l E A hA).hom) ≫
    (pointRationalSectionsScalarExtensionIso l E L ι D hl _ hK).inv ≫
    (pointModuleDerivedRationalization l L).map
      ((pointCompletedDerivedSections D.k l L).map
        ((pointConstructibleCompletionIso l E L ι D hl _ hK).inv ≫ g)) ≫
    (pointModuleDerivedRationalization l L).map (unitD D l L C hC).inv

private theorem transport_formula (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (g : (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) ⟶
        DerivedCategory.Q.obj ((model D l L).obj C)) :
    transport D l E L ι hl A C hA hC hK g =
      (pointIntegralModuleDerivedTensor l E L ι).map (unitD D l E A hA).hom ≫
        (pointDerivedSectionsTensor D.k l E L ι).hom.app
          (DerivedCategory.Q.obj ((model D l E).obj A)) ≫
        (pointCompletedDerivedSections D.k l L).map g ≫ (unitD D l L C hC).inv := by
  simp only [transport, pointSectionsScalarExtensionIso, Iso.symm_inv, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id_assoc]

private theorem rationalTransport_formula (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (g : (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) ⟶
        DerivedCategory.Q.obj ((model D l L).obj C)) :
    rationalTransport D l E L ι hl A C hA hC hK g =
      (pointDerivedTensorRationalization.{u} l E L ι).inv.app
        (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj A) ≫
        (pointModuleDerivedRationalization.{u} l L).map
          (transport D l E L ι hl A C hA hC hK g) := by
  simp only [rationalTransport, pointRationalSectionsScalarExtensionIso,
    Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, transport, Functor.map_comp,
    Category.assoc]
  have hn := (pointDerivedTensorRationalization.{u} l E L ι).inv.naturality
    (unitD D l E A hA).hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- The derived class of v, using the standard module-tensor localization factors.
Source: completed model transport, displayed equality
(blueprint: lem-pod-completed-model-sections-transport). -/
def moduleMap
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (v : ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C) :=
  (pointIntegralModuleTensor l E L ι).mapDerivedCategoryFactors.hom.app A ≫
    DerivedCategory.Q.map v

/-- The rationalized module map, whose source is identified by the specified
beta = pointDerivedTensorRationalization, including its direction.
Source: completed model transport, Step 7
(blueprint: lem-pod-completed-model-sections-transport). -/
def rationalModuleMap
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (v : ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C) :=
  (pointDerivedTensorRationalization l E L ι).inv.app (DerivedCategory.Q.obj A) ≫
    (pointModuleDerivedRationalization l L).map (moduleMap l E L ι A C v)

/-- The cochain transport obtained before inserting completion, with the actual theta.
Source: completed model transport, Steps 2--4
(blueprint: lem-pod-completed-model-sections-transport). -/
def chainTransport
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (g : (completedOrdinaryScalarComplex l E L ι (Spec (.of D.k))).obj
      ((model D l E).obj A) ⟶ (model D l L).obj C) :
    ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C :=
  ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).map
      (unit D l E A hA).hom ≫
    (NatIso.mapHomologicalComplex (pointSectionsTensor D.k l E L ι) (.up ℤ)).hom.app
      ((model D l E).obj A) ≫
    ((pointCompletedSections D.k l L).mapHomologicalComplex (.up ℤ)).map g ≫
      (unit D l L C hC).inv

/-- The equivalent cochain equality, pure-tensor calculation, and precise cancellation
identity for the specified phi and chi.
Source: completed model transport, Steps 2--4
(blueprint: lem-pod-completed-model-sections-transport).
Proof: insert the definition of phi, cancel sections of chi with sections of its inverse,
and evaluate theta on a tensor of a constant generator and a scalar. The local formula
for g and balancing give e_C(v(x tensor a)); the inverse unit removes e_C. Pure tensors
generate, so the cochain maps agree, not just their values on cohomology. -/
theorem chainTransport_spec (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (v : ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
    (g : (completedOrdinaryScalarComplex l E L ι (Spec (.of D.k))).obj
      ((model D l E).obj A) ⟶ (model D l L).obj C)
    (_hg : Realizes D l E L ι A C v g) :
    chainTransport D l E L ι A C hA hC g = v ∧
    (∀ (i : ℤ) (x : A.X i) (a : Padic.coefficientExtensionIntegers l L),
      ((chainTransport D l E L ι A C hA hC g).f i)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] x) =
        (v.f i) (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] x)) ∧
    (pointSectionsScalarExtensionIso l E L ι D hl _ hK).inv =
      (pointDerivedSectionsTensor D.k l E L ι).hom.app
        (DerivedCategory.Q.obj ((model D l E).obj A)) ≫
      (pointCompletedDerivedSections D.k l L).map
        ((pointConstructibleCompletionIso l E L ι D hl _ hK).hom) := by
  have heA := (unit_existsUnique D l E A hA).exists.choose_spec
  have heC := (unit_existsUnique D l L C hC).exists.choose_spec
  change ∀ (i : ℤ) (x : A.X i), (unit D l E A hA).hom.f i x =
    generator D l E (A.X i) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x at heA
  change ∀ (i : ℤ) (x : C.X i), (unit D l L C hC).hom.f i x =
    generator D l L (C.X i) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x at heC
  have hc : chainTransport D l E L ι A C hA hC g = v := by
    rw [← cancel_mono (unit D l L C hC).hom]
    simp only [chainTransport, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (g.f i).val.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
      ((pointSectionsTensor D.k l E L ι).hom.app (((model D l E).obj A).X i)
        ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
          integralScalarIntegerInclusion l E L ι] ((unit D l E A hA).hom.f i x))) =
      (unit D l L C hC).hom.f i
        ((v.f i) ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
          integralScalarIntegerInclusion l E L ι] x))
    rw [heA, heC]
    have ht := (pointSectionsTensor_existsUnique D.k l E L ι).exists.choose_spec
      (((model D l E).obj A).X i) 1
      (generator D l E (A.X i) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x)
    change (pointSectionsTensor D.k l E L ι).hom.app (((model D l E).obj A).X i)
      ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
        integralScalarIntegerInclusion l E L ι]
        (generator D l E (A.X i) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x)) = _ at ht
    rw [ht]
    simpa only [map_one, one_mul] using _hg i
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 1 x
  refine ⟨hc, ?_, ?_⟩
  · intro i x a
    rw [hc]
  · rfl


private theorem sectionsTensor_counit_factor
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (pointDerivedSectionsTensor D.k l E L ι).hom.app (DerivedCategory.Q.obj K) ≫
      (pointCompletedDerivedSections D.k l L).map
        (completedScalarCounit l E L ι (Spec (.of D.k)) K) ≫
      (pointCompletedSections D.k l L).mapDerivedCategoryFactors.hom.app
        ((completedOrdinaryScalarComplex l E L ι (Spec (.of D.k))).obj K) =
    (pointIntegralModuleDerivedTensor l E L ι).map
      ((pointCompletedSections D.k l E).mapDerivedCategoryFactors.hom.app K) ≫
      (pointIntegralModuleTensor l E L ι).mapDerivedCategoryFactors.hom.app
        (((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pointSectionsTensor D.k l E L ι) (.up ℤ)).hom.app K) := by
  dsimp only [completedOrdinaryScalarComplex]
  have hd := (pointOrdinaryDerivedComparison_existsUnique D.k l E L ι).exists.choose_spec K
  change (pointOrdinaryDerivedComparison D.k l E L ι).hom.app _ ≫ _ = _ at hd
  rw [← hd, Functor.map_comp]
  simp only [pointDerivedSectionsTensor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  have hc : (pointCompletedDerivedSections D.k l L).map
      ((pointOrdinaryDerivedComparison D.k l E L ι).inv.app (DerivedCategory.Q.obj K)) ≫
      (pointCompletedDerivedSections D.k l L).map
        ((pointOrdinaryDerivedComparison D.k l E L ι).hom.app (DerivedCategory.Q.obj K)) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso
    (pointCompletedSections D.k l E) (pointIntegralModuleTensor l E L ι)).hom.app
      (DerivedCategory.Q.obj K))).mp
  rw [Iso.hom_inv_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  rfl

/-- Sections recover the specified model map, as an actual equality in D(O_L).
Source: blueprint lem-pod-point-dualizing-complex.proof.md, coefficient-ring sentence
(blueprint: lem-pod-completed-model-sections-transport).
Proof: use the splitting argument for the two normalized units (Step 1), and the
counit-normalized descent of theta (Step 2). Substitute phi inverse = Gamma(chi) theta
and cancel the adjacent chi inverse and chi (Step 3). On a tensor x tensor a the
remaining composite gives a times v(x tensor 1) = v(x tensor a), by the local-generator
hypothesis with b = 1 (Step 4). Pure tensors generate, hence chain maps and their
classes in D(O_L) agree. For Step 7 expand rational phi as rationalized integral
phi followed by beta. Naturality of beta moves the rationalized source unit across it;
the result is beta inverse followed by rationalized v. The assertion is equality of
morphisms in the derived category, before taking cohomology. -/
theorem transport_eq (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (_hH : boundedConstructibleDerivedCompleteIntegral D l hl L (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l L).obj C)))
    (v : ((pointIntegralModuleTensor l E L ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
    (g : (completedOrdinaryScalarComplex l E L ι (Spec (.of D.k))).obj
      ((model D l E).obj A) ⟶ (model D l L).obj C)
    (_hg : Realizes D l E L ι A C v g) :
    transport D l E L ι hl A C hA hC hK (realizedMap D l E L ι A C g) =
      moduleMap l E L ι A C v ∧
    rationalTransport D l E L ι hl A C hA hC hK (realizedMap D l E L ι A C g) =
      rationalModuleMap l E L ι A C v := by
  have hc := (chainTransport_spec D l E L ι hl A C hA hC hK v g _hg).1
  have ht := sectionsTensor_counit_factor D l E L ι ((model D l E).obj A)
  have hi : transport D l E L ι hl A C hA hC hK (realizedMap D l E L ι A C g) =
      moduleMap l E L ι A C v := by
    rw [transport_formula]
    simp only [realizedMap, unitD, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Functor.map_comp, Category.assoc]
    erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    rw [reassoc_of% ht]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id, Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    simp only [← Functor.map_comp, ← hc, chainTransport, moduleMap, Category.assoc]
  refine ⟨hi, ?_⟩
  rw [rationalTransport_formula, hi]
  rfl

/-- Naturality in both perfect models for arbitrary derived maps.
Source: completed model transport, Step 5
(blueprint: lem-pod-completed-model-sections-transport).
Proof: represent p and q by chain maps using the K-projective representative lemma.
The realized derived maps are independent of that choice by derivedMap_existsUnique.
Naturality of the actual units, theta, chi and phi moves p and q through the displayed
composite; the adjacent unit inverses cancel. For the rational assertion use naturality
of the field tensor functor and the specified rational phi, or expand it and use
naturality of beta to move the arbitrary derived source map across its inverse. The
result has field tensor of rationalized p on the source and rationalized q on the target. -/
theorem transport_naturality (hl : l ≠ D.p)
    (A A' : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C C' : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hA' : IsModel l E A')
    (hC : IsModel l L C) (hC' : IsModel l L C')
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (hK' : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A')))
    (p : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A)
    (q : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj C')
    (g : (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) ⟶
        DerivedCategory.Q.obj ((model D l L).obj C)) :
    (transport D l E L ι hl A' C' hA' hC' hK'
      ((completedDerivedScalarExtension l E L ι (Spec (.of D.k))).map
        (derivedMap D l E A' A hA' hA p) ≫ g ≫ derivedMap D l L C C' hC hC' q) =
      (pointIntegralModuleDerivedTensor l E L ι).map p ≫
        transport D l E L ι hl A C hA hC hK g ≫ q) ∧
    rationalTransport D l E L ι hl A' C' hA' hC' hK'
      ((completedDerivedScalarExtension l E L ι (Spec (.of D.k))).map
        (derivedMap D l E A' A hA' hA p) ≫ g ≫ derivedMap D l L C C' hC hC' q) =
      (pointCoefficientFieldDerivedTensor l E L ι).map
          ((pointModuleDerivedRationalization l E).map p) ≫
        rationalTransport D l E L ι hl A C hA hC hK g ≫
        (pointModuleDerivedRationalization l L).map q := by
  have hp := (derivedMap_existsUnique D l E A' A hA' hA p).exists.choose_spec.2
  have hq := (derivedMap_existsUnique D l L C C' hC hC' q).exists.choose_spec.2
  change p ≫ (unitD D l E A hA).hom =
    (unitD D l E A' hA').hom ≫
      (pointCompletedDerivedSections D.k l E).map
        (derivedMap D l E A' A hA' hA p) at hp
  change q ≫ (unitD D l L C' hC').hom =
    (unitD D l L C hC).hom ≫
      (pointCompletedDerivedSections D.k l L).map
        (derivedMap D l L C C' hC hC' q) at hq
  have hqi : (pointCompletedDerivedSections D.k l L).map
      (derivedMap D l L C C' hC hC' q) ≫ (unitD D l L C' hC').inv =
      (unitD D l L C hC).inv ≫ q := by
    rw [← cancel_epi (unitD D l L C hC).hom, ← reassoc_of% hq]
    simp
  have hi : transport D l E L ι hl A' C' hA' hC' hK'
      ((completedDerivedScalarExtension l E L ι (Spec (.of D.k))).map
        (derivedMap D l E A' A hA' hA p) ≫ g ≫ derivedMap D l L C C' hC hC' q) =
      (pointIntegralModuleDerivedTensor l E L ι).map p ≫
        transport D l E L ι hl A C hA hC hK g ≫ q := by
    simp only [transport_formula, Functor.map_comp, Category.assoc]
    rw [hqi]
    have hn := (pointDerivedSectionsTensor D.k l E L ι).hom.naturality
      (derivedMap D l E A' A hA' hA p)
    simp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, ← Functor.map_comp_assoc, ← hp, Functor.map_comp_assoc]
  refine ⟨hi, ?_⟩
  simp only [rationalTransport_formula, hi, Functor.map_comp, Category.assoc]
  have hn := (pointDerivedTensorRationalization l E L ι).inv.naturality p
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]


/-- Identity normalization uses the specified sheaf and module multiplication maps.
Source: completed model transport, Step 6
(blueprint: lem-pod-completed-model-sections-transport).
Proof: theta sends n tensor a to an, and the identity phi equation identifies the
completed comparison with this multiplication. Substitute into transport; the two
normalized model units cancel by naturality. For the rational assertion expand rational
phi and use the beta unit law: beta followed by field multiplication equals rationalized
integral multiplication. Thus the result is the specified field unit. -/
theorem transport_identity (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hA : IsModel l E A)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A))) :
    (transport D l E E (AlgHom.id ℚ_[l] E) hl A A hA hA hK
      ((pointDerivedTensorUnit D.k l E).hom.app
        (DerivedCategory.Q.obj ((model D l E).obj A))) =
      (pointIntegralModuleDerivedUnit l E).hom.app (DerivedCategory.Q.obj A)) ∧
    rationalTransport D l E E (AlgHom.id ℚ_[l] E) hl A A hA hA hK
      ((pointDerivedTensorUnit D.k l E).hom.app
        (DerivedCategory.Q.obj ((model D l E).obj A))) =
      (pointCoefficientFieldDerivedUnit l E).hom.app
        ((pointModuleDerivedRationalization l E).obj (DerivedCategory.Q.obj A)) := by
  have hu := pointDerivedSectionsUnit D.k l E
    (DerivedCategory.Q.obj ((model D l E).obj A))
  have hi : transport D l E E (AlgHom.id ℚ_[l] E) hl A A hA hA hK
      ((pointDerivedTensorUnit D.k l E).hom.app
        (DerivedCategory.Q.obj ((model D l E).obj A))) =
      (pointIntegralModuleDerivedUnit l E).hom.app (DerivedCategory.Q.obj A) := by
    rw [transport_formula, ← hu]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% (pointIntegralModuleDerivedUnit l E).hom.naturality
      (unitD D l E A hA).hom]
    simp
  refine ⟨hi, ?_⟩
  rw [rationalTransport_formula, hi, ← pointRationalizationUnit l E]
  simp

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)

/-- Tower compatibility, explicitly using the specified integral associator and module
associator. The input to the direct transport is the ordinary map obtained by inserting
chi at the source and its two inverse comparisons at the intermediate stages.
Source: completed model transport, Step 6
(blueprint: lem-pod-completed-model-sections-transport).
Proof: expand the integral associator as the chi-conjugate of the ordinary associator.
The ordinary sections-tensor tower square sends ((n tensor a) tensor b) to n tensor ab.
Naturality moves each comparison past theta and cancels adjacent chi inverse and chi.
The intermediate normalized model units cancel, leaving exactly the module associator
and the two transports. For the rational assertion expand rational phi and use the beta
tower law: rationalized integral association followed by beta equals the two beta maps
followed by field association. The intermediate rationalized unit cancels, leaving the
specified field associator and the two rational transports. This includes repeated fields
and identity inclusions. -/
theorem transport_tower (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ℤ)
    (H : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l M)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C) (hH : IsModel l M H)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (hJ : boundedConstructibleDerivedCompleteIntegral D l hl L (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l L).obj C)))
    (g : (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l E).obj A)) ⟶
        DerivedCategory.Q.obj ((model D l L).obj C))
    (h : (completedDerivedScalarExtension l L M κ (Spec (.of D.k))).obj
      (DerivedCategory.Q.obj ((model D l L).obj C)) ⟶
        DerivedCategory.Q.obj ((model D l M).obj H)) :
    (transport D l E M (κ.comp ι) hl A H hA hH hK
      ((pointConstructibleCompletionIso l E M (κ.comp ι) D hl _ hK).hom ≫
        (pointIntegralScalarAssoc l E L ι M κ D hl _ hK).inv ≫
        (integralScalarExtension l L M κ (Spec (.of D.k))).map
          ((pointConstructibleCompletionIso l E L ι D hl _ hK).inv ≫ g) ≫
        (pointConstructibleCompletionIso l L M κ D hl _ hJ).inv ≫ h) =
      (pointIntegralModuleDerivedAssoc l E L ι M κ).inv.app (DerivedCategory.Q.obj A) ≫
        (pointIntegralModuleDerivedTensor l L M κ).map
          (transport D l E L ι hl A C hA hC hK g) ≫
        transport D l L M κ hl C H hC hH hJ h) ∧
    rationalTransport D l E M (κ.comp ι) hl A H hA hH hK
      ((pointConstructibleCompletionIso l E M (κ.comp ι) D hl _ hK).hom ≫
        (pointIntegralScalarAssoc l E L ι M κ D hl _ hK).inv ≫
        (integralScalarExtension l L M κ (Spec (.of D.k))).map
          ((pointConstructibleCompletionIso l E L ι D hl _ hK).inv ≫ g) ≫
        (pointConstructibleCompletionIso l L M κ D hl _ hJ).inv ≫ h) =
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).inv.app
          ((pointModuleDerivedRationalization l E).obj (DerivedCategory.Q.obj A)) ≫
        (pointCoefficientFieldDerivedTensor l L M κ).map
          (rationalTransport D l E L ι hl A C hA hC hK g) ≫
        rationalTransport D l L M κ hl C H hC hH hJ h := by
  let K := DerivedCategory.Q.obj ((model D l E).obj A)
  let hTK := integralScalarExtension_constructible D l hl E L ι (Spec (.of D.k)) ⟨K, hK⟩
  let φ₁ := pointSectionsScalarExtensionIso l E L ι D hl K hK
  let φ₂ := pointSectionsScalarExtensionIso l L M κ D hl _ hTK
  let φ₃ := pointSectionsScalarExtensionIso l E M (κ.comp ι) D hl K hK
  let am := (pointIntegralModuleDerivedAssoc l E L ι M κ).app
    ((pointCompletedDerivedSections D.k l E).obj K)
  let a := pointIntegralScalarAssoc l E L ι M κ D hl K hK
  let S := pointCompletedDerivedSections D.k l M
  let T := pointIntegralModuleDerivedTensor l L M κ
  have hs : S.mapIso a ≪≫ φ₃ = φ₂ ≪≫ T.mapIso φ₁ ≪≫ am := by
    apply Iso.ext
    exact pointScalarSectionsTower l E L ι M κ D hl K hK
  have ht := congrArg Iso.inv hs
  simp only [Iso.trans_inv, Functor.mapIso_inv] at ht
  let f := (pointConstructibleCompletionIso l E L ι D hl K hK).inv ≫ g
  let φC := pointSectionsScalarExtensionIso l L M κ D hl _ hJ
  have hn : φ₂.inv ≫ S.map
      ((integralScalarExtension l L M κ (Spec (.of D.k))).map f) =
      T.map ((pointCompletedDerivedSections D.k l L).map f) ≫ φC.inv := by
    apply (cancel_mono φC.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pointScalarSectionsNatural l L M κ D hl _ _ hTK hJ f]
    simp [φ₂, T]
  have hi : transport D l E M (κ.comp ι) hl A H hA hH hK
      ((pointConstructibleCompletionIso l E M (κ.comp ι) D hl _ hK).hom ≫
        a.inv ≫ (integralScalarExtension l L M κ (Spec (.of D.k))).map f ≫
        (pointConstructibleCompletionIso l L M κ D hl _ hJ).inv ≫ h) =
      (pointIntegralModuleDerivedAssoc l E L ι M κ).inv.app (DerivedCategory.Q.obj A) ≫
        T.map (transport D l E L ι hl A C hA hC hK g) ≫
        transport D l L M κ hl C H hC hH hJ h := by
    simp only [transport, Functor.map_comp, Category.assoc]
    simp only [Iso.map_inv_hom_id_assoc]
    rw [reassoc_of% ht, reassoc_of% hn]
    have ha := (pointIntegralModuleDerivedAssoc l E L ι M κ).inv.naturality
      (unitD D l E A hA).hom
    simp only [Functor.comp_map] at ha
    simp only [am, Iso.app_inv]
    erw [reassoc_of% ha]
    dsimp only [T, f, φ₁, φC, S, K]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨hi, ?_⟩
  simp only [rationalTransport_formula]
  rw [hi]
  simp only [Functor.map_comp, Category.assoc]
  have hb := pointRationalizationTower l E L ι M κ (DerivedCategory.Q.obj A)
  have hbi : (pointDerivedTensorRationalization l E M (κ.comp ι)).inv.app
        (DerivedCategory.Q.obj A) ≫
      (pointModuleDerivedRationalization l M).map
        ((pointIntegralModuleDerivedAssoc l E L ι M κ).inv.app (DerivedCategory.Q.obj A)) =
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).inv.app
        ((pointModuleDerivedRationalization l E).obj (DerivedCategory.Q.obj A)) ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        ((pointDerivedTensorRationalization l E L ι).inv.app (DerivedCategory.Q.obj A)) ≫
      (pointDerivedTensorRationalization l L M κ).inv.app
        ((pointIntegralModuleDerivedTensor l E L ι).obj (DerivedCategory.Q.obj A)) := by
    have he : (pointModuleDerivedRationalization l M).mapIso
        ((pointIntegralModuleDerivedAssoc l E L ι M κ).app (DerivedCategory.Q.obj A)) ≪≫
          (pointDerivedTensorRationalization l E M (κ.comp ι)).app
            (DerivedCategory.Q.obj A) =
      (pointDerivedTensorRationalization l L M κ).app
        ((pointIntegralModuleDerivedTensor l E L ι).obj (DerivedCategory.Q.obj A)) ≪≫
      (pointCoefficientFieldDerivedTensor l L M κ).mapIso
        ((pointDerivedTensorRationalization l E L ι).app (DerivedCategory.Q.obj A)) ≪≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).app
        ((pointModuleDerivedRationalization l E).obj (DerivedCategory.Q.obj A)) := by
      apply Iso.ext
      exact hb
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
      congrArg Iso.inv he
  rw [reassoc_of% hbi]
  have hbN := (pointDerivedTensorRationalization l L M κ).inv.naturality
    (transport D l E L ι hl A C hA hC hK g)
  simp only [Functor.comp_map] at hbN
  rw [reassoc_of% hbN]

/-- Convert the two constructibility hypotheses to the pointwise derived interface
before specializing the coefficient fields. -/
private theorem transport_sf_eq (hl : l ≠ D.p)
    (A : CochainComplex (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l L)) ℤ)
    (hA : IsModel l E A) (hC : IsModel l L C)
    (hK : sfIntegralConstructible l E (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l E).obj A)))
    (_hH : sfIntegralConstructible l L (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l L).obj C)))
    (v : ((pointIntegralModuleTensor l E L
      ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
    (g : (completedOrdinaryScalarComplex l E L
      ι (Spec (.of D.k))).obj
        ((model D l E).obj A) ⟶ (model D l L).obj C)
    (_hg : Realizes D l E L ι A C v g) :
    transport D l E L ι hl A C hA hC
      ((pointIntegralConstructible_iff l E D hl _).mpr hK)
      (realizedMap D l E L ι A C g) =
        moduleMap l E L ι A C v ∧
    rationalTransport D l E L ι hl A C hA hC
      ((pointIntegralConstructible_iff l E D hl _).mpr hK)
      (realizedMap D l E L ι A C g) =
      rationalModuleMap l E L ι A C v := by
  exact transport_eq D l E L ι hl A C hA hC
    ((pointIntegralConstructible_iff l E D hl _).mpr hK)
    ((pointIntegralConstructible_iff l L D hl _).mpr _hH) v g _hg

/-- Transport for the finite subextensions in the fixed algebraic closure, with the
recorded intrinsic constructibility predicate. The auxiliary declarations in this module
state the equivalent cochain formula, derived naturality, identity, tower and raw
localization clauses of the same node.
Source: blueprint lem-pod-point-dualizing-complex.proof.md, coefficient-ring sentence
(blueprint: lem-pod-completed-model-sections-transport).
Proof: identify the two constructibility predicates by pointIntegralConstructible_iff.
The canonical units follow from final-object sheafification in Step 1. Descent
identifies theta on representatives (Step 2), phi inverse cancels the specified chi
(Step 3), and the local-generator calculation identifies the cochain map (Step 4).
K-projective representatives give derived naturality (Step 5). The normalized unit and
tower squares give identity and associator compatibility (Step 6). Expand the specified
rational phi and move the source unit through beta by naturality. Its unit and tower
laws give exactly the field multiplication and field associator (Step 7). A common
denominator and the localized comparison extension give all raw localized arrows,
including the opposite source (Steps 8--9),
and functoriality preserves the identity and tower equations (Step 10).
The generic coefficient telescope is specialized as one expression so that its
canonical coefficient structures are shared throughout the statement. -/
theorem completedModelSectionsTransport (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F G : Padic.FiniteCoefficientFields l Ω) (hFG : F ≤ G) :
    (fun (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
      (ι : E →ₐ[ℚ_[l]] L) ↦
      ∀ (A : CochainComplex (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E)) ℤ)
        (C : CochainComplex (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l L)) ℤ)
        (hA : IsModel l E A) (hC : IsModel l L C)
        (hK : sfIntegralConstructible l E (Spec (.of D.k))
          (DerivedCategory.Q.obj ((model D l E).obj A)))
        (_hH : sfIntegralConstructible l L (Spec (.of D.k))
          (DerivedCategory.Q.obj ((model D l L).obj C)))
        (v : ((pointIntegralModuleTensor l E L
          ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
        (g : (completedOrdinaryScalarComplex l E L
          ι (Spec (.of D.k))).obj
            ((model D l E).obj A) ⟶ (model D l L).obj C)
        (_hg : Realizes D l E L ι A C v g),
        transport D l E L ι hl A C hA hC
          ((pointIntegralConstructible_iff l E D hl _).mpr hK)
          (realizedMap D l E L ι A C g) =
            moduleMap l E L ι A C v ∧
        rationalTransport D l E L ι hl A C hA hC
          ((pointIntegralConstructible_iff l E D hl _).mpr hK)
          (realizedMap D l E L ι A C g) =
          rationalModuleMap l E L ι A C v) F.val G.val (IntermediateField.inclusion hFG) :=
  (fun (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
      (ι : E →ₐ[ℚ_[l]] L) ↦
      transport_sf_eq D l E L ι hl) F.val G.val (IntermediateField.inclusion hFG)

end WeilConjectures.CompletedModelSections


namespace WeilConjectures.CompletedModelSections

universe v' w'

variable {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  {I : Type v} [Category.{w} I] [Preadditive I] [Linear R I]
  {J : Type v'} [Category.{w'} J] [Preadditive J] [Linear S J]
  (t : R) (b : S) (φ : R →+* S)
  (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))
  (F G : I ⥤ J) [F.Additive] [G.Additive]
  (hF : ScalarLocalization.IsSemilinear φ F) (hG : ScalarLocalization.IsSemilinear φ G)

/-- The opposite category has the same coefficient modules on reversed Hom spaces.
Source: the contravariant clause of completed model transport
(blueprint: lem-pod-completed-model-sections-transport). -/
instance (priority := 100) oppositeLinear : Linear R Iᵒᵖ where
  homModule A B := (opEquiv A B).module R
  smul_comp A B C a f g := Quiver.Hom.unop_inj
    (Linear.comp_smul C.unop B.unop A.unop g.unop a f.unop)
  comp_smul A B C f a g := Quiver.Hom.unop_inj
    (Linear.smul_comp C.unop B.unop A.unop a g.unop f.unop)

private theorem tensor_fraction (X Y : I)
    (f : TensorProduct R (Localization.Away t) (X ⟶ Y)) :
    ∃ (n : ℕ) (a : X ⟶ Y),
      f = ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[R] a := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hn⟩ := IsLocalizedModule.surj (Submonoid.powers t)
    (TensorProduct.mk R (Localization.Away t) (X ⟶ Y) 1) f
  refine ⟨n, a, ?_⟩
  change (t ^ n) • f = (1 : Localization.Away t) ⊗ₜ[R] a at hn
  have hi : (IsLocalization.Away.invSelf t : Localization.Away t) ^ n *
      algebraMap R (Localization.Away t) (t ^ n) = 1 := by
    rw [map_pow, ← mul_pow, mul_comm, IsLocalization.Away.mul_invSelf, one_pow]
  have he := congrArg
    (fun z ↦ (IsLocalization.Away.invSelf t : Localization.Away t) ^ n • z) hn
  rw [← IsScalarTower.algebraMap_smul (Localization.Away t) (t ^ n) f,
    smul_smul, hi, one_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at he
  exact he

/-- Naturality on every raw localized morphism, with one denominator for both functors,
the actual fraction formulas, fixed components, and independence of representatives.
Apply this also with I replaced by I opposite: its displayed naturality equation is
then precisely precomposition for contravariant functors. For the coefficient-model
application R is O_E, t its chosen uniformizer, and the rational target inverts φ(t).
Source: completed model transport, Steps 8--9; Stacks 00DK, 07JZ and 07K0
(blueprint: lem-pod-completed-model-sections-transport).
Proof: a finite sum of tensors admits a common denominator t^N; take N the largest
exponent and absorb numerators and the remaining powers into one integral map. The
empty sum is 0/1. Equality of fractions means t^k(t^m u - t^n u') = 0 for some k.
Apply semilinearity and cancel the invertible image of t in the rational target;
this proves the two fraction values agree even with integral t-torsion. Extend the
comparison by lem-pur-semilinear-scalar-localization. Its components are the localized
integral components; the statement writes those components directly as localization.map.
Dividing the integral naturality equation by t^n gives the
asserted equation. In the opposite source the same calculation reverses the source
arrow and gives the stated precomposition equation. -/
theorem scalarLocalizedNaturality (η : F ⟶ G) :
    (∀ (X Y : I)
      (f : (⟨X⟩ : ScalarLocalization R I t) ⟶ (⟨Y⟩ : ScalarLocalization R I t)),
      ∃ (n : ℕ) (a : X ⟶ Y),
        f = ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[R] a ∧
        (ScalarLocalization.extension t b φ h F hF).map f =
          (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] F.map a ∧
        (ScalarLocalization.extension t b φ h G hG).map f =
          (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] G.map a ∧
        (ScalarLocalization.extension t b φ h F hF).map f ≫
            (ScalarLocalization.localization S J b).map (η.app Y) =
          (ScalarLocalization.localization S J b).map (η.app X) ≫
            (ScalarLocalization.extension t b φ h G hG).map f) ∧
    (∀ (X Y : I) (a a' : X ⟶ Y) (n m : ℕ),
      ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[R] a =
        ((IsLocalization.Away.invSelf t : Localization.Away t) ^ m) ⊗ₜ[R] a' →
      ((Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] F.map a =
        (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ m) ⊗ₜ[S] F.map a') ∧
      ((Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] G.map a =
        (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ m) ⊗ₜ[S] G.map a')) := by
  constructor
  · intro X Y f
    obtain ⟨n, a, ha⟩ := tensor_fraction t X Y f
    refine ⟨n, a, ha, ?_, ?_, ?_⟩
    · rw [ha]
      exact (ScalarLocalization.extension_spec t b φ h F hF).2.2 X Y a n
    · rw [ha]
      exact (ScalarLocalization.extension_spec t b φ h G hG).2.2 X Y a n
    · exact ScalarLocalization.extensionNatTrans_naturality t b φ h hF hG η _ _ f
  · intro X Y a a' n m heq
    constructor
    · have he := congrArg (fun f ↦
        (ScalarLocalization.extension t b φ h F hF).map
          (show (⟨X⟩ : ScalarLocalization R I t) ⟶ ⟨Y⟩ from f)) heq
      exact ((ScalarLocalization.extension_spec t b φ h F hF).2.2 X Y a n).symm.trans
        (he.trans ((ScalarLocalization.extension_spec t b φ h F hF).2.2 X Y a' m))
    · have he := congrArg (fun f ↦
        (ScalarLocalization.extension t b φ h G hG).map
          (show (⟨X⟩ : ScalarLocalization R I t) ⟶ ⟨Y⟩ from f)) heq
      exact ((ScalarLocalization.extension_spec t b φ h G hG).2.2 X Y a n).symm.trans
        (he.trans ((ScalarLocalization.extension_spec t b φ h G hG).2.2 X Y a' m))

omit [G.Additive] in
/-- Identity, tower and comparison-square equations persist as equations of localized
natural transformations. Components are on the same raw objects; no Karoubi completion
or additional idempotent summands are introduced. The two factorizations can be the
integral associator and either iterated comparison. The same assertion on the opposite
source gives its contravariant form.
Source: completed model transport, Step 10
(blueprint: lem-pod-completed-model-sections-transport).
Proof: evaluate the integral comparison-square equation at X and apply localization.
Its composition law gives the first equation of actual components. Apply the common-
denominator naturality calculation to the composite a followed by c on an arbitrary
localized arrow, and replace its source component using the integral square. This gives
the second equation. For identity normalization one path is the identity comparison;
for a tower the paths are the two integral associator comparisons. Taking components
of whiskered comparisons gives the same result. The fraction computation proves
naturality on all raw arrows, with unchanged objects, also for the opposite source. -/
theorem scalarLocalizedCoherence
    (H K : I ⥤ J) [H.Additive]
    (hH : ScalarLocalization.IsSemilinear φ H)
    (a : F ⟶ G) (c : G ⟶ H) (d : F ⟶ K) (e : K ⟶ H) (_heq : a ≫ c = d ≫ e) :
    (∀ X : I,
      (ScalarLocalization.localization S J b).map (a.app X) ≫
          (ScalarLocalization.localization S J b).map (c.app X) =
        (ScalarLocalization.localization S J b).map (d.app X) ≫
          (ScalarLocalization.localization S J b).map (e.app X)) ∧
    (∀ (X Y : I)
      (f : (⟨X⟩ : ScalarLocalization R I t) ⟶ (⟨Y⟩ : ScalarLocalization R I t)),
      (ScalarLocalization.extension t b φ h F hF).map f ≫
          (ScalarLocalization.localization S J b).map (a.app Y) ≫
          (ScalarLocalization.localization S J b).map (c.app Y) =
        (ScalarLocalization.localization S J b).map (d.app X) ≫
          (ScalarLocalization.localization S J b).map (e.app X) ≫
          (ScalarLocalization.extension t b φ h H hH).map f) := by
  have hs (X : I) :
      (ScalarLocalization.localization S J b).map (a.app X) ≫
          (ScalarLocalization.localization S J b).map (c.app X) =
        (ScalarLocalization.localization S J b).map (d.app X) ≫
          (ScalarLocalization.localization S J b).map (e.app X) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((ScalarLocalization.localization S J b).map)
      (congrArg (fun η ↦ η.app X) _heq)
  refine ⟨hs, ?_⟩
  intro X Y f
  have hn := ScalarLocalization.extensionNatTrans_naturality t b φ h hF hH (a ≫ c)
    (⟨X⟩ : ScalarLocalization R I t) ⟨Y⟩ f
  simpa only [NatTrans.comp_app, Functor.map_comp, Category.assoc, hs X] using hn

/-- The contravariant equation on raw localized arrows, explicitly in the opposite
source presentation. A tensor a tensor u.op represents u divided by the same denominator;
the resulting functor map goes from the value at Y to the value at X.
Source: completed model transport, Step 9
(blueprint: lem-pod-completed-model-sections-transport).
Proof: apply scalarLocalizedNaturality to I opposite. Its integral arrow u.op has
source Y.op and target X.op, so the naturality equation composes on the required side.
The common-denominator and independence assertions are unchanged for the opposite
Hom module. Thus the equation holds on every raw localized arrow. -/
theorem scalarLocalizedContravariant
    (Fop Gop : Iᵒᵖ ⥤ J) [Fop.Additive] [Gop.Additive]
    (hFop : ScalarLocalization.IsSemilinear φ Fop)
    (hGop : ScalarLocalization.IsSemilinear φ Gop) (η : Fop ⟶ Gop)
    (X Y : I)
    (f : (⟨op Y⟩ : ScalarLocalization R Iᵒᵖ t) ⟶
      (⟨op X⟩ : ScalarLocalization R Iᵒᵖ t)) :
    (ScalarLocalization.extension t b φ h Fop hFop).map f ≫
        (ScalarLocalization.localization S J b).map (η.app (op X)) =
      (ScalarLocalization.localization S J b).map (η.app (op Y)) ≫
        (ScalarLocalization.extension t b φ h Gop hGop).map f ∧
    ∃ (n : ℕ) (a : X ⟶ Y),
      f = ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[R] a.op ∧
      (ScalarLocalization.extension t b φ h Fop hFop).map f =
        (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] Fop.map a.op ∧
      (ScalarLocalization.extension t b φ h Gop hGop).map f =
        (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] Gop.map a.op := by
  obtain ⟨n, a, ha, hFa, hGa, hn⟩ :=
    (scalarLocalizedNaturality t b φ h Fop Gop hFop hGop η).1 (op Y) (op X) f
  exact ⟨hn, n, a.unop, ha, hFa, hGa⟩

end WeilConjectures.CompletedModelSections
