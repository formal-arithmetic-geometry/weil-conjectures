/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Ring.NegOnePow
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.CompletedConstantSheafReduction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.AdmissibleScalarRealizationExact
import Sheaf.Paper.OrdinaryScalarPerfectLocalDual
import Sheaf.Paper.OrdinaryScalarModelBoundedDescent

/-!
# Scalar cohomology models for locally perfect complexes and their duals

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-internal-hom.proof.md,
paragraphs 2--3; Stacks Tags 093J, 093M, 08JB, 08JH, 08JJ
(blueprint: lem-sfb-internal-hom-dual-constructible-models).

The result is expressed for each of the six admissible coefficients. The auxiliary
predicate expands the same assertion for each coefficient without replacing the
specified scalar-extension functor by an arbitrary functor hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.InternalHomDualModels

variable {R : Type u} [CommRing R]

/-- The signed scalar dual differential: phi maps to -(-1)^i phi d_F.
Source: Stacks Tag 08JJ, ordinary dual complex
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def scalarDualDifferential (F : CochainComplex (ModuleCat.{u + 1} R) ℤ) (i j : ℤ) :
    ModuleCat.of R (Module.Dual R (F.X (-i))) ⟶
      ModuleCat.of R (Module.Dual R (F.X (-j))) :=
  ModuleCat.ofHom (-i.negOnePow • (F.d (-j) (-i)).hom.dualMap)

/-- The explicit dual differentials satisfy the complex axioms.
Source: Stacks Tag 08JJ (blueprint: lem-sfb-internal-hom-dual-constructible-models).
Proof: if i+1 is not j then -j+1 is not -i, so the original differential vanishes.
A composite is the product of two signs times precomposition with d_F d_F, hence zero.
These are the two well-definedness checks of the ordinary scalar Hom complex. -/
theorem scalarDualDifferential_laws (F : CochainComplex (ModuleCat.{u + 1} R) ℤ) :
    (∀ i j : ℤ, ¬ (ComplexShape.up ℤ).Rel i j → scalarDualDifferential F i j = 0) ∧
    (∀ i j k : ℤ, scalarDualDifferential F i j ≫ scalarDualDifferential F j k = 0) := by
  constructor
  · intro i j hij
    have hd : F.d (-j) (-i) = 0 := F.shape _ _ (by
      simp only [ComplexShape.up_Rel] at hij ⊢
      omega)
    apply ModuleCat.hom_ext
    ext φ x
    simp [scalarDualDifferential, hd]
  · intro i j k
    apply ModuleCat.hom_ext
    ext φ x
    have hd (x : F.X (-k)) :
        (F.d (-j) (-i)).hom ((F.d (-k) (-j)).hom x) = 0 :=
      ConcreteCategory.congr_hom (F.d_comp_d (-k) (-j) (-i)) x
    simp [scalarDualDifferential, hd]

/-- The actual scalar complex Hom_R(F,R[0]), with reversed degrees and its Hom sign.
Source: Stacks Tag 08JJ (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def scalarDual (F : CochainComplex (ModuleCat.{u + 1} R) ℤ) :
    CochainComplex (ModuleCat.{u + 1} R) ℤ where
  X i := ModuleCat.of R (Module.Dual R (F.X (-i)))
  d := scalarDualDifferential F
  shape := (scalarDualDifferential_laws F).1
  d_comp_d' i j k _ _ := (scalarDualDifferential_laws F).2 i j k

/-- Additivity of the already defined scalar module functor.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models).
Proof: its map is the original additive linear map; addition is unchanged in internal
abelian-group modules. Sheafification, extension of scalars and point pullback are additive. -/
theorem scalarModules_additive (A : Type u) [CommRing A] :
    (FiniteConstantModel.scalarModules A).Additive := by
  exact { map_add := by intros; rfl }

attribute [instance] scalarModules_additive

/-- The finite-discrete coefficient model, with the discrete topology fixed in the data.
Source: blueprint admissible coefficients; Stacks Tag 093J
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def finiteModel (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  FiniteConstantModel.modelFunctor A T

/-- Finite-discrete coefficients, with their actual continuous-function ring structure.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev finiteCoefficients (A : Type u) [CommRing A] :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  Profinite.continuousCoefficientRingObj A

/-- The integral base coefficient, lifted only to the scheme universe.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev baseIntegralCoefficients (l : ℕ) [Fact l.Prime] :=
  Profinite.continuousCoefficientRingObj (ULift.{u} ℤ_[l])

/-- Its canonical ordinary scalar model.
Source: Stacks Tags 093J, 093M
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def baseIntegralModel (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  FiniteConstantModel.modelFunctor (ULift.{u} ℤ_[l]) T

/-- The rational base coefficient, lifted only to the scheme universe.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev baseRationalCoefficients (l : ℕ) [Fact l.Prime] :=
  Profinite.continuousCoefficientRingObj (ULift.{u} ℚ_[l])

/-- Its canonical ordinary scalar model.
Source: Stacks Tag 093J
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def baseRationalModel (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  FiniteConstantModel.modelFunctor (ULift.{u} ℚ_[l]) T

/-- The algebraic-closure coefficient: all continuous functions into Qbar_l with the
topology of its l-adic absolute value, lifted only to the scheme universe. This is the
condensed ring of the topological ring Qbar_l (sk-def-sfb-condensed-ring), as fixed by the
coefficient convention of sk-def-localizing-closure; it is not the finite-subextension
colimit object.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev algebraicCoefficients (l : ℕ) [Fact l.Prime] :=
  Profinite.continuousCoefficientRingObj (ULift.{u} (PadicAlgCl l))

/-- Its canonical ordinary scalar model.
Source: Stacks Tag 093J
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def algebraicModel (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  FiniteConstantModel.modelFunctor (ULift.{u} (PadicAlgCl l)) T

/-- Commutativity of the already constructed discrete constant scalar ring.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance constantScalarsComm (A : Type u) [CommRing A] :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  FiniteConstantModel.constantScalars_commutative A

/-- Termwise realization of scalar complexes preserves zero maps.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models).
Proof: the scalar module functor, sheafification and point inverse image are additive.
Relative scalar extension is a left adjoint between abelian categories, so is additive.
The resulting composite therefore preserves zero and addition. -/
theorem realization_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (A : Type u) [CommRing A]
    (ρ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Λ) [IsMonHom ρ] (T : Scheme.{u}) :
    (FiniteConstantModel.scalarModules A ⋙
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙ Mod.extendScalars ρ ⋙
          (upperStarFromPoint T).mapMod Λ).Additive := by
  have : ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A))).Additive :=
    { map_add := by
        intros
        apply Mod.hom_ext
        exact (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map_add }
  have : PreservesFiniteColimits (upperStarFromPoint T) := by
    have h : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint T) := by
      let adj := pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
      exact adj.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesBinaryBiproducts (upperStarFromPoint T) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint T).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : ((upperStarFromPoint T).mapMod Λ).Additive :=
    { map_add := by intros; apply Mod.hom_ext; exact (upperStarFromPoint T).map_add }
  infer_instance

attribute [instance] realization_additive

/-- Additivity of the canonical continuous-coefficient model.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance continuousModelAdditive (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (T : Scheme.{u}) :
    (FiniteConstantModel.modelFunctor A T).Additive :=
  realization_additive _ A (FiniteConstantModel.scalarToContinuous A) T

/-- Additivity for finite discrete coefficients.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance finiteModelAdditive (A : Type u) [CommRing A] (T : Scheme.{u}) :
    (finiteModel A T).Additive :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  continuousModelAdditive A T

/-- Additivity for the integral base coefficient.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance baseIntegralModelAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (baseIntegralModel l T).Additive := continuousModelAdditive _ T

/-- Additivity for the rational base coefficient.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance baseRationalModelAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (baseRationalModel l T).Additive := continuousModelAdditive _ T

/-- Additivity for a finite extension's completed integral coefficient.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance integralModelAdditive (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (FiniteConstantModel.integralModel l E T).Additive :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  continuousModelAdditive _ T

/-- Additivity for finite extension field coefficients.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance rationalModelAdditive (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (FiniteConstantModel.rationalModel l E T).Additive :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  continuousModelAdditive _ T

/-- Additivity for the continuous condensed algebraic closure.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance algebraicModelAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (algebraicModel l T).Additive := continuousModelAdditive _ T

/-- The two original-cover cohomology formulas, finite presentation, and membership
of both objects in Dbc. The model functor is a parameter here only to share the syntax:
the main theorem substitutes the explicit canonical functor in each coefficient case.
Source: blueprint internal-Hom stability proof, paragraphs 2--3
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def Assertion (A : Type u) [CommRing A]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : ∀ T : Scheme.{u}, ModuleCat.{u + 1} A ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    [∀ T : Scheme.{u}, (C T).Additive] (S : Scheme.{u}) : Prop :=
  ∀ (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (F : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ),
    (∀ i : 𝒰.I₀, ∃ a b : ℤ, (F i).IsStrictlyGE a ∧ (F i).IsStrictlyLE b) →
    (∀ (i : 𝒰.I₀) (q : ℤ), Module.Finite A ((F i).X q) ∧
      Module.Projective A ((F i).X q)) →
    (∀ i : 𝒰.I₀, Nonempty
      (((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory).obj P ≅
        DerivedCategory.Q.obj (((C (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj (F i)))) →
    (∀ (i : 𝒰.I₀) (q : ℤ),
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj P) ≅
          (C (𝒰.X i)).obj
            ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj (F i))) ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedHom Λ S).obj (op P)).obj (𝟙_ _))) ≅
            (C (𝒰.X i)).obj
              ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj
                (scalarDual (F i)))) ∧
      Module.FinitePresentation A
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj (F i)) ∧
      Module.FinitePresentation A
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj
          (scalarDual (F i)))) ∧
    constantModelBoundedConstructible Λ S P ∧
    constantModelBoundedConstructible Λ S
      (((CondensedRing.derivedHom Λ S).obj (op P)).obj (𝟙_ _))

private theorem finitePresentation_homology
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (F : CochainComplex (ModuleCat.{u + 1} A) ℤ) (q : ℤ)
    (hfinite : Module.Finite A (F.X q)) : Module.FinitePresentation A (F.homology q) := by
  let : Module.Finite A (F.sc q).X₂ := hfinite
  let K := LinearMap.ker (F.sc q).g.hom
  have : Module.Finite A K := Module.Finite.of_injective K.subtype K.injective_subtype
  have : Module.FinitePresentation A (F.sc q).moduleCatLeftHomologyData.H := by
    change Module.FinitePresentation A (K ⧸ LinearMap.range (F.sc q).moduleCatToCycles)
    exact Module.finitePresentation_of_finite A _
  exact Module.FinitePresentation.of_equiv (F.sc q).moduleCatHomologyIso.symm.toLinearEquiv

private theorem assertion_of_exact_realization
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (h : ∀ T : Scheme.{u}, AdmissibleScalarRealization.ScalarAssertions A T) :
    Assertion A (Profinite.continuousCoefficientRingObj A)
      (FiniteConstantModel.modelFunctor A) S := by
  let : IsNoetherianRing A := (h S).1
  have hexact (T : Scheme.{u}) :
      PreservesFiniteLimits (FiniteConstantModel.modelFunctor A T) ∧
        PreservesFiniteColimits (FiniteConstantModel.modelFunctor A T) :=
    ⟨(h T).2.2.1, (h T).2.2.2.1⟩
  intro P 𝒰 F hbounded hterms hmodel
  have hb (i : 𝒰.I₀) : ∃ a b : ℤ, ∀ q : ℤ,
      q < a ∨ b < q → IsZero ((F i).X q) := by
    obtain ⟨a, b, ha, hb⟩ := hbounded i
    let := ha
    let := hb
    exact ⟨a, b, fun q hq ↦ hq.elim
      (fun hq ↦ (F i).isZero_of_isStrictlyGE a q hq)
      (fun hq ↦ (F i).isZero_of_isStrictlyLE b q hq)⟩
  have hdb (i : 𝒰.I₀) : ∃ a b : ℤ, ∀ q : ℤ,
      q < a ∨ b < q → IsZero ((scalarDual (F i)).X q) := by
    obtain ⟨a, b, hab⟩ := hb i
    refine ⟨-b, -a, fun q hq ↦ ?_⟩
    have hz := hab (-q) (by omega)
    have : Subsingleton ((F i).X (-q)) := ModuleCat.isZero_iff_subsingleton.mp hz
    change IsZero (ModuleCat.of A (Module.Dual A ((F i).X (-q))))
    exact ModuleCat.isZero_of_subsingleton _
  have hdfinite (i : 𝒰.I₀) (q : ℤ) :
      Module.Finite A ((scalarDual (F i)).X q) := by
    let := (hterms i (-q)).1
    let := (hterms i (-q)).2
    exact Module.dual_finite (R := A) (M := (F i).X (-q))
  have hfp (i : 𝒰.I₀) (q : ℤ) : Module.FinitePresentation A ((F i).homology q) :=
    finitePresentation_homology A (F i) q (hterms i q).1
  have hdfp (i : 𝒰.I₀) (q : ℤ) :
      Module.FinitePresentation A ((scalarDual (F i)).homology q) :=
    finitePresentation_homology A (scalarDual (F i)) q (hdfinite i q)
  have hdmodel := ordinaryScalarPerfect_local_dual A S P 𝒰 F
    (fun i ↦ scalarDual (F i)) hb hterms (fun _ _ ↦ Iso.refl _) (by
      intro i q r
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl) hmodel
  have cohomology_model
      (Q : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousCoefficientRingObj A) S)))
      (K : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ)
      (hm : ∀ i : 𝒰.I₀, Nonempty
        (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
          (𝒰.f i)).mapDerivedCategory).obj Q ≅ DerivedCategory.Q.obj
            (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex
              (.up ℤ)).obj (K i)))) (i : 𝒰.I₀) (q : ℤ) :
      Nonempty ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
        (𝒰.f i)).obj ((DerivedCategory.homologyFunctor _ q).obj Q) ≅
          (FiniteConstantModel.modelFunctor A (𝒰.X i)).obj ((K i).homology q)) := by
    let := (hexact (𝒰.X i)).1
    let := (hexact (𝒰.X i)).2
    obtain ⟨e⟩ := hm i
    exact ⟨((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
      (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso q).app Q ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      ((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplexHomologyIso
        (.up ℤ) q).app (K i)⟩
  refine ⟨fun i q ↦ ⟨cohomology_model P F hmodel i q,
    cohomology_model _ _ hdmodel i q, hfp i q, hdfp i q⟩, ?_, ?_⟩
  · exact ordinaryScalarModel_bounded_descent A S P 𝒰 F hexact hb hmodel hfp
  · exact ordinaryScalarModel_bounded_descent A S _ 𝒰
      (fun i ↦ scalarDual (F i)) hexact hdb hdmodel hdfp

/-- Constructible scalar cohomology models for all six admissible coefficient rings.
The integral sheaves are the pulled-back continuous condensed rings, including their
completed inverse-limit realization; no discrete replacement or derived completeness
condition is imposed. Bounds on each scalar complex may vary with the cover member.

Source: blueprint main-20261015, internal-Hom stability proof, paragraphs 2--3;
Stacks Tags 00FP, 093J, 093M, 08JB, 08JH, 08JJ
(blueprint: lem-sfb-internal-hom-dual-constructible-models).

Proof (the ten node steps):
1. Every admissible scalar ring is Noetherian: finite rings and fields by the ideal
criterion; integral rings by lem-weil-l-adic-extension-integers-dvr, with Z_l the base case.
2. Finite-projective duality makes the scalar dual bounded and finite projective.
Noetherian finite kernels and cokernels and finite-module finite presentation show
that both scalar cohomology modules are finitely presented; they need not be projective.
3. For finite coefficients scalar realization is the exact constant module functor
(def-sfb-site-derived-constant-module-functor and finite-discrete condensed comparison).
For field coefficients scalar exact sequences split by a basis, and realization preserves
that splitting, including for the continuous condensed algebraic closure.
4. For integral coefficients det-prop-sfb-qlbar-colimit-x-integral-limit identifies the
coefficient sheaf with the limit of constant finite quotients. Completion-flatness
(lem-weil-pbc-completed-constant-sheaf-reduction) gives exact scalar realization.
5. The strict-perfect package splits every realized term from a finite free sheaf.
Internal Hom out of a finite free sheaf is exact; its direct summand is exact as well.
6. Exact restriction commutes with derived internal Hom. On the chart, bounded
exact-term Hom takes the K-injective resolution B[0] to a quasi-isomorphic Hom complex.
Thus the dual is represented by the ordinary finite-projective dual complex.
7. The map b tensor phi to (b' tensor v to bb'phi(v)) is an isomorphism for finite free
modules and hence their retracts. Naturality respects the differential -(-1)^q phi d_F,
identifying that ordinary dual with the realization of the stated scalarDual.
8. Exact functors commute with homology, and exact restriction commutes with it too.
Apply this to F and scalarDual F to obtain both formulas on EVERY ORIGINAL chart.
9. Finite type over a field makes S Noetherian, hence qcqs. The finite affine proetale
refinement lemma gives a finite refinement of the given cover. Cartesian coefficients
restrict both models to that refinement. If S is empty use zero complexes and [0,0].
10. Take the minimum and maximum of the finitely many bounds. The dual bounds are
[-b,-a]. Local-model cohomology descent gives global bounds and constructibility on the
single stratum S, proving both Dbc memberships without changing the coefficient sheaf. -/
theorem internalHomDual_constructible_models
    (l p : ℕ) [Fact l.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpl : p ≠ l) (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
    (∀ (A : Type u) [CommRing A] [Finite A],
      (∃ n : ℕ, (l : A) ^ n = 0) →
      Assertion A (finiteCoefficients A) (finiteModel A) S) ∧
    Assertion (ULift.{u} ℤ_[l]) (baseIntegralCoefficients l) (baseIntegralModel l) S ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      Assertion (Padic.coefficientExtensionIntegers l E)
        (FiniteConstantModel.integralCoefficients l E)
        (FiniteConstantModel.integralModel l E) S) ∧
    Assertion (ULift.{u} ℚ_[l]) (baseRationalCoefficients l) (baseRationalModel l) S ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      Assertion E (FiniteConstantModel.rationalCoefficients l E)
        (FiniteConstantModel.rationalModel l E) S) ∧
    Assertion (ULift.{u} (PadicAlgCl l)) (algebraicCoefficients l)
      (algebraicModel l) S := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
    (S ↘ Spec (.of k))
  have _ := hp
  have _ := hpl
  have h := AdmissibleScalarRealization.admissible_scalar_realization_exact
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ hnil
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    apply assertion_of_exact_realization A S
    intro T
    apply ((h l T).1 A ?_).1
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, fun a ↦ ?_⟩
    rw [nsmul_eq_mul, Nat.cast_pow, hn, zero_mul]
  · exact assertion_of_exact_realization _ S (fun T ↦ (h l T).2.1.1)
  · intro E _ _ _
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    exact assertion_of_exact_realization _ S (fun T ↦ ((h l T).2.2.1 E).1.1)
  · exact assertion_of_exact_realization _ S (fun T ↦ (h l T).2.2.2.1)
  · intro E _ _ _
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    exact assertion_of_exact_realization _ S (fun T ↦ ((h l T).2.2.1 E).2)
  · exact assertion_of_exact_realization _ S (fun T ↦ (h l T).2.2.2.2)

end AlgebraicGeometry.ProEtale.InternalHomDualModels
