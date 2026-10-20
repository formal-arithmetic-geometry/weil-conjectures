/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
import Sheaf.Paper.RestrictionLocalCompleteness
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.Paper.IntegralCohomologicalAdicCriterion

/-! # Integral constructible objects and Stacks adic constructibility

Source: blueprint main-20261015, sk-lem-integral-models-stacks; Stacks Project,
Tag 09C1 (blueprint: det-lem-integral-models-stacks).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- The discrete scalar ring on the pro-etale point. Source: Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks). -/
abbrev discreteSheaf (A : Type u) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A)))

/-- Its underlying condensed abelian ring object. Source: Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks). -/
abbrev discreteObj (A : Type u) [CommRing A] :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (discreteSheaf A)

/-- The commutative ring structure comes from the actual constant commutative ring sheaf.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
instance discreteObj_comm (A : Type u) [CommRing A] : IsCommMonObj (discreteObj A) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (discreteSheaf A) (fun U a b ↦
      @mul_comm (((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} A))).obj.obj U) _ a b)

/-- The scalar map on the point sends an element to its constant continuous function.
Source: blueprint integral-models-stacks, the map from the constant sheaf
(blueprint: det-lem-integral-models-stacks). -/
def constantToContinuous (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteSheaf A ⟶ Profinite.continuousMapRingSheafOfUniverse A :=
  ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} A))).hom ≫
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) RingCat.{u + 1}).homEquiv
    _ _).symm
      { app S := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ContinuousMap.C (α := S.unop)).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) }

/-- A scalar homomorphism induces the actual map between discrete condensed rings.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
def discreteMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    discreteObj A ⟶ discreteObj B :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)))))

/-- The source and target ring structures are the sheafified scalar structures.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
instance discreteMap_mon {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    IsMonHom (discreteMap f) := inferInstanceAs (IsMonHom
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _))

/-- Reconstruct the section-ring map of a map of internal commutative rings.
Source: Stacks Tag 00YV (blueprint: det-lem-integral-models-stacks). -/
def sectionMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf _ Ab.{u + 1}).mapCommMon.map (CommMon.homMk (Mon.ofHom f))))
    InternalAbelianSheafModule.commMonToRing.{u + 1}⟩

/-- The section ring on the equivalent coefficient-sized small pro-etale site.
Source: Stacks Tags 00YV and 09A5 (blueprint: det-lem-integral-models-stacks). -/
abbrev smallRing (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :=
  ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R)

/-- The same reconstructed coefficient homomorphism on the small site.
Source: Stacks Tags 00YV and 09A5 (blueprint: det-lem-integral-models-stacks). -/
def smallMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] : smallRing X R ⟶ smallRing X S :=
  ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).map
    (sectionMap X f)

/-- Sectionwise module transport to the equivalent small site. It preserves sections
and their scalar action. Source: Stacks Tags 00YV and 09A5
(blueprint: det-lem-integral-models-stacks). -/
def smallModules (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      ConstantCompletion.Mod (smallRing X R) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X) R).functor ⋙
    SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _)

/-- Transport a derived object by the sectionwise equivalence, on a localization
representative. This is the exact transport to the identical small ringed topos.
Source: Stacks Tags 00YV, 05RU and 09A5
(blueprint: det-lem-integral-models-stacks). -/
def smallDerivedObject (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    ConstantCompletion.D (smallRing X R) :=
  letI : (smallModules X R).PreservesZeroMorphisms :=
    { map_zero := fun _ _ ↦ rfl }
  (ConstantCompletion.Q _).obj (((smallModules X R).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage K))

/-- The existing completed integral condensed ring, without any finite-field base datum.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
abbrev integersObj (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  (sfbCondensedIntegers l E).X

/-- Commutativity of the continuous-function coefficient ring.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
instance integersObj_comm (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integersObj l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionIntegers l E))
    (fun S a b ↦ @mul_comm
      (ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers l E)) _ a b)

/-- The canonical map from discrete to completed integral coefficients on the point.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
def scalarPointMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    discreteObj (Padic.coefficientExtensionIntegers l E) ⟶ integersObj l E :=
  letI := spectralNorm.normedField (Padic l) E
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (constantToContinuous (Padic.coefficientExtensionIntegers l E))

/-- The scalar map preserves the ring operations by its construction from a ring map.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
instance scalarPointMap_mon (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsMonHom (scalarPointMap l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (constantToContinuous (Padic.coefficientExtensionIntegers l E))

/-- Pull back the specified constant-to-continuous map to X.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
def scalarMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (upperStarFromPoint X).map (scalarPointMap l E)

/-- Monoidality of the site inverse image preserves the specified coefficient map.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
instance scalarMap_mon (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    IsMonHom (scalarMap l E X) := inferInstanceAs
      (IsMonHom ((upperStarFromPoint X).map (scalarPointMap l E)))

/-- The canonical residue coefficient map on X, induced by the actual first quotient.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
def residueMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (upperStarFromPoint X).map
    (discreteMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)))

/-- The residue map is a map of the actual pulled-back commutative ring objects.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
instance residueMap_mon (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    IsMonHom (residueMap l E X) := inferInstanceAs
      (IsMonHom ((upperStarFromPoint X).map
        (discreteMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)))))

/-- Exact, termwise restriction along the canonical map from the constant coefficient ring.
Source: blueprint integral-models-stacks (blueprint: det-lem-integral-models-stacks). -/
abbrev restriction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (scalarMap l E X)).mapDerivedCategory

/-- Stacks adic constructibility: local derived completeness for the kernel of the
first residue map, constructible residue cohomology, and finite relative Tor amplitude.
Transport to the equivalent small site is used only for the recorded local completeness
predicate; no hypothesis on the complex is imposed by this transport.
Source: Stacks Tag 09C1 (blueprint: det-lem-integral-models-stacks). -/
def stacksConstructible (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))) :=
  fun L ↦
    ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
      (smallDerivedObject X _ L) ∧
    (∀ n : ℤ, IsConstantModelConstructible
      (discreteObj (Padic.coefficientExtensionRing l E 1)) X
        ((DerivedCategory.homologyFunctor _ n).obj
          ((Mod.extendScalars (residueMap l E X)).leftDerivedFunctor.obj L))) ∧
    DerivedCategory.finiteTorAmplitude _
      ((Mod.extendScalars (residueMap l E X)).leftDerivedFunctor.obj L)

/-- Restriction of scalars identifies the bounded constant-model constructible category
with the Stacks adic constructible category, and reflects membership for every complex.
Source: blueprint main-20261015, sk-lem-integral-models-stacks; Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof:
1. `det-prop-sfb-qlbar-colimit-x-integral-limit` and parts (1),(3) of
   `det-prop-integral-criterion-constant-coefficients` identify all positive quotients
   and the relative derived reductions before and after restriction.
2. `lem-weil-pbc-restriction-local-completeness` identifies local completeness for
   arbitrary complexes. `lem-weil-pbc-constant-completion-equivalence` identifies local
   and quotient-tower completeness. Its hypotheses hold since the integers are a DVR
   (`lem-weil-l-adic-extension-integers-dvr`) and the uniformizer ideal is principal.
3. Noetherian X is qcqs: apply `lem-sc-affine-noetherian-underlying-space` on a finite
   affine cover. `sk-thm-pe-constructible-comparison` and
   `det-pe-finite-tor-comparison-noetherian` identify the residue condition with a bounded
   constructible etale residue complex of finite Tor amplitude. Tensor with the unit
   in `sk-def-sfb-derived-tensor-hom` to see that finite Tor amplitude forces boundedness.
4. `lem-sfb-proetale-tor-local-global` identifies locally finite Tor dimension with a
   single global interval on this quasi-compact X, testing all modules on every slice.
5. `lem-sfb-integral-cohomological-adic-criterion` identifies bounded constant-model
   constructibility with completeness and the etale-origin residue condition. Steps
   1--4 translate these precisely into stacksConstructible of the restricted complex.
6. Part (2) of `det-prop-integral-criterion-constant-coefficients` makes restriction an
   equivalence on complete objects. Step 5 identifies the selected objects. Its
   restriction is fully faithful with unchanged Hom maps. Every adic constructible L
   has a complete preimage K, which is bounded constructible by step 5. The displayed
   natural isomorphism identifies the resulting equivalence's functor with Res.
   Section-module equivalence and AsSmall precomposition only change presentation.
-/
theorem integral_models_stacks (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K, constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K)) ∧
    ∃ e : ConstantModelBoundedConstructible (integersObj l E) X ≌
        (stacksConstructible l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksConstructible l E X).ι ≅
        (constantModelBoundedConstructible (integersObj l E) X).ι ⋙ restriction l E X) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
