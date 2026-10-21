/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.IntegralModels
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Sheaf.Paper.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.SixFunctors.IntegralExtHomContinuity
import Sheaf.SixFunctors.IntegralModelsGenerators
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.IntegralModelsOperations
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage

/-! # Rational Hom groups from integral models

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational-hom.md (blueprint: det-sp-rational-localized-hom).

The Hom scalar actions use the existing continuous module encoding and constant functions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.RationalLocalizedHom

/-- Fix the exact existing locally bijective criterion at the coefficient universe.
Source: Stacks 03DA (blueprint: det-sp-rational-localized-hom). -/
instance (priority := 4000) locallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

/-- Constant functions give the actual scalar sections of the continuous coefficient sheaf.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
def scalarSections (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    A →+* RingCat.sectionsSubring (continuousMapRingSheaf.{0, u} X A).obj where
  toFun a := ⟨fun _ ↦ ULift.up (ContinuousMap.const _ a), fun _ ↦ rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original continuous coefficient presheaf, retaining commutativity.
Source: blueprint coefficient convention (blueprint: det-sp-rational-localized-hom). -/
def commutativePresheaf (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj V := CommRingCat.of (ULift.{u + 1} C(V.unop.left, A))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ A f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Pointwise constant-scalar action on module sheaves.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance continuousLinear (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    Linear A (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) :=
  letI : Linear (RingCat.sectionsSubring (continuousMapRingSheaf.{0, u} X A).obj)
      (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) :=
    SheafOfModules.homLinear (commutativePresheaf X A)
      (continuousMapRingSheaf.{0, u} X A).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (scalarSections X A)
    smul_comp := fun M N P a f g ↦ Linear.smul_comp M N P (scalarSections X A a) f g
    comp_smul := fun M N P f a g ↦ Linear.comp_smul M N P f (scalarSections X A a) g }

/-- The standard ambient localization on continuous module sheaves.
Source: Stacks 05RR (blueprint: det-sp-rational-localized-hom). -/
instance continuousDerived (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      (continuousMapRingSheaf.{0, u} X A)) := HasDerivedCategory.standard _

/-- An equivalence of abelian categories is additive.
Source: Stacks 00YV (blueprint: det-sp-rational-localized-hom). -/
instance encodingAdditive (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    (CondensedRing.continuousRingModuleEquivalence X A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse encoding is additive as well.
Source: Stacks 00YV (blueprint: det-sp-rational-localized-hom). -/
instance encodingInverseAdditive (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    (CondensedRing.continuousRingModuleEquivalence X A).inverse.Additive := inferInstance

/-- The existing continuous module equivalence on ordinary derived categories.
Source: Stacks 05RR (blueprint: det-sp-rational-localized-hom). -/
abbrev encoding (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) ≌
    DerivedCategory.{u + 2} (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) :=
  (CondensedRing.continuousRingModuleEquivalence X A).mapDerivedCategory

/-- Derived encoding remains additive.
Source: Stacks 05RR (blueprint: det-sp-rational-localized-hom). -/
instance derivedEncodingAdditive (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    (encoding X A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Hom scalar action transported through the actual coefficient encoding.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance homModule (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))) : Module A (K ⟶ L) :=
  AddEquiv.module A
    { (encoding X A).fullyFaithfulFunctor.homEquiv with
      map_add' := fun f g ↦ (encoding X A).functor.map_add (f := f) (g := g) }

/-- Flatness is the existing coefficient-localization theorem's final clause.
Source: blueprint proof step 1 (blueprint: det-sp-rational-localized-hom). -/
instance exactExtension (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) :=
  (padicIntegers_invertEll X ℓ E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2

/-- Canonical shifts of scalar extension, using its exact termwise description.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance extensionShift (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso
    (Functor.leftDerivedFunctorIsoMapDerivedCategory
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E))).symm ℤ

/-- Integral and rational ambient derived categories with the published coefficient sheaves.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev integral (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))

/-- Rational ambient category with the continuous field coefficients.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev rational (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E.1) X))

/-- The specified rationalization is the recorded total left derived scalar extension.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev extend (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : integral X ℓ E ⥤ rational X ℓ E :=
  (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor

/-- Bounded constructibility is the recorded full subcategory predicate.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev integralConstructible (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)

/-- Bounded constructibility over the field is the same recorded predicate.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev rationalConstructible (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)

/-- Use the canonical induced norm for the finite embedded coefficient field.
Source: blueprint coefficient convention (blueprint: det-sp-rational-localized-hom). -/
instance coefficientNorm (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : NormedField E.1 :=
  PadicAlgCl.normedFieldOfAlgebra ℓ E.1

/-- The induced norm is ultrametric.
Source: the existing PadicAlgCl valuation (blueprint: det-sp-rational-localized-hom). -/
instance coefficientUltra (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : IsUltrametricDist E.1 :=
  PadicAlgCl.isUltrametricDist_ofAlgebra ℓ E.1

/-- The integer Hom action is the canonical continuous scalar action above.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance integralHomModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (K L : integral X ℓ E) :
    Module (PadicAlgCl.integers ℓ E.1) (K ⟶ L) :=
  homModule X (PadicAlgCl.integers ℓ E.1) K L

/-- The field Hom action is the canonical continuous scalar action above.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance rationalHomModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (K L : rational X ℓ E) :
    Module E.1 (K ⟶ L) := homModule X E.1 K L

/-- The standing chosen compactification defines the ambient compact-support composite.
Source: blueprint rational Hom groups, final clause
(blueprint: det-sp-rational-localized-hom). -/
abbrev shriek (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification Λ
    (CondensedRing.compactificationOverField f)

/-- The specified natural compact-support comparison, with the chosen Nagata compactification.
Source: blueprint rational Hom groups, final clause
(blueprint: det-sp-rational-localized-hom). -/
def shriekComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    shriek (Profinite.padicIntegersRingObj ℓ E.1) f ⋙ extend Y.left ℓ E ⟶
      extend X.left ℓ E ⋙ shriek (Profinite.continuousMapRingObj E.1) f :=
  letI := HasCompactification.of_over f
  CondensedRing.derivedLowerShriekHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left

/-- The pullback and compact-support claims, using the existing canonical natural maps.
Source: blueprint rational Hom groups, final paragraph
(blueprint: det-sp-rational-localized-hom). -/
def Comparisons (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : Prop :=
    (∀ {X Y : Over (Spec (.of k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      [IsNoetherian X.left] [IsNoetherian Y.left] (f : X ⟶ Y),
      (∀ K₀ : integral Y.left ℓ E, integralConstructible Y.left ℓ E K₀ →
        integralConstructible X.left ℓ E
          ((CondensedRing.moduleObjectDerivedPullback
            (Profinite.padicIntegersRingObj ℓ E.1) f.left).obj K₀) ∧
        rationalConstructible X.left ℓ E
          ((CondensedRing.moduleObjectDerivedPullback
            (Profinite.continuousMapRingObj E.1) f.left).obj
              ((extend Y.left ℓ E).obj K₀))) ∧
      IsIso (Functor.whiskerLeft (integralConstructible Y.left ℓ E).ι
        (CondensedRing.derivedPullIso
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left).inv) ∧
      (∀ M₀ : integral X.left ℓ E, integralConstructible X.left ℓ E M₀ →
        integralConstructible Y.left ℓ E
          ((shriek (Profinite.padicIntegersRingObj ℓ E.1) f).obj M₀) ∧
        rationalConstructible Y.left ℓ E
          ((shriek (Profinite.continuousMapRingObj E.1) f).obj
            ((extend X.left ℓ E).obj M₀))) ∧
      IsIso (Functor.whiskerLeft (integralConstructible X.left ℓ E).ι
        (shriekComparison ℓ E f)))

/-- Hom localization, with its natural map determined on all pure tensors.
Source: blueprint main-20261015, rational Hom groups
(blueprint: det-sp-rational-localized-hom).
Proof: the coefficient localization is the sequential ell-telescope, by
 det-prop-sfb-qlbar-colimit-x-invert-ell. Exact filtered colimits give its derived version.
The derived scalar adjunction identifies rational Hom with integral Hom into this telescope.
Use det-lem-int-ext-continuity with a bounded-below representative of L and common bound
for all telescope terms. This identifies Hom with its ell-localization. Since E=O_E[1/ell],
fractions identify it with tensor E. At stage n a map h is sent to ell^(-n) F(h), with the
canonical shift comparison. This proves the pure-tensor formula and E-linearity.
For essential surjectivity use det-lem-integral-models-generators: lift each generator,
and clear denominators in each arrow using the Hom result, then lift its cone. Scalar
extension preserves the cone triangles; TR3 and lem-sf-triangle-morphism-iso identify the
rational cones. Induct on the finite cone-and-shift construction, starting with zero.
For pullback use sk-def-sfb-coefficient-comparisons (Pull), together with flatness and
sk-prop-sfb-cartesian-coefficients. Integral pullback preserves constructibility by
 det-lem-integral-models-operations. Scalar extension preserves local finite presentations
and cohomological bounds. For lower shriek choose the standing Nagata compactification:
first apply integral extension by zero and proper direct-image preservation. Then apply
 det-pe-bounded-continuity-direct-image to the ell-telescope with a common lower bound.
Restriction of scalars commutes with derived proper pushforward by
 def-sfb-derived-comap-lower-star-iso and reflects quasi-isomorphisms, so (Push) is invertible.
Compose with the canonical open extension-by-zero comparison. The composite is precisely
(Shriek), and its inverse has the orientation stated in the node. Restriction of natural
transformations to the full subcategories gives naturality. -/
theorem rationalLocalizedHom
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [IsNoetherian T] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ K : rational T ℓ E, rationalConstructible T ℓ E K →
      ∃ K₀ : integral T ℓ E, integralConstructible T ℓ E K₀ ∧
        Nonempty ((extend T ℓ E).obj K₀ ≅ K)) ∧
    (∀ K₀ L₀ : integral T ℓ E,
      integralConstructible T ℓ E K₀ → integralConstructible T ℓ E L₀ →
      ∀ q : ℤ, ∃ c :
        (E.1 ⊗[PadicAlgCl.integers ℓ E.1] (K₀ ⟶ L₀⟦q⟧)) ≃ₗ[E.1]
          ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧),
        ∀ (e : E.1) (h : K₀ ⟶ L₀⟦q⟧),
          c (e ⊗ₜ h) = @SMul.smul E.1
            ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧)
            (rationalHomModule T ℓ E _ _).toSMul e
            ((extend T ℓ E).map h ≫ ((extend T ℓ E).commShiftIso q).hom.app L₀)) ∧
    Comparisons ℓ k E := by
  sorry

end AlgebraicGeometry.ProEtale.RationalLocalizedHom
