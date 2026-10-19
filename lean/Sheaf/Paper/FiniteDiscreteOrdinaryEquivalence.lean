/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Paper.FiniteDiscreteSchemeRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.SheafTensor
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.Paper.FiniteDiscreteCoefficientSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Paper.CondensedModuleDerivedPushpull

/-! # Finite discrete internal and ordinary coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, coefficient-identification step
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The already defined continuous condensed coefficient ring.
Source: blueprint coefficient identification
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev coefficient := Profinite.continuousCoefficientRingObj A

/-- The pulled-back internal module category, without boundedness or completion.
Source: blueprint coefficient identification
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev Internal (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (coefficient A) T)

/-- Ordinary modules over the constant commutative ring sheaf, in the scalar universe.
Source: blueprint coefficient identification
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev Ordinary (T : Scheme.{u}) :=
  realizationModules (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- The reconstructed commutative section-ring sheaf of the pulled-back coefficients.
Source: Stacks 00YV, section-action equivalence
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev sectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)

/-- Constant functions, as a map into the actual continuous condensed sheaf.
Source: blueprint proof step 1, constant-section normalization
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def pointConstants :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (coefficient A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The canonical constant-coefficient map: sheafify constant functions on the point,
then apply the monoidal inverse image and its constant-sheaf comparison.
Source: blueprint proof step 1
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def canonicalAbelianMap (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ condensedRingObj (coefficient A) T :=
  (constantSchemeIso T).hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
    (upperStarFromPoint T).map
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (coefficient A)).symm (pointConstants A))

/-- The intrinsic-to-fixed coefficient functor restricts to constant scalar sections.
The commutative-ring/underlying-ring constant-sheaf comparison is canonical.
Source: blueprint proof step 3, Stacks 03CY
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def fixedRestriction (T : Scheme.{u}) :
    Ordinary A T ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (ULift.{u + 1} A))) ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- Restrict the section-action equivalence along the specified coefficient isomorphism.
Source: blueprint proof step 2, Stacks 00YV
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def sectionEncoding (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T) :
    Internal A T ⥤ Ordinary A T :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
    (condensedRingObj (coefficient A) T)).functor ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)

/-- The two coefficient presentations and their actual section-action functors.
The ring isomorphism is normalized by the canonical constant-function map; the
forward intrinsic functor is precisely section-action followed by scalar restriction.
The fixed scalar encoding likewise restricts along the constant-sheaf unit.
Source: blueprint proof steps 1--3, Stacks 00YV and 03CY
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
structure Encoding (T : Scheme.{u}) where
  ringIso : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T
  normalization : ∀ (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A),
    ringIso.hom.hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    (canonicalAbelianMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)
  ordinary : Internal A T ≌ Ordinary A T
  ordinary_functor : ordinary.functor = sectionEncoding A T ringIso
  fixed : Ordinary A T ≌
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))
  fixed_functor : fixed.functor = fixedRestriction A T
  [ordinaryAdditive : ordinary.functor.Additive]
  [ordinaryInverseAdditive : ordinary.inverse.Additive]
  [fixedAdditive : fixed.functor.Additive]
  [fixedInverseAdditive : fixed.inverse.Additive]

attribute [instance] Encoding.ordinaryAdditive Encoding.ordinaryInverseAdditive
  Encoding.fixedAdditive Encoding.fixedInverseAdditive

/-- Termwise extension of the specified intrinsic equivalence to unbounded derived categories.
Source: blueprint proof step 4, Stacks 015F
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def Encoding.ordinaryDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌ Scheme.proEtaleDerivedCategory T A :=
  letI := HasDerivedCategory.standard (Ordinary A T)
  e.ordinary.mapDerivedCategory

/-- Termwise extension to fixed scalar sheaves, using the same intrinsic equivalence.
Source: blueprint proof steps 3--4, Stacks 015F
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def Encoding.fixedDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  (e.ordinary.trans e.fixed).mapDerivedCategory

/-- The canonical shift comparison on the actual termwise derived functor.
Source: blueprint proof step 4 and Stacks 015F
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
instance Encoding.fixedDerivedShift {T : Scheme.{u}} (e : Encoding A T) :
    e.fixedDerived.functor.CommShift ℤ := by
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  change (e.ordinary.trans e.fixed).functor.mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The ordinary finite constant local models: on each member of one pro-etale cover
there is a constant finite module. Over a finite ring, finite modules are precisely
finitely presented modules. This is the ordinary side of the source's local-model clause.
Source: blueprint proof step 9 and sk-def-sfb-constructible, clause 1
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryLocalModel (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : C.I₀,
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C.f i)).obj M ≅
        (constantSheaf (Scheme.ProEt.topology (C.X i))
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)

/-- The ordinary finite stratification condition in the same scalar presentation.
Source: sk-def-sfb-constructible, clause 2, and blueprint proof step 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryStratified (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ S : Scheme.Stratification T, ∀ a : Fin S.n,
    ordinaryLocalModel A (S.domain a)
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion a)).obj M)

open Classical in
/-- Qcqs schemes use finite constructible stratifications; otherwise use every affine open.
Source: sk-def-sfb-constructible, clause 2, and blueprint proof step 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryConstructible (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  if CompactSpace T ∧ QuasiSeparatedSpace T then ordinaryStratified A T M
  else ∀ U : T.Opens, IsAffineOpen U → ordinaryStratified A U.toScheme
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U.ι).obj M)

/-- The ordinary bounded constructible predicate in the fixed scalar presentation.
Source: sk-def-sfb-constructible, final paragraph, and blueprint proof step 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryBoundedConstructible (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    ordinaryConstructible A T ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The ordinary bounded constructible finite-Tor predicate, without a fixed Tor bound.
Source: sk-def-sfb-constructible, final paragraph, and blueprint proof steps 7 and 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryCtf (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  ordinaryBoundedConstructible A T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K

/-- Finite discrete condensed and ordinary coefficients agree, including the exact
section-action equivalence, its actual unbounded termwise extension, relative derived
tensor, every ordered Tor interval, finite local models, bounded constructible finite-Tor
objects, triangulated and coproduct structure, localizing closures, and the two composites
for each fixed compactification.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, coefficient-identification step
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence).

Proof following the twelve DAG steps:
1. The finite-discrete condensed-ring constant comparison and its scheme inverse-image
comparison give the normalized ringIso. The canonical map is sheafified constant functions
followed by constantSchemeIso and upperStarFromPoint. Zero rings and empty schemes are allowed.
2. Apply def-weil-pbc-internal-abelian-sheaf-module-equivalence and restrict scalars along
ringIso. The maps and underlying abelian sheaves are identical. Both functors are additive
and inverse equivalences preserve kernels and cokernels, hence are exact.
3. Restrict to constant scalars to identify the intrinsic module category with fixed scalar
module sheaves (lem-cbc-constant-ring-module-sheaves). Conversely local scalar sections act
by gluing constant actions. The unit and counit are identity on underlying sections.
4. Apply lem-sf-exact-functor-derived-triangulated to the two additive equivalences and
inverses. Units and counits extend termwise and descend through quasi-isomorphisms. Homology,
shifts and distinguished triangles are preserved.
5. Apply lem-pe-internal-section-tensor-comparison. Its local pure-tensor comparison is the
identity. Restriction along ringIso preserves the same balancing relations and coherence.
6. The equivalences preserve coproducts by their Hom bijections. Their termwise comparisons
therefore identify direct-sum total tensors, including their signed differential. The cited
tensor comparison preserves and reflects acyclicity and K-flatness. The mapping-cone test
identifies this K-flatness with def-sfb-preserves-kflat-quasi-iso. Compute both relative derived
tensors on the same K-flat resolution to obtain the monoidal derived comparison.
7. Every module sheaf in degree zero corresponds in both directions. Tensor comparison and
homology compatibility identify all zero tests outside each specified interval. This is
exactly def-weil-proetale-tor-amplitude in intrinsic coordinates, and the generic Tor predicate
in fixed scalar coordinates. No test sheaf or interval is omitted.
8. lem-weil-pbc-finite-discrete-coefficient-sections identifies the scalar maps under every
scheme pullback. Adjoint transposition gives compatibility of ringIso with inverse image.
The balanced tensor description then identifies both module pullbacks.
9. A finite presentation over A is the cokernel of a finite scalar matrix. Both encodings
send it to the identical matrix, and sheafification preserves cokernels. Thus the same cover
trivializes the constant models. Over finite A, finite and finitely presented modules agree.
Apply this on the same constructible locally closed strata, and affine-locally on arbitrary
schemes. Homology and Tor compatibility identify the bounded constructible finite-Tor objects.
10. The derived equivalence preserves shifts, triangles, isomorphisms and small coproducts.
Transport the subcategories in the intersection defining sk-def-localizing-closure. Apply
the same argument to the inverse to obtain equality of localizing-closure membership.
11. Both direct images have sections M(V times_T U). The coefficient-sections equation
identifies their actions. For an open immersion both extensions by zero are left adjoint
to the same restriction, so adjunction uniqueness identifies them naturally.
12. Each equivalence is right adjoint to its exact inverse and hence preserves K-injectives
by lem-weil-pbc-right-adjoint-preserves-kinjective. Compute direct images on corresponding
K-injective resolutions, then compose with the termwise exact extension-by-zero comparison.
This gives exactly Rp_*D(j_!) and Rp_*j_! for the same specified compactification.
-/
theorem moduleObject_ordinary_coefficient_equivalence [Finite A] [DiscreteTopology A] :
    ∃ E : ∀ T : Scheme.{u}, Encoding A T,
      (∀ T : Scheme.{u},
        Nonempty ((E T).fixedDerived.functor.Monoidal) ∧
        (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
          (DerivedCategory.torAmplitudeIn _ a b K ↔
            Scheme.HasProEtaleTorAmplitude T A ((E T).ordinaryDerived.functor.obj K) a b)) ∧
        (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
          (DerivedCategory.torAmplitudeIn _ a b K ↔ DerivedCategory.torAmplitudeIn _ a b
            ((E T).fixedDerived.functor.obj K))) ∧
        (∀ M : Internal A T,
          HasFiniteConstantLocalModel (coefficient A) T M ↔
            ordinaryLocalModel A T (((E T).ordinary.functor ⋙ (E T).fixed.functor).obj M)) ∧
        (∀ K : DerivedCategory (Internal A T),
          (constantModelBoundedConstructible (coefficient A) T K ∧
            DerivedCategory.finiteTorAmplitude _ K) ↔
              ordinaryCtf A T ((E T).fixedDerived.functor.obj K)) ∧
        Nonempty ((E T).fixedDerived.functor.CommShift ℤ) ∧
        (E T).fixedDerived.functor.IsTriangulated ∧
        PreservesColimitsOfSize.{u + 1, u + 1} (E T).fixedDerived.functor ∧
        (∀ K : DerivedCategory (Internal A T),
          localizingClosureProEtale (coefficient A) T K ↔
            CategoryTheory.localizingClosure (ordinaryCtf A T)
              ((E T).fixedDerived.functor.obj K))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f),
        Nonempty (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
            (E Y).fixedDerived.functor ≅
          (E X).fixedDerived.functor ⋙
            rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
