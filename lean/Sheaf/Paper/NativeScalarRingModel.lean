/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData
public import Sheaf.Paper.NativeProperScalarMateData
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding

/-! # Ring diagrams for native scalar transport

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-sf-native-scalar-ring-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale

/-- The section-ring map for the two actual condensed coefficient inclusions.
Source: Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-sf-native-scalar-ring-model). -/
def nativeScalarSectionMap (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    (T : Scheme.{u}) :
    InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T ⟶
      InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) T :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (CondensedRing.sectionRingMap T
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) T ≫
        coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T))

/-- A ring presentation is natural for the actual adjunct of the inverse-image ring map.
This is a pointwise equality on sections of the base-change site object.
Source: Bhatt--Scholze, Section 6.8; Stacks, Modules on Sites.
(blueprint: lem-sf-native-scalar-ring-model). -/
def NativeScalarRingNaturality (R : PurCompactSupport.Coefficients.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
      InternalModuleOperations.ring Λ T) : Prop :=
  ∀ {U V : Scheme.{u}} (g : U ⟶ V) (W : V.ProEtᵒᵖ)
      (s : (R.ring V).obj.obj W),
    (i U).hom.hom.app ((proEtaleBaseChange g).op.obj W)
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          (R.pull g).hom).hom.app W s) =
      (InternalModuleOperations.coefficientMap Λ g).hom.app W ((i V).hom.hom.app W s)

/-- An ordinary coefficient-ring diagram. Its fields mention neither complexes nor scalar mates.
The two ring isomorphisms identify scalar inclusions and precomposition maps.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-sf-native-scalar-ring-model). -/
structure NativeScalarRingModel (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S) where
  integral : ∀ T : Scheme.{u}, (adicLisseForget T).obj (R.ring T) ≅
    InternalModuleOperations.ring (Profinite.padicIntegersRingObj l E.1) T
  closure : ∀ T : Scheme.{u}, (adicLisseForget T).obj (S.ring T) ≅
    InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) T
  scalar : ∀ T : Scheme.{u},
    (adicLisseForget T).map (a.map T) ≫ (closure T).hom =
      (integral T).hom ≫ nativeScalarSectionMap l E T
  integral_natural : NativeScalarRingNaturality R
    (Profinite.padicIntegersRingObj l E.1) integral
  closure_natural : NativeScalarRingNaturality S (Profinite.padicAlgClRingObj l) closure

namespace NativeScalarRingModel

/-- The integral module equivalence constructed from the supplied ring isomorphism.
Source: Stacks, Modules on Sites, Tag 00YV.
(blueprint: lem-sf-native-scalar-ring-model). -/
def integralEquivalence {l : ℕ} [Fact l.Prime] {E : Index l (PadicAlgCl l)}
    {R S : PurCompactSupport.Coefficients.{u}} {a : PurCompactSupport.Change R S}
    (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    pbcModules T (R.ring T) ≌
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T) :=
  (CondensedRing.ringModuleEquivalenceOfIso T (P.integral T).symm).trans
    (InternalModuleOperations.equivalence (Profinite.padicIntegersRingObj l E.1) T).symm

/-- The native-to-condensed module equivalence constructed from the supplied ring isomorphism.
Source: Stacks, Modules on Sites, Tag 00YV.
(blueprint: lem-sf-native-scalar-ring-model). -/
def closureEquivalence {l : ℕ} [Fact l.Prime] {E : Index l (PadicAlgCl l)}
    {R S : PurCompactSupport.Coefficients.{u}} {a : PurCompactSupport.Change R S}
    (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    pbcModules T (S.ring T) ≌
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) T) :=
  (CondensedRing.ringModuleEquivalenceOfIso T (P.closure T).symm).trans
    (InternalModuleOperations.equivalence (Profinite.padicAlgClRingObj l) T).symm

/-- An equivalence of these abelian categories preserves binary products and zero maps,
so it is additive. Source: Mathlib's additive_of_preserves_binary_products.
(blueprint: lem-sf-native-scalar-ring-model). -/
instance integralEquivalence_additive {l : ℕ} [Fact l.Prime]
    {E : Index l (PadicAlgCl l)} {R S : PurCompactSupport.Coefficients.{u}}
    {a : PurCompactSupport.Change R S} (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    (P.integralEquivalence T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the closure module equivalence, by preservation of products and zero maps.
Source: Mathlib's additive_of_preserves_binary_products.
(blueprint: lem-sf-native-scalar-ring-model). -/
instance closureEquivalence_additive {l : ℕ} [Fact l.Prime]
    {E : Index l (PadicAlgCl l)} {R S : PurCompactSupport.Coefficients.{u}}
    {a : PurCompactSupport.Change R S} (P : NativeScalarRingModel l E a) (T : Scheme.{u}) :
    (P.closureEquivalence T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

end NativeScalarRingModel

/-- The completed/native coefficient change has a natural ordinary ring presentation.

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; the coefficient-identification
steps 1--3 of lem-sf-native-proper-scalar-mate-presentation.
(blueprint: lem-sf-native-scalar-ring-model).

Proof in words:
1. The normalized continuous integral comparison identifies the completed coefficient
ring for Coefficient E with continuous functions into its valuation ring. Shrink.algEquiv
identifies the size model with the original finite subfield. Its algebra linear equivalence
is bicontinuous over the complete base field; uniqueness of the extending absolute value
identifies the valuation subrings. Postcomposition gives the continuous integer-ring sheaf
isomorphism. The pulled condensed integral limit theorem and internal section reconstruction
then give integral. The finite quotient projections fix this isomorphism uniquely.
2. Apply the locally finite coefficient-ring realization and reconstruct its section ring.
Its inverse gives closure. Multiplication and the unit are preserved by the supplied
IsMonHom, so these are ring isomorphisms, not only abelian-sheaf isomorphisms.
3. Obtain a normalized CoefficientPresentation from coefficientPresentations_exists.
The continuous chart comparison commutes with integral inclusion, localization and
inclusion of the finite subfield into the closure. The normalization of CoefficientPresentation
therefore identifies the composite with its integralMap. The hypothesis ha identifies it
with a.map, giving scalar.
4. Take the inverse-image adjuncts. Both ring comparisons send the given coefficient
adjuncts to precomposition on continuous functions, by chart naturality and the native
pull_normalized equation. Equality on every site section proves integral_natural and
closure_natural. Empty schemes and zero section rings require no separate choice. -/
theorem exists_nativeScalarRingModel
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T) :
    Nonempty (NativeScalarRingModel l E a) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
