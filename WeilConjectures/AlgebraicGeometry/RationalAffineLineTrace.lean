/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.SecSmoothPurity.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.RationalTatePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

public import WeilConjectures.CategoryTheory.InverseMateEquivalence

import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.TateTwistLocallyFree
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.RationalLocalizingProjectionFormula
import WeilConjectures.AlgebraicGeometry.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.VectorTraceScalarDescent
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.CondensedSupportProjectionFormula
import WeilConjectures.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.IntegralModels
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstruction
import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability

/-! # The rational affine-line trace over the ground field

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-thm-inversion/
lem-fd-first-formula.proof.md, constant-sheaf paragraph, and
sk-lem-wft-character-integral/lem-fd-character-integral.proof.md, coefficients paragraph.
(blueprint: lem-fd-rational-affine-line-trace).

The target uses the recorded internal signed Tate line in degree two. Its pullback
is transported from the recorded signed comparison, including its evaluation
normalization. No roots of unity or trivialization over k are chosen.

## Main definitions and statement

- `negative`: the recorded internal signed Tate line, shifted by [-2].
- `compactSupport`: the actual affine-line compact-support coefficient object.
- `exchange`: the actual proper/open compact-support exchange on that object.
- `exists_compatible_trace`: a trace family commuting with every field extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u vA vB vC vD uA uB uC uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalAffineLineTrace

open CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

section NativeTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- Typed alias of the recorded native signed line; the object itself is unchanged.
Source: sk-def-sp-tate-twist, signed powers in internal module notation
(blueprint: lem-fd-rational-affine-line-trace). -/
def nativeLine (X : Scheme.{u}) (L : DiagonalCoefficients.Modules Λ X) (d : ℤ) :
    DiagonalCoefficients.Modules Λ X :=
  spInternalSignedTwist X (condensedRingObj Λ X) L d
/-- Native pullback isomorphisms, with the module category fixed before specialization.
Source: sk-prop-sfb-cartesian-coefficients, canonical coefficient-module inverse image
(blueprint: lem-fd-rational-affine-line-trace). -/
def PullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DiagonalCoefficients.Modules Λ Y) (M : DiagonalCoefficients.Modules Λ X) :=
  (CondensedRing.upperStar Λ f).obj L ≅ M
/-- Compare the two recorded direct images by uniqueness of their coefficient adjunct.
Both coefficient maps have precisely the normalization of condensedPushforwardHom.
Source: sk-prop-sfb-cartesian-coefficients, compatibility with the coefficient map
(blueprint: lem-fd-rational-affine-line-trace). -/
@[irreducible]
def coefficientBridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (InternalModuleOperations.equivalence Λ X).functor ⋙
      InternalModuleOperations.lowerStar Λ f ≅
    (InternalModuleOperations.equivalence Λ X).functor ⋙
      Scheme.proEtaleRingModuleDirectImage f _ _
        (spCoefficientIso f Λ) :=
  Functor.isoWhiskerLeft _ (SheafOfModules.pushforwardCongr
    ((InternalModuleOperations.coefficientMap_existsUnique
      Λ f).unique
        (InternalModuleOperations.coefficientMap_existsUnique
          Λ f).exists.choose_spec
        (spCoefficientIso_existsUnique f
          Λ).choose_spec.1))

/-- The unique inverse-image mate of the normalized direct-image comparison.
Source: sk-prop-sfb-cartesian-coefficients, coefficient-module pullback compatibility
(blueprint: lem-fd-rational-affine-line-trace). -/
@[irreducible]
def pullbackBridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙
      (InternalModuleOperations.equivalence Λ X).functor ≅
    (InternalModuleOperations.equivalence Λ Y).functor ⋙
      Scheme.proEtaleRingModulePullback f _ _
        (spCoefficientIso f Λ) :=
  let a := CondensedRing.upperStarLowerStarAdjunction
    Λ f
  let b := Scheme.proEtaleRingModuleAdjunction f _ _
    (spCoefficientIso f Λ)
  let c := InternalModuleOperations.lowerComparison Λ f ≪≫
    coefficientBridge Λ f
  letI := isIso_inverseMate_of_equivalences a b c
  (asIso (((mateEquiv a b).symm c.hom).natTrans)).symm

/-- Transport an isomorphism through the specified equivalences and inverse-image comparison.
The equivalence counits identify the recorded objects; full faithfulness lifts their map.
Source: sk-prop-sfb-cartesian-coefficients, canonical coefficient-module comparison
(blueprint: lem-fd-rational-affine-line-trace). -/
def transportIso
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
    (EA : A ≌ C) (EB : B ≌ D) (L : A ⥤ B) (T : C ⥤ D)
    (i : L ⋙ EB.functor ≅ EA.functor ⋙ T) {P : C} {Q : D}
    (q : T.obj P ≅ Q) : L.obj (EA.inverse.obj P) ≅ EB.inverse.obj Q :=
  EB.functor.preimageIso
    (i.app (EA.inverse.obj P) ≪≫ T.mapIso (EA.counitIso.app P) ≪≫ q ≪≫
      (EB.counitIso.app Q).symm)

/-- Construct the native signed pullback from the recorded signed comparison, using
only the fixed inverse-image mate and the equivalence counits. Thus its actual
sectionwise image is prescribed, including the negative evaluation normalization.
Source: sk-prop-sfb-cartesian-coefficients, powers and duals
(blueprint: lem-fd-rational-affine-line-trace). -/
def signedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (LY : DiagonalCoefficients.Modules Λ Y) (LX : DiagonalCoefficients.Modules Λ X)
    (β : SpSignedComparison f
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) (condensedRingObj Λ Y))
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj Λ X))
      (spCoefficientIso f Λ)
      ((InternalModuleOperations.equivalence Λ Y).functor.obj LY)
      ((InternalModuleOperations.equivalence Λ X).functor.obj LX)) (d : ℤ) :
    PullIso Λ f (nativeLine Λ Y LY d) (nativeLine Λ X LX d) :=
  transportIso (InternalModuleOperations.equivalence Λ Y)
    (InternalModuleOperations.equivalence Λ X) (CondensedRing.upperStar Λ f)
    (Scheme.proEtaleRingModulePullback f _ _ (spCoefficientIso f Λ))
    (pullbackBridge Λ f) (β.signed d)

/-- Canonical degree-zero and shift passage of a native pullback isomorphism.
Source: sk-prop-sfb-cartesian-coefficients, derived signed comparisons
(blueprint: lem-fd-rational-affine-line-trace). -/
def shiftedPullbackHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L : DiagonalCoefficients.Modules Λ Y} {M : DiagonalCoefficients.Modules Λ X}
    (e : PullIso Λ f L M) (n : ℤ) :
    (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor _ 0).obj L) ⟦n⟧) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟦n⟧ :=
  ((moduleObjectDerivedPullback Λ f).commShiftIso n).hom.app _ ≫
    (shiftFunctor _ n).map
      ((Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ f)).hom.app L ≫
        (DerivedCategory.singleFunctor _ 0).map e.hom)

end NativeTransport

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The tensor unit for the published native module-object derived tensor structure.
Source: det-def-sfb-pulled-back-coefficients, regular coefficient module
(blueprint: lem-fd-rational-affine-line-trace). -/
def unit (X : Scheme.{u}) : CondensedOpenProper.D (Profinite.continuousMapRingObj E.1) X :=
  @MonoidalCategory.tensorUnit
    (CondensedOpenProper.D (Profinite.continuousMapRingObj E.1) X) _
    (Mod.derivedMonoidalCategory.toMonoidalCategoryStruct)

/-- The recorded internal signed Tate line E_X(-1), shifted by [-2].
Source: sk-def-sp-tate-twist, signed powers and degree-zero inclusion
(blueprint: lem-fd-rational-affine-line-trace). -/
def negative (X : Scheme.{u}) : CondensedOpenProper.D (Profinite.continuousMapRingObj E.1) X :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (nativeLine (Profinite.continuousMapRingObj E.1) X
      (spRationalTwist X ℓ E) (-1))) ⟦(-2 : ℤ)⟧

/-- The actual compact-support image of the coefficient unit using the standard P1 chart.
Source: lem-fd-first-formula.proof.md, constant-sheaf paragraph
(blueprint: lem-fd-rational-affine-line-trace). -/
def compactSupport (S : Scheme.{u}) :
    CondensedOpenProper.D (Profinite.continuousMapRingObj E.1) S :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (Profinite.continuousMapRingObj E.1)
    (AlgebraicGeometry.affineTraceLineCompactification S)).obj (unit ℓ E _)

/-- The recorded signed comparison, selected with its positive adjunct normalization.
Its negative component is fixed by evaluation, independently of the chosen witness.
Source: sk-prop-sfb-cartesian-coefficients, rational and signed comparisons
(blueprint: lem-fd-rational-affine-line-trace). -/
@[irreducible]
def rationalSignedComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    SpSignedComparison f
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y)
        (condensedRingObj (Profinite.continuousMapRingObj E.1) Y))
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
      (spCoefficientIso f (Profinite.continuousMapRingObj E.1))
      ((InternalModuleOperations.equivalence (Profinite.continuousMapRingObj E.1) Y).functor.obj
        (spRationalTwist Y ℓ E))
      ((InternalModuleOperations.equivalence (Profinite.continuousMapRingObj E.1) X).functor.obj
        (spRationalTwist X ℓ E)) :=
  ((RationalP1.adicComparison ℓ f).integral_rational_cartesian E).2.2.choose

/-- The canonical shifted derived pullback of E(-1)[-2].
Source: sk-prop-sfb-cartesian-coefficients, signed twists and shift comparison
(blueprint: lem-fd-rational-affine-line-trace). -/
@[irreducible]
def negativePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    (moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1) f).obj
      (negative ℓ E Y) ⟶ negative ℓ E X :=
  shiftedPullbackHom (Profinite.continuousMapRingObj E.1) f
    (signedPullback (Profinite.continuousMapRingObj E.1) f
      (spRationalTwist Y ℓ E) (spRationalTwist X ℓ E)
      (rationalSignedComparison ℓ E f) (-1)) (-2)

/-- The same canonical signed comparison for a field extension. Residue invertibility
is derived from the stated prime and characteristic assumptions, rather than assumed.
Source: sk-prop-sfb-cartesian-coefficients, signed twists
(blueprint: lem-fd-rational-affine-line-trace). -/
def fieldNegativePullback (p : ℕ) [Fact p.Prime] (hℓp : ℓ ≠ p)
    (k k' : Type u) [Field k] [Field k'] [CharP k p] [CharP k' p]
    (φ : k →+* k') :
    (moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1)
      (Spec.map (CommRingCat.ofHom φ))).obj (negative ℓ E (Spec (.of k))) ⟶
      negative ℓ E (Spec (.of k')) :=
  letI : ∀ x : Spec (.of k), Invertible (ℓ : (Spec (.of k)).residueField x) :=
    fun x ↦ (RationalP1.residueIsUnit ℓ k p hℓp.symm _ (𝟙 _) x).invertible
  letI : ∀ x : Spec (.of k'), Invertible (ℓ : (Spec (.of k')).residueField x) :=
    fun x ↦ (RationalP1.residueIsUnit ℓ k' p hℓp.symm _ (𝟙 _) x).invertible
  negativePullback ℓ E (Spec.map (CommRingCat.ofHom φ))

/-- The actual proper/open exchange, evaluated at the coefficient unit, followed by
its canonical pullback identification. Both Cartesian witnesses are existing theorems.
Source: det-prop-sf-cbc, definition of the exchange
(blueprint: lem-fd-rational-affine-line-trace). -/
def exchange {S T : Scheme.{u}} (g : T ⟶ S) :
    (moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1) g).obj
      (compactSupport ℓ E S) ⟶ compactSupport ℓ E T :=
  ((compactSupportCondensedFormalism (Profinite.continuousMapRingObj E.1)).shriekBaseChange
    (affineTraceLineCompactification S) (affineTraceLineCompactification T)
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)
    (affineTraceChart_isPullback g) (ProjectiveSpace.isPullback_map _ g)).natTrans.app
      (unit ℓ E (𝔸(PUnit.{u + 1}; S))) ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification (Profinite.continuousMapRingObj E.1)
      (affineTraceLineCompactification T)).map
        (leftDerivedUpperStarUnitIso (Profinite.continuousMapRingObj E.1)
          (AffineSpace.map PUnit.{u + 1} g)).hom

/-- Affine-line trace over every field of characteristic p, with one family compatible
with all field extensions. Both objects belong to the bounded constructible full
subcategory, whose morphisms are the ambient derived morphisms displayed here.
In particular for finite k this is on Spec k itself and retains the Tate Galois action.

Source: lem-fd-first-formula.proof.md, constant-sheaf paragraph, and
lem-fd-character-integral.proof.md, coefficient paragraph
(blueprint: lem-fd-rational-affine-line-trace).

Proof, matching the seven DAG steps:
1. Begin over s0 = Spec F_p. Embed E in the fixed algebraic closure, put R = O_E,
   and choose a uniformizer pi with ell = u pi^e. The rings A_n = R/ell^n = R/pi^(en)
   are finite by def-weil-l-adic-coefficient-extension. The Noetherian base s0 has
   ell^n invertible. Apply lem-amb-affine-space-top-trace in dimension one to obtain
   the projective-line-normalized finite trace Ra0! A_n(1)[2] ≅ A_n.
2. Keep this same compactification. The exact open-extension comparison of
   lem-cbc-proetale-extension-zero-comparison identifies the etale and pro-etale
   open extensions termwise. For the proper qcqs projective-line projection,
   prop-weil-pbc-comparison-direct-image identifies their direct images on this
   bounded-below input. Then lem-sf-module-object-ordinary-coefficient-equivalence
   identifies the coefficient, tensor and actual proper/open composite with the
   native finite module-object construction. Thus these are actual native traces.
3. Put L = R_X0(1)[2] and C = Ra0! L. The Tate sheaf is lisse free of rank one.
   Clause (4) of sk-lem-integral-models and sk-thm-sf-ctf-stability put L and C in
   the bounded constructible finite-Tor category. Clause (2) gives derived
   completeness of C and R_s0. The pi-power and ell-power towers are cofinal.
   The actual scalar mates of sk-prop-scalar-six identify the reductions of C
   with Ra0!,A_n A_n(1)[2]. The source Tate comparisons are the quotient maps on
   compatible roots; on a common trivializing cover this is R tensor_R A_n = A_n.
4. Use det-sp-tower-p1-adjunction to construct the whole-system projective-line
   counit, and compose with the system open-extension counit supplied by
   lem-coef-semilinear-derived-sections. Its evaluated maps are the finite traces
   from step 1, since that normalized trace is precisely this composite counit.
   The equation of lem-pur-vector-trace-scalar-descent identifies the quotient
   comparisons with normalized Tate balancing even for non-flat quotients.
   The scalar mates respect coefficient composition and counits, so this is a map
   from the actual reduction tower of C to that of R_s0. Evaluations detect
   isomorphisms by lem-coef-semilinear-derived-sections. Apply the derived inverse
   limit to the resulting system isomorphism. By sk-lem-sp-tower its completion
   unit is invertible on these bounded constructible objects. This gives
   t_R : C ≅ R_s0; no lifting of a merely levelwise collection of maps is used.
5. Apply ordinary derived extension of scalars R → E. This is a listed coefficient
   map of sk-prop-scalar-six, and its compact-support comparison is invertible on
   these finite-Tor objects. The defining scalar extension of the locally free
   integral Tate line gives E tensor_R R(1) = E(1). Thus
   t_E : Ra0!,E E_X0(1)[2] ≅ E_s0 in the native ordinary derived category.
6. The open projection isomorphism lem-sfb-condensed-support-projection-formula,
   followed by det-thm-sf-pf-field-localizing for the proper projection, identifies
   Ra0! E_X0 tensor E_s0(1)[2] with Ra0! E_X0(1)[2]. The open chart is quasi-compact
   with infinity as closed complement, and its extended unit and Tate line are
   bounded constructible, hence in the required localizing domains. Compose with
   t_E and tensor by E_s0(-1)[-2]. The evaluation isomorphism supplied by
   det-def-sp-tate-twist-locally-free and shift cancellation give I0. This uses
   the actual inverse Tate line, without choosing a trivialization of it.
7. For any k pull I0 along its prime-field map g_k. Clause (b) of det-prop-sf-cbc
   applies to the bounded constructible unit: the original prime-field schemes
   are Noetherian and the new base is arbitrary. Define I_k by inverse exchange,
   followed by Lg_k* I0 and the normalized signed Tate comparison. Both objects
   remain bounded constructible. For every extension h, Cartesian pasting says
   Ex_(g_k') = Ex_h composed with Lh* Ex_(g_k), with the canonical compositors.
   Substitute this into the definition of I_k and use the normalized signed
   coefficient comparisons of sk-prop-sfb-cartesian-coefficients. The result is
   exactly the displayed equation. This never commutes arbitrary pullback with a
   derived inverse limit. In particular for finite k all maps are on Spec k itself
   and therefore retain the Tate Galois action. -/
theorem exists_compatible_trace (p : ℕ) [Fact p.Prime] (hℓp : ℓ ≠ p) :
    ∃ I : ∀ (k : Type u) [Field k] [CharP k p],
      compactSupport ℓ E (Spec (.of k)) ≅ negative ℓ E (Spec (.of k)),
      (∀ (k : Type u) [Field k] [CharP k p],
        boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1)
          (Spec (.of k))) (compactSupport ℓ E (Spec (.of k))) ∧
        boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1)
          (Spec (.of k))) (negative ℓ E (Spec (.of k)))) ∧
      ∀ (k k' : Type u) [Field k] [Field k'] [CharP k p] [CharP k' p]
        (φ : k →+* k'),
        (moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1)
          (Spec.map (CommRingCat.ofHom φ))).map (I k).hom ≫
            fieldNegativePullback ℓ E p hℓp k k' φ =
          exchange ℓ E (Spec.map (CommRingCat.ofHom φ)) ≫ (I k').hom := by
  sorry

end AlgebraicGeometry.ProEtale.RationalAffineLineTrace
