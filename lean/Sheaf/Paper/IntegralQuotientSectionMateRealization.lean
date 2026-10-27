/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.Paper.IntegralQuotientDirectImageComparison
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.Paper.CondensedAmbientExchange

/-! # Integral quotient adjunctions in section coordinates

Source: blueprint main-20261015, integral proper base change proof (3);
Stacks Tags 03EK, 0GMW, 07A6, 07A7, 09T5 and 08BJ
(blueprint: lem-sfb-integral-quotient-section-mate-realization).

The quotient index n denotes exponent n + 1. The section scalar functors are independent
universal derived pairs. Their geometric balancing comparison is normalized by the
identity on sections of the restriction/direct-image composites, and by its K-flat
localization square. No exchange/reduction rectangle is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.IntegralQuotient.SectionMateRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]

/-- The published geometric pullback comparison with the fixed internal endpoint.
Source: Stacks 07A6 and 09T5
(blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
abbrev pull {U V : Scheme.{u}} (f : U ⟶ V) :
    L Λ f ⋙ ModuleRingedComparison.derivedFunctor Λ U ≅
      ModuleRingedComparison.derivedFunctor Λ V ⋙ ModuleRingedComparison.derivedPullback Λ f := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ModuleRingedComparison.derivedPullComparison Λ f

/-- The published geometric direct-image comparison with the fixed internal endpoint.
Source: Stacks 07A6 and 09T5
(blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
abbrev push {U V : Scheme.{u}} (f : U ⟶ V) :
    F Λ f ⋙ ModuleRingedComparison.derivedFunctor Λ V ≅
      ModuleRingedComparison.derivedFunctor Λ U ⋙
        ModuleRingedComparison.derivedPushforward Λ f := by
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact ModuleRingedComparison.derivedPushComparison Λ f

/-- The published geometric compositor with the fixed internal endpoints.
Source: Stacks 07A6 (blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
abbrev compose {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    L Λ (f ≫ g) ≅ L Λ g ⋙ L Λ f := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp Λ f g

/-- The published ambient exchange with the fixed internal endpoint functors.
Source: Stacks 07A7 (blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
abbrev exchange {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    F Λ f ⋙ L Λ g ⟶ L Λ h ⋙ F Λ f' := by
  unfold F L CondensedRing.moduleObjectDerivedPushforward
    CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.condensedAmbientExchange Λ sq

/-- Agreement of the specified geometric adjunction, both unit and counit, all pullback
compositors, and preservation of flat-term K-flat complexes under section reconstruction.
Source: Stacks 07A6, 09T5, 08BJ, 03EK and 0GMW
(blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
def GeometricAgreement : Prop :=
  (∀ {U V : Scheme.{u}} (f : U ⟶ V)
      (M : DerivedCategory (Modules Λ V)) (N : DerivedCategory (Modules Λ U))
      (a : (L Λ f).obj M ⟶ N),
    (ModuleRingedComparison.derivedAdjunction Λ f).homEquiv _ _
        ((pull Λ f).inv.app M ≫ (ModuleRingedComparison.derivedFunctor Λ U).map a) =
      (ModuleRingedComparison.derivedFunctor Λ V).map ((adj Λ f).homEquiv _ _ a) ≫
        (push Λ f).hom.app N) ∧
  (∀ {U V : Scheme.{u}} (f : U ⟶ V) (M : DerivedCategory (Modules Λ V)),
    (ModuleRingedComparison.derivedAdjunction Λ f).unit.app
        ((ModuleRingedComparison.derivedFunctor Λ V).obj M) =
      (ModuleRingedComparison.derivedFunctor Λ V).map ((adj Λ f).unit.app M) ≫
        (push Λ f).hom.app ((L Λ f).obj M) ≫
        (ModuleRingedComparison.derivedPushforward Λ f).map ((pull Λ f).hom.app M)) ∧
  (∀ {U V : Scheme.{u}} (f : U ⟶ V) (N : DerivedCategory (Modules Λ U)),
    (ModuleRingedComparison.derivedAdjunction Λ f).counit.app
        ((ModuleRingedComparison.derivedFunctor Λ U).obj N) =
      (ModuleRingedComparison.derivedPullback Λ f).map ((push Λ f).inv.app N) ≫
        (pull Λ f).inv.app ((F Λ f).obj N) ≫
        (ModuleRingedComparison.derivedFunctor Λ U).map ((adj Λ f).counit.app N)) ∧
  (∀ {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
      (M : DerivedCategory (Modules Λ W)),
    (pull Λ (f ≫ g)).hom.app M ≫
        (ModuleRingedComparison.derivedPullbackComposition Λ f g).hom.app
          ((ModuleRingedComparison.derivedFunctor Λ W).obj M) =
      (ModuleRingedComparison.derivedFunctor Λ U).map
          ((compose Λ f g).hom.app M) ≫
        (pull Λ f).hom.app ((L Λ g).obj M) ≫
        (ModuleRingedComparison.derivedPullback Λ f).map ((pull Λ g).hom.app M)) ∧
  (∀ (T : Scheme.{u}) (P : CochainComplex (Modules Λ T) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := ModuleRingedComparison.ring Λ T)
      (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology T) (R := ModuleRingedComparison.ring Λ T)
      ((ModuleRingedComparison.equivalence Λ T).functor.obj (P.X i))) ∧
        ∀ {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
          {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
          (K : DerivedCategory (Modules Λ X)),
        (pull Λ g).hom.app ((F Λ f).obj K) ≫
            (ModuleRingedComparison.derivedPullback Λ g).map ((push Λ f).hom.app K) ≫
            (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ f)
              (ModuleRingedComparison.derivedAdjunction Λ f')
              (TwoSquare.mk _ _ _ _
                ((ModuleRingedComparison.derivedPullbackComposition Λ f' g).symm ≪≫
                  eqToIso (congrArg
                    (fun k : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback Λ k)
                    sq.toCommSq.w.symm) ≪≫
                  ModuleRingedComparison.derivedPullbackComposition Λ h f).hom)).natTrans.app
                    ((ModuleRingedComparison.derivedFunctor Λ X).obj K) =
          (ModuleRingedComparison.derivedFunctor Λ Y').map
              ((exchange Λ sq).app K) ≫
            (push Λ f').hom.app ((L Λ h).obj K) ≫
            (ModuleRingedComparison.derivedPushforward Λ f').map
              ((pull Λ h).hom.app K)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual reconstructed finite projection, retaining both section-ring endpoints.
Source: Stacks 03EK (blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
abbrev scalarMap (n : ℕ) (T : Scheme.{u}) :
    ModuleRingedComparison.ring (integral l E) T ⟶
      ModuleRingedComparison.ring (finite l E n) T :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (coefficientMap (reduction l E n) T)

/-- The existing normalized section scalar pair at the actual positive quotient projection.
This is only a type alias, with no choice of a derived functor.
Source: Stacks 06YY and 07A6
(blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
abbrev Pair (n : ℕ) (T : Scheme.{u})
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (integral l E) T)]
    [HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (finite l E n) T)] :=
  SheafOfModules.ScalarDerivedPair
    (J := Scheme.ProEt.topology T)
    (R := ModuleRingedComparison.ring (integral l E) T)
    (S := ModuleRingedComparison.ring (finite l E n) T)
    (scalarMap l E n T)

variable (n : ℕ)
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (integral l E) T)]
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (finite l E n) T)]

set_option maxHeartbeats 800000 in
-- The representative square compares two universal localization interfaces.
/-- Scalar reconstruction for the fixed internal universal derived extension and its
specified adjunction, including ordinary generators and the K-flat localization equation.
The restriction comparison is normalized on every section; its derived comparison is its
termwise localization. Agreement of Hom transposes identifies both units and counits.
Source: Stacks 03EK, 0GMW, 06YY, 07A6 and 09T5
(blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
def ScalarAgreement (T : Scheme.{u}) (q : Pair l E n T)
    (e₀ : extension (reduction l E n) T ⋙
        (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
      (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ q.extension)
    (e : D (reduction l E n) T ⋙ ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
      ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ q.derived) : Prop :=
  ∃ r : V₀ (reduction l E n) T ⋙
        (ModuleRingedComparison.equivalence (integral l E) T).functor ≅
      (ModuleRingedComparison.equivalence (finite l E n) T).functor ⋙
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (J := Scheme.ProEt.topology T) (scalarMap l E n T),
    (∀ (N : Modules (finite l E n) T) (U : T.ProEtᵒᵖ) (x : N.X.obj.obj U),
      (r.hom.app N).val.app U x = x) ∧
    (∀ (M : Modules (integral l E) T) (U : T.ProEtᵒᵖ)
        (s : (condensedRingObj (finite l E n) T).obj.obj U) (x : M.X.obj.obj U),
      ((eqToHom (q.extension_obj
          ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj M))).val.app U)
          ((e₀.hom.app M).val.app U
            (InternalAbelianSheafModule.internalScalarGenerator (Scheme.ProEt.topology T)
              (coefficientMap (reduction l E n) T) M U s x)) =
        (toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (scalarMap l E n T)
            ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj M)).presheaf).app U
          (s ⊗ₜ[(ModuleRingedComparison.ring (integral l E) T).obj.obj U,
            ((scalarMap l E n T).hom.app U).hom] x)) ∧
    (∀ (M : Modules (integral l E) T) (N : Modules (finite l E n) T)
        (a : (extension (reduction l E n) T).obj M ⟶ N),
      (ModuleRingedComparison.equivalence (integral l E) T).functor.map
          ((Mod.extendRestrictAdjunction (coefficientMap (reduction l E n) T)).homEquiv _ _ a) ≫
          r.hom.app N =
        q.ordinaryAdjunction.homEquiv _ _
          (e₀.inv.app M ≫ (ModuleRingedComparison.equivalence (finite l E n) T).functor.map a)) ∧
    (∀ P : CochainComplex (Modules (integral l E) T) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (ModuleRingedComparison.derivedFunctor (finite l E n) T).map
          (compute (reduction l E n) T P) ≫
          (Functor.mapDerivedCategoryFactors
            (ModuleRingedComparison.equivalence (finite l E n) T).functor).hom.app
            (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom.app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫
          q.derived.map
            (ModuleRingedComparison.sectionLocalizationComparison (integral l E) T P).hom ≫
          SheafOfModules.scalarPairComplexComparison q.extension q.extension_additive
            q.derived q.counit
            (((ModuleRingedComparison.equivalence (integral l E) T).functor.mapHomologicalComplex
              (.up ℤ)).obj P)) ∧
    (∀ (M : DerivedCategory (Modules (integral l E) T))
        (N : DerivedCategory (Modules (finite l E n) T))
        (a : (D (reduction l E n) T).obj M ⟶ N),
      (ModuleRingedComparison.derivedFunctor (integral l E) T).map
          ((scalarAdj (reduction l E n) T).homEquiv _ _ a) ≫
          ((Functor.mapDerivedCategoryCompIso (V₀ (reduction l E n) T)
              (ModuleRingedComparison.equivalence (integral l E) T).functor).symm ≪≫
            Functor.mapDerivedCategoryNatIso r ≪≫
            Functor.mapDerivedCategoryCompIso
              (ModuleRingedComparison.equivalence (finite l E n) T).functor
              (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
                (J := Scheme.ProEt.topology T) (scalarMap l E n T))).hom.app N =
        q.adjunction.homEquiv _ _
          (e.inv.app M ≫ (ModuleRingedComparison.derivedFunctor (finite l E n) T).map a))

set_option maxHeartbeats 800000 in
-- Both universal counits occur in the same representative comparison.
/-- Independent section balancing: its ordinary map is the conjugate of the identity
on sections of restriction/direct image. The derived comparison localizes precisely
that ordinary map on flat-term K-flat representatives. This fixes the balanced-generator
formula without defining the comparison by internal transport.
Source: Stacks 03EK, 07A6, 07A7 and 09T5
(blueprint: lem-sfb-integral-quotient-section-mate-realization). -/
def BalancingAgreement (q : ∀ T : Scheme.{u}, Pair l E n T)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (χ : (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) f ≅
      ModuleRingedComparison.derivedPullback (integral l E) f ⋙ (q U).derived) : Prop :=
  ∃ r : ModuleRingedComparison.pushforward (finite l E n) f ⋙
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (scalarMap l E n V) ≅
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (scalarMap l E n U) ⋙
        ModuleRingedComparison.pushforward (integral l E) f,
    (∀ (N : ModuleRingedComparison.modules (finite l E n) U) (W : V.ProEtᵒᵖ)
        (x : N.val.obj ((InternalModuleOperations.siteMap f).op.obj W)),
      (r.hom.app N).val.app W x = x) ∧
    ∃ χ₀ : (q V).extension ⋙ ModuleRingedComparison.pullback (finite l E n) f ≅
        ModuleRingedComparison.pullback (integral l E) f ⋙ (q U).extension,
      conjugateIsoEquiv
          ((ModuleRingedComparison.adjunction (integral l E) f).comp
            (q U).ordinaryAdjunction)
          ((q V).ordinaryAdjunction.comp
            (ModuleRingedComparison.adjunction (finite l E n) f)) χ₀ = r.symm ∧
      ∀ P : CochainComplex (ModuleRingedComparison.modules (integral l E) V) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := ModuleRingedComparison.ring (integral l E) V) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := Scheme.ProEt.topology V)
          (R := ModuleRingedComparison.ring (integral l E) V) (P.X i)) →
        χ.hom.app (DerivedCategory.Q.obj P) ≫
            (q U).derived.map
              ((Functor.mapDerivedCategoryFactors
                (ModuleRingedComparison.pullback (integral l E) f)).hom.app P) ≫
            SheafOfModules.scalarPairComplexComparison (q U).extension
              (q U).extension_additive (q U).derived (q U).counit
              (((ModuleRingedComparison.pullback (integral l E) f).mapHomologicalComplex
                (.up ℤ)).obj P) =
          (ModuleRingedComparison.derivedPullback (finite l E n) f).map
              (SheafOfModules.scalarPairComplexComparison (q V).extension
                (q V).extension_additive (q V).derived (q V).counit P) ≫
            (ModuleRingedComparison.pullback (finite l E n) f).mapDerivedCategoryFactors.hom.app
              ((SheafOfModules.scalarComplex (q V).extension (q V).extension_additive).obj P) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso χ₀ (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (Iso.refl (ModuleRingedComparison.pullback (integral l E) f ⋙
                  (q U).extension)) (.up ℤ)).inv.app P)

/-- The fixed normalized internal balancing and its direct-image mate have their
independently normalized section realizations, and the same comparisons identify every
ambient geometric exchange. The assertion is on the entire unbounded categories.
The quantified scalar pairs are presentations of the specified ordinary sheafified
extension and its universal derived adjunction, not arbitrary functors or adjunctions.

Source: blueprint main-20261015, integral proper base change proof (3);
Stacks 03EK, 0GMW, 07A6, 07A7, 09T5 and 08BJ
(blueprint: lem-sfb-integral-quotient-section-mate-realization).

Proof:
1. Apply lem-pe-internal-section-tensor-comparison to both coefficient rings on each
small pro-etale site. The size convention and sk-def-sfb-sheaf-tensor supply its size and
monoidal-local-equivalence hypotheses. The termwise reconstruction preserves flatness,
acyclicity and K-flatness, hence flat-term K-flat representatives.
2. Apply lem-pd-section-derived-pushpull-normalization to the integral condensed ring
and its finite quotient separately. It identifies the specified geometric adjunctions,
units, counits and all pullback compositors with the independently derived section ones.
3. Apply lem-sfb-internal-section-scalar-adjunction to the actual coefficient projection.
The ordinary comparison preserves balanced generators and both scalar Hom transposes.
Its localization on flat-term K-flat representatives gives e and identifies the derived
scalar transposes. Symmetry converts left tensor notation to right tensor notation.
4. Apply lem-sfb-internal-scalar-pullback-normalization to continuous reduction. By
sk-def-sfb-pulled-back-coefficients and det-prop-sfb-qlbar-colimit-x-integral-limit this is
the actual finite projection, and sk-prop-sfb-cartesian-coefficients identifies its
geometric coefficient maps. The ordinary section balancing is uniquely the conjugate
of identity on restriction/direct-image sections: its formula pulls back both balanced
generators. Localizing on K-flat representatives gives precisely chi and the displayed
pullback comparison equation, with no coefficient-flatness hypothesis.
5. Expand rho using def-weil-pbc-adjunction-mate: insert the finite geometric unit,
apply balancing and the reduced integral counit. Steps 2--4 identify each factor with
the corresponding section factor, giving equality with the independently formed mate.
6. For a chosen Cartesian square, expand def-weil-pbc-ambient-ringed-exchange as its
unit--square--counit formula. Step 2 identifies the two geometric compositors, the
commutativity identification, and both adjunctions. Substitution gives exactly the
section mate below, separately for integral and finite coefficients. No exchange is
inverted and no properness, completeness or constructibility restriction is used. -/
theorem integral_quotient_section_mate_realization
    (q : ∀ T : Scheme.{u}, Pair l E n T)
    (b : ∀ {U V : Scheme.{u}} (f : U ⟶ V),
      D (reduction l E n) V ⋙ L (finite l E n) f ≅
        L (integral l E) f ⋙ D (reduction l E n) U)
    (hb : ∀ {U V : Scheme.{u}} (f : U ⟶ V),
      PullNormalized (reduction l E n) f (b f)) :
    GeometricAgreement (integral l E) ∧ GeometricAgreement (finite l E n) ∧
    ∃ e₀ : ∀ T : Scheme.{u},
        extension (reduction l E n) T ⋙
            (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
          (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ (q T).extension,
    ∃ e : ∀ T : Scheme.{u},
        D (reduction l E n) T ⋙ ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
          ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ (q T).derived,
      (∀ T : Scheme.{u}, ScalarAgreement l E n T (q T) (e₀ T) (e T)) ∧
    ∃ χ : ∀ {U V : Scheme.{u}} (f : U ⟶ V),
        (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) f ≅
          ModuleRingedComparison.derivedPullback (integral l E) f ⋙ (q U).derived,
      (∀ {U V : Scheme.{u}} (f : U ⟶ V), BalancingAgreement l E n q f (χ f)) ∧
      (∀ {U V : Scheme.{u}} (f : U ⟶ V)
          (M : DerivedCategory (Modules (integral l E) V)),
        (pull (finite l E n) f).hom.app ((D (reduction l E n) V).obj M) ≫
            (ModuleRingedComparison.derivedPullback (finite l E n) f).map ((e V).hom.app M) ≫
            (χ f).hom.app ((ModuleRingedComparison.derivedFunctor (integral l E) V).obj M) =
          (ModuleRingedComparison.derivedFunctor (finite l E n) U).map ((b f).hom.app M) ≫
            (e U).hom.app ((L (integral l E) f).obj M) ≫
            (q U).derived.map ((pull (integral l E) f).hom.app M)) ∧
      (∀ {U V : Scheme.{u}} (f : U ⟶ V)
          (K : DerivedCategory (Modules (integral l E) U)),
        (ModuleRingedComparison.derivedFunctor (finite l E n) V).map
            ((rho (reduction l E n) f (b f)).app K) ≫
            (push (finite l E n) f).hom.app ((D (reduction l E n) U).obj K) ≫
            (ModuleRingedComparison.derivedPushforward (finite l E n) f).map
              ((e U).hom.app K) =
          (e V).hom.app ((F (integral l E) f).obj K) ≫
            (q V).derived.map ((push (integral l E) f).hom.app K) ≫
            (mateEquiv (ModuleRingedComparison.derivedAdjunction (integral l E) f)
              (ModuleRingedComparison.derivedAdjunction (finite l E n) f)
              (TwoSquare.mk _ _ _ _ (χ f).hom)).natTrans.app
                ((ModuleRingedComparison.derivedFunctor (integral l E) U).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralQuotient.SectionMateRealization
