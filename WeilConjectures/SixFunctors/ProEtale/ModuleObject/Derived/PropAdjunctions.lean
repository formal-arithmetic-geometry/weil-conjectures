/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Adjunctions of the six-functor datum

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/`
`sec-sbc-uniform/sk-thm-sbc-coefficients/fix-prop-adjunctions.md`, clauses (1)--(4).
Source place: the `fix-prop-adjunctions` unit (blueprint: fix-prop-adjunctions).
Proof source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/`
`sec-sbc-uniform/sk-thm-sbc-coefficients/fix-prop-adjunctions.proof.md`, Steps 1--4.

The statement keeps the finite coefficient `A_(E,n) = Padic.coefficientExtensionRing ℓ E n`
and the bound condensed operation datum `S` in scope.  Clause (1) is the actual restriction
of the canonical derived adjunction.  Clause (2) records the finite exceptional adjunction,
the canonical finite refinement witness, the condensed operation adjunction, its Dctf
restriction, and the canonical condensed refinement comparison.  Clause (3) uses the
canonical pullback and derived-direct-image compositors together with the normalized
compact-support composition compositor on the actual separated finite-type models.
Clause (4) records both exchange mates and the projection map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two triangle identities for a specified adjunction. -/
def adjunctionTriangles {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) : Prop :=
  (∀ K : C,
      L.map (a.unit.app K) ≫ a.counit.app (L.obj K) = 𝟙 (L.obj K)) ∧
    ∀ K : D,
      a.unit.app (R.obj K) ≫ R.map (a.counit.app K) = 𝟙 (R.obj K)

/-- Restriction of a specified ambient adjunction along the actual full inclusions. -/
def restrictedAdjunctionOf {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (L : C ⥤ D) (R : D ⥤ C) (a : L ⊣ R) : Prop :=
  ∃ hL : ∀ K, P K → Q (L.obj K),
    ∃ hR : ∀ K, Q K → P (R.obj K),
      let L' := Q.lift (P.ι ⋙ L) (fun K ↦ hL K.obj K.property)
      let R' := P.lift (Q.ι ⋙ R) (fun K ↦ hR K.obj K.property)
      adjunctionTriangles
        (a.restrictFullyFaithful (iC := P.ι) (iD := Q.ι) (L := L') (R := R')
          (ObjectProperty.fullyFaithfulι P) (ObjectProperty.fullyFaithfulι Q)
          (ObjectProperty.liftCompιIso Q (P.ι ⋙ L) _).symm
          (ObjectProperty.liftCompιIso P (Q.ι ⋙ R) _).symm)

/-- Agreement of an ambient adjunction with a specified full-subcategory adjunction.
The two comparison isomorphisms transport the ambient unit and counit to the specified
restricted unit and counit; this prevents a merely existential ambient adjunction from
being substituted for the operation datum's normalized adjunction. -/
def adjunctionRestrictionAgreement {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {L' : P.FullSubcategory ⥤ Q.FullSubcategory}
    {R' : Q.FullSubcategory ⥤ P.FullSubcategory} (b : L' ⊣ R') : Prop :=
  ∃ eL : P.ι ⋙ L ≅ L' ⋙ Q.ι,
    ∃ eR : Q.ι ⋙ R ≅ R' ⋙ P.ι,
      (∀ K, a.unit.app (P.ι.obj K) ≫ R.map (eL.hom.app K) ≫
          eR.hom.app (L'.obj K) = P.ι.map (b.unit.app K)) ∧
      ∀ M, L.map (eR.hom.app M) ≫ eL.hom.app (R'.obj M) ≫
          Q.ι.map (b.counit.app M) = a.counit.app (Q.ι.obj M)

/-- Unit and counit compatibility for the canonical comparison of two refinement
adjunctions.  The comparison maps are part of the statement, so the equations cannot
be discharged by choosing an unrelated adjunction. -/
def adjunctionRefinementPasting {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (θ : L₁ ≅ L₂) (ρ : R₂ ≅ R₁) : Prop :=
  (∀ K, b.unit.app K ≫ ρ.hom.app (L₂.obj K) =
      a.unit.app K ≫ R₁.map (θ.hom.app K)) ∧
    ∀ M, L₁.map (ρ.hom.app M) ≫ a.counit.app M =
      θ.hom.app (R₂.obj M) ≫ b.counit.app M

/-- The finite exceptional pair, including its finite-Tor restriction. -/
def finiteExceptionalAdjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  ∃ hF : ∀ K, intrinsicFiniteTorsionConstructible ℓ E n hn X K →
      intrinsicFiniteTorsionConstructible ℓ E n hn Y
        ((@sfIntrinsicCompactSupport _ _ f c (Padic.coefficientExtensionRing ℓ E n) _
          (Padic.finite_coefficientExtensionRing ℓ E n hn)).obj K),
    ∃ hG : ∀ K, intrinsicFiniteTorsionConstructible ℓ E n hn Y K →
      intrinsicFiniteTorsionConstructible ℓ E n hn X
        ((finiteExceptionalInverseImage ℓ E n hn k X Y f).obj K),
      ∃ a :
        (intrinsicFiniteTorsionConstructible ℓ E n hn Y).lift
            ((intrinsicFiniteTorsionConstructible ℓ E n hn X).ι ⋙
              @sfIntrinsicCompactSupport _ _ f c (Padic.coefficientExtensionRing ℓ E n) _
                (Padic.finite_coefficientExtensionRing ℓ E n hn))
            (fun K ↦ hF K.obj K.property) ⊣
          (intrinsicFiniteTorsionConstructible ℓ E n hn X).lift
            ((intrinsicFiniteTorsionConstructible ℓ E n hn Y).ι ⋙
              finiteExceptionalInverseImage ℓ E n hn k X Y f)
            (fun K ↦ hG K.obj K.property),
        adjunctionTriangles a ∧
          (∀ K, WeilConjectures.finiteTorConstructible ℓ E n hn X K →
            WeilConjectures.finiteTorConstructible ℓ E n hn Y
              ((@sfIntrinsicCompactSupport _ _ f c (Padic.coefficientExtensionRing ℓ E n) _
                (Padic.finite_coefficientExtensionRing ℓ E n hn)).obj K)) ∧
          (∀ K, WeilConjectures.finiteTorConstructible ℓ E n hn Y K →
            WeilConjectures.finiteTorConstructible ℓ E n hn X
              ((finiteExceptionalInverseImage ℓ E n hn k X Y f).obj K))

/-- The finite-level unit and counit comparison required for a compactification
refinement.  The comparison is the canonical finite-origin comparison of
`rightDerivedLowerShriekOfCompactification`, and the two adjunctions are the concrete
class adjunctions induced by the étale compactification adjunctions at `c` and `d`.
Their right sides are transported through `ν^* ⊣ Rν_*` and are compared by the
conjugate of the displayed left comparison; no unrelated adjunction is quantified.
This is the finite refinement clause of `fix-prop-adjunctions` (blueprint:
`fix-prop-adjunctions`), at the source place
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/`
`sec-sbc-uniform/sk-thm-sbc-coefficients/fix-prop-adjunctions.md`, clause (2). -/
def finiteExceptionalRefinementAgreement
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  ∀ {d : Compactification f} (r : c ⟶ d),
    let B : Type u := Padic.coefficientExtensionRing ℓ E n
    letI : Finite B := Padic.finite_coefficientExtensionRing ℓ E n hn
    let A : Type (u + 1) := ULift.{u + 1} B
    letI : HasCompactification f := c.hasCompactification
    letI : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    let hG_c : ∀ L : DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)),
        DerivedCategory.TStructure.t.plus L →
          DerivedCategory.TStructure.t.plus
            ((AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification A c).obj L) := by
      intro L hL
      let adj := AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction A c
      obtain ⟨N, hN⟩ :=
        AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj A c
      obtain ⟨n, hn⟩ := hL
      exact ⟨n - N, adj.isGE_obj_of_isLE _ _ N hN L n⟩
    let hG_d : ∀ L : DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)),
        DerivedCategory.TStructure.t.plus L →
          DerivedCategory.TStructure.t.plus
            ((AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification A d).obj L) := by
      intro L hL
      let adj := AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction A d
      obtain ⟨N, hN⟩ :=
        AlgebraicGeometry.Etale.exists_isLE_rightDerivedLowerShriekOfCompactification_obj A d
      obtain ⟨n, hn⟩ := hL
      exact ⟨n - N, adj.isGE_obj_of_isLE _ _ N hN L n⟩
    let a_c :=
      AlgebraicGeometry.ProEtale.rightDerivedUpperShriekOfAdjunctionClassAdjunction
        (AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction A c)
        hG_c
    let a_d :=
      AlgebraicGeometry.ProEtale.rightDerivedUpperShriekOfAdjunctionClassAdjunction
        (AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction A d)
        hG_d
    let θ := AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso
      A c d
    let ρ := (conjugateIsoEquiv a_c a_d θ.symm).symm
    adjunctionRefinementPasting a_c a_d θ ρ

/-- The unit and counit pasting equations for an explicitly specified compositor.
The compositor is the mate `conjugateIsoEquiv` of the displayed left-composition iso. -/
def adjunctionCompositionPasting {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {T : C ⥤ E} {U : E ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : T ⊣ U)
    (α : L₁ ⋙ L₂ ≅ T) : Prop :=
  (∀ K, c.unit.app K ≫
      (conjugateIsoEquiv c (a.comp b) α).hom.app (T.obj K) =
        (a.comp b).unit.app K ≫ (R₂ ⋙ R₁).map (α.hom.app K)) ∧
    ∀ N, (L₁ ⋙ L₂).map ((conjugateIsoEquiv c (a.comp b) α).hom.app N) ≫
        L₂.map (a.counit.app (R₂.obj N)) ≫ b.counit.app N =
      α.hom.app (U.obj N) ≫ c.counit.app N

/-- The canonical mate equation for a square transformation. -/
def exchangeMateEquation {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (square : TwoSquare G L₁ L₂ H)
    (e : R₁ ⋙ G ⟶ H ⋙ R₂) : Prop :=
  e = (mateEquiv a b square).natTrans

/-- The exceptional composition law, written with the compositor supplied by the
composition datum.  The two component equations are the unit and counit pasting
formulas for the exceptional pair; the caller supplies the canonical compositor from
the compact-support composition law. -/
def exceptionalAdjunctionCompositionPasting {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {T : C ⥤ E} {U : E ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : T ⊣ U)
    (α : L₁ ⋙ L₂ ≅ T) (β : U ≅ R₂ ⋙ R₁) : Prop :=
  (β = conjugateIsoEquiv c (a.comp b) α) ∧ ((∀ K, c.unit.app K ≫ β.hom.app (T.obj K) =
      (a.comp b).unit.app K ≫ (R₂ ⋙ R₁).map (α.hom.app K)) ∧
    (∀ N, (L₁ ⋙ L₂).map (β.hom.app N) ≫
        L₂.map (a.counit.app (R₂.obj N)) ≫ b.counit.app N =
      α.hom.app (U.obj N) ≫ c.counit.app N))

/-- The actual exceptional-inverse-image transpose of a compact-support exchange.
First transpose the exchange through the two compact-support adjunctions, then
transpose the resulting square through the two pullback/direct-image adjunctions.
This gives the orientation `R g'_* R f'^! ⟶ R f^! R g_*` from clause (4). -/
def exceptionalExchangeTransposeMap {C : Type u₁} {D : Type u₂}
    {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F} {U : E ⥤ C} {V : F ⥤ D}
    (pullbackLeft : L₁ ⊣ R₁) (pullbackRight : L₂ ⊣ R₂)
    (exceptionalLeft : G ⊣ U) (exceptionalRight : H ⊣ V)
    (square : TwoSquare G L₁ L₂ H) : V ⋙ R₁ ⟶ R₂ ⋙ U :=
  (mateEquiv exceptionalRight exceptionalLeft
    (TwoSquare.mk _ _ _ _ ((mateEquiv pullbackLeft pullbackRight square).natTrans))).natTrans

end AlgebraicGeometry.ProEtale.CondensedRing
