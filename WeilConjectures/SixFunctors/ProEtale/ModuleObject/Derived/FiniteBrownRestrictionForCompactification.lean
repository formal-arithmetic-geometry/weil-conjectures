/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityFiniteComparison.NativeFiniteAdjunctionRestrictions
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer

/-! # Brown restriction for a chosen compactification

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-et-proet/
det-sp-et-proet-adjunction-transfer.proof.md, second paragraph, invoking the
finite-coefficient restriction theorem sk-prop-sf-rf-shriek-preservation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 2000000 in
-- The proof transports the restricted adjunction through several derived equivalences.
/-- The existing finite-coefficient restriction theorem for any chosen compactification.
An invertible coefficient exponent is the only characteristic input to its proof.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-et-proet/
det-sp-et-proet-adjunction-transfer.proof.md, second paragraph, using the finite
restriction theorem sk-prop-sf-rf-shriek-preservation
(blueprint: lem-sp-finite-brown-restriction-compactification).

Proof: use the ordinary finite-coefficient restriction theorem for this compactification.
The constant-model encoding identifies its constructible finite-Tor predicate with the
native predicate and identifies compact support. Transport the restricted adjunction.
The counit transpose into the supplied Brown value is an isomorphism: its Hom maps on
all shifted generators are bijections, so its cone is zero in their localizing closure.
Repleteness then puts the Brown value in the native Dctf category. This is the existing
restriction proof, reused without the unnecessary positive-characteristic or boundary
compactification inputs. It applies to zero coefficients and empty schemes as well.
-/
theorem finiteBrownRestrictionForCompactification
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [HasInvertibleExponent (ULift.{u + 1} A) Y]
    (c : Compactification f)
    (h : ∀ K, localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X K →
      localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y
        ((rightDerivedLowerShriekOfCompactification
          (FiniteDiscreteOrdinary.coefficient A) c).obj K))
    (J : (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).FullSubcategory ⥤
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).FullSubcategory)
    (adj : localizingLowerShriek (FiniteDiscreteOrdinary.coefficient A) c h ⊣ J) :
    ∀ N : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) Y,
      constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X
          (J.obj ((SmoothPurityFiniteComparison.ctfToLocalizing A Y).obj N)).obj ∧
        _root_.DerivedCategory.finiteTorAmplitude _
          (J.obj ((SmoothPurityFiniteComparison.ctfToLocalizing A Y).obj N)).obj := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : HasCompactification f := c.hasCompactification
  obtain ⟨E, hE, hcomp⟩ := FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence A
  let P (T : Scheme.{u}) := constantModelBoundedConstructible
    (Profinite.continuousCoefficientRingObj A) T ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
  let Q := ordinaryProperty A
  have hX (K) : P X K ↔ Q X ((E X).fixedDerived.functor.obj K) :=
    ((hE X).2.2.2.2.1 K).trans (ordinary_ctf_iff A X _)
  have hY (K) : P Y K ↔ Q Y ((E Y).fixedDerived.functor.obj K) :=
    ((hE Y).2.2.2.2.1 K).trans (ordinary_ctf_iff A Y _)
  let eX : (P X).FullSubcategory ≌ (Q X).FullSubcategory :=
    (E X).fixedDerived.congrFullSubcategory (by
      funext K
      exact propext (hX K).symm)
  let eY : (P Y).FullSubcategory ≌ (Q Y).FullSubcategory :=
    (E Y).fixedDerived.congrFullSubcategory (by
      funext K
      exact propext (hY K).symm)
  let F := rightDerivedLowerShriekOfCompactification
    (Profinite.continuousCoefficientRingObj A) c
  obtain ⟨cf⟩ := hcomp X Y f c
  obtain ⟨hOrd, ROrd, ⟨aOrd⟩⟩ := ordinary_small_adjunction A k
    (Y ↘ Spec (.of k)) f c
  have hF (K) (hK : P X K) : P Y (F.obj K) :=
    (hY _).mpr ((Q Y).prop_of_iso (cf.app K).symm (hOrd _ ((hX K).mp hK)))
  let L := (P Y).lift ((P X).ι ⋙ F) (fun M ↦ hF M.obj M.property)
  let LOrd := (Q Y).lift ((Q X).ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)
      (fun M ↦ hOrd M.obj M.property)
  let comm : L ⋙ eY.functor ≅ eX.functor ⋙ LOrd :=
    ((Q Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (P X).ι cf)
  let R := eY.functor ⋙ ROrd ⋙ eX.inverse
  let ae : (eX.functor ⋙ LOrd) ⋙ eY.inverse ⊣ R :=
    (eX.toAdjunction.comp aOrd).comp eY.symm.toAdjunction
  let el : (eX.functor ⋙ LOrd) ⋙ eY.inverse ≅ L :=
    Functor.isoWhiskerRight comm.symm eY.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L eY.unitIso.symm ≪≫ Functor.rightUnitor L
  let a : L ⊣ R := ae.ofNatIsoLeft el
  have hIso : (P X).IsClosedUnderIsomorphisms := ⟨fun e hK ↦
    (hX _).mpr ((Q X).prop_of_iso ((E X).fixedDerived.functor.mapIso e) ((hX _).mp hK))⟩
  have hShift : (P X).IsStableUnderShift ℤ := by
    refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
    exact (hX _).mpr ((Q X).prop_of_iso
      (((E X).fixedDerived.functor.commShiftIso n).app K).symm
      (((hX K).mp hK).shift n))
  intro N
  exact AdjunctionTransfer.rightAdjoint_preserves_generators (P X) (P Y) F hF h R a J adj N

end AlgebraicGeometry.ProEtale.CondensedRing
