/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingSmoothLocalFormula
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-!
# Finite-coefficient exceptional inverse image on the localizing closure

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, statement and proof
(blueprint: sk-prop-sf-rf-shriek-preservation).

The small categories are the inverse images of the recorded Dctf object property under
inclusion of the localizing closures. The smooth formula is stated after trivializing the
actual comparison-pulled-back Tate line on one common etale cover, independently of the input
complex. This is the local coordinate form of tensoring with that line and shifting by 2d.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem ordinary_constructible_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

private theorem ordinary_ctf_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    FiniteDiscreteOrdinary.ordinaryCtf A T K ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  have hb : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
    constructor
    · rintro ⟨hb, hc⟩
      apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A) hb
      intro n
      exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} A)
        ((ordinary_constructible_iff A T _).mp (hc n))
    · intro h
      have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
      exact ⟨hi.1, fun n ↦ (ordinary_constructible_iff A T _).mpr (hi.2 n)⟩
  exact and_congr hb Iff.rfl

private theorem coefficient_exponent (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (A : Type u) [CommRing A]
    (hA : ∃ r : ℕ, ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0) :
    HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) := by
  obtain ⟨r, hr⟩ := hA
  have hℓ : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime)
      (Fact.out : ringChar k ≠ ℓ)
  exact ⟨ℓ ^ r, pow_pos (Fact.out : ℓ.Prime).pos _, hr,
    by
      simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
        (Scheme.ΓSpecIso (.of k)).inv.hom⟩

private abbrev ordinaryProperty (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T

private def ordinary_compactification_iso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (c : Compactification f) :
    (ordinaryProperty A X).ι ⋙
        ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ≅
      (ordinaryProperty A X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let P := DerivedCategory.plusEtaleOrigin B X
  let E := (comparisonUpperStarPlusEtaleOrigin B X).asEquivalence
  let I : (ordinaryProperty A X).FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.ιOfLE (fun _ hK ↦ hK.plusEtaleOrigin)
  let O := I ⋙ E.inverse
  let e : O ⋙ DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar B X).mapDerivedCategory ≅ (ordinaryProperty A X).ι :=
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight E.counitIso P.ι)
  exact (Functor.isoWhiskerRight e (ProEtale.rightDerivedLowerShriek B f)).symm ≪≫
    Functor.isoWhiskerLeft O (rightDerivedLowerShriekCompactificationIso
      (ULift.{u + 1} A) c) ≪≫
    Functor.isoWhiskerRight e (ProEtale.rightDerivedLowerShriekOfCompactification B c)

private theorem ordinary_small_adjunction
    (A : Type u) [CommRing A] [Finite A] (k : Type u) [Field k]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [QuasiCompact s]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [HasInvertibleExponent (ULift.{u + 1} A) Y] (c : Compactification f) :
    ∃ (hF : ∀ K, ordinaryProperty A X K → ordinaryProperty A Y
          ((ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K))
      (R : (ordinaryProperty A Y).FullSubcategory ⥤
        (ordinaryProperty A X).FullSubcategory),
      Nonempty ((ordinaryProperty A Y).lift ((ordinaryProperty A X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)
        (fun K ↦ hF K.obj K.property) ⊣ R) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Q := ordinaryProperty A Y
  let P := ordinaryProperty A X
  let e := ordinary_compactification_iso A f c
  have hf := fun K (hK : P K) ↦ constructibleFiniteTor_rightDerivedLowerShriek
    (ULift.{u + 1} A) s f hK
  have hc (K) (hK : P K) : Q
      ((ProEtale.rightDerivedLowerShriekOfCompactification B c).obj K) :=
    Q.prop_of_iso (e.app ⟨K, hK⟩) (hf K hK)
  let R := P.lift (Q.ι ⋙ ProEtale.rightDerivedUpperShriek (ULift.{u + 1} A) f)
    (fun K ↦ constructibleFiniteTor_rightDerivedUpperShriek (ULift.{u + 1} A) s f K.property)
  let L := Q.lift (P.ι ⋙ ProEtale.rightDerivedLowerShriek B f)
    (fun K ↦ hf K.obj K.property)
  let Lc := Q.lift (P.ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification B c)
    (fun K ↦ hc K.obj K.property)
  let ec : L ≅ Lc := (Q.fullyFaithfulι.whiskeringRight _).preimageIso e
  exact ⟨hc, R, ⟨(DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction
    (ULift.{u + 1} A) s f).ofNatIsoLeft ec⟩⟩

/-- Pull back the existing Dctf object property along the localizing inclusion. This changes
only its ambient category: boundedness, constant-model constructibility and the Tor test are
exactly those of `ConstantModelConstructibleFiniteTor`.
Source: blueprint sk-prop-sf-rf-shriek-preservation, first two displays
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
abbrev localizingDctfProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    ObjectProperty (localizingClosureProEtale Λ T).FullSubcategory :=
  fun K ↦ (constantModelBoundedConstructible Λ T ⊓
    fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K.obj

/-- The specified nonnegative pro-etale Tate line, in fixed-scalar coordinates: apply the
exact site-comparison inverse image to the recorded ordinary etale Tate twist. `ULift`
places A in the sheaf coefficient universe and changes no scalar or module.
Source: blueprint sk-prop-sf-rf-shriek-preservation, final paragraph
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
def finiteShriekProEtaleTateLine (T : Scheme.{u}) (A : Type u) [CommRing A]
    (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (d : ℕ) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj
    (finiteEtaleTateTwist T N (ULift.{u + 1} A) hA d)

/-- The finite-coefficient right adjoint preserves Dctf, its given adjunction restricts to
Dctf, and for a smooth map of dimension d it is etale locally the twisted shifted pullback.
The last clause chooses one cover trivializing the actual pro-etale Tate line, then states
the natural isomorphism in those coordinates. Tensoring with the chosen trivialization and
the tensor unitors recovers exactly `f^*(-)(d)[2d]`; conversely the stated local twist formula
can be untwisted on a common refinement. No canonical global orientation is asserted.
Source: blueprint main-20261015, sk-prop-sf-rf-shriek-preservation, entire statement
(blueprint: sk-prop-sf-rf-shriek-preservation).

Proof:
1. The ordinary finite-coefficient library already proves compact-support preservation,
exceptional preservation, and the restricted adjunction. Its proofs use the closed-support
triangle, smooth tensor duality, affine charts and finite-cover gluing, as required here.
2. Identify the ordinary constructibility convention of the coefficient encoding with the
source library's bounded-constructible finite-Tor property. The intrinsic constructibility
comparison and bounded constructible etale origin supply this identification.
3. Compare the source compact-support functor with the chosen compactification on bounded
etale-origin objects. Transport its restricted adjunction through the finite-discrete
coefficient equivalences and their compact-support comparison.
4. Transpose the small counit under the given large adjunction. Postcomposition with this
map induces bijections on Hom from every shifted generator. Its cone lies in the localizing
closure and has zero Hom from the generators. The left orthogonal of its shift closure is
localizing by the coproduct universal property; hence its identity vanishes. The zero-cone
criterion makes the comparison invertible and gives preservation by the given right adjoint.
5. Restrict the given adjunction through the fully faithful inclusions. Its hom equivalence
is the original hom equivalence: expanding the restricted unit removes only identity maps.
6. Apply the separate smooth-local-formula lemma for the common-cover tensor calculation.
-/
theorem localizingExceptionalAdjoint_preserves_finiteConstructible
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (_hA : ∃ r : ℕ, ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X K →
      localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y
        ((rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj A) c.obj.obj).obj K))
    (G : (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory
      ⥤ (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).FullSubcategory)
    (adj : localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h ⊣ G) :
    ∃ (hF : ∀ M : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
          X).FullSubcategory,
        localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y
          ((localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h).obj
            M.obj))
      (hG : ∀ K : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
          Y).FullSubcategory,
        localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X (G.obj K.obj)),
      (∃ adjSmall :
        (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).lift
            ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X).ι ⋙
              localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h) hF ⊣
          (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X).lift
            ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙ G) hG,
        ∀ (M : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
              X).FullSubcategory)
          (K : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
              Y).FullSubcategory)
          (a : (localizingLowerShriek (Profinite.continuousCoefficientRingObj A)
            c.obj.obj h).obj M.obj ⟶ K.obj),
          (adjSmall.homEquiv M K (ObjectProperty.homMk a)).hom =
            adj.homEquiv M.obj K.obj a) ∧
      ∀ (d : ℕ) [SmoothOfRelativeDimension d f]
        (r : ℕ) (hAr : ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0),
        ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
          Nonempty
            ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝒰.f i)).obj
                (finiteShriekProEtaleTateLine X A (ℓ ^ r) hAr d) ≅
              (constantSheaf (Scheme.ProEt.topology (𝒰.X i))
                (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
                  (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) ∧
          Nonempty
            ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                G ⋙ (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).ι ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory ≅
              (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) f).mapDerivedCategory ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory ⋙
                shiftFunctor _ (2 * (d : ℤ))) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : HasCompactification f := c.obj.obj.hasCompactification
  have : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) :=
    coefficient_exponent ℓ k A _hA
  have : HasInvertibleExponent (ULift.{u + 1} A) Y :=
    HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
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
    (Profinite.continuousCoefficientRingObj A) c.obj.obj
  obtain ⟨cf⟩ := hcomp X Y f c.obj.obj
  obtain ⟨hOrd, ROrd, ⟨aOrd⟩⟩ := ordinary_small_adjunction A k
    (Y ↘ Spec (.of k)) f c.obj.obj
  have hF (K) (hK : P X K) : P Y (F.obj K) :=
    (hY _).mpr ((Q Y).prop_of_iso (cf.app K).symm (hOrd _ ((hX K).mp hK)))
  let L := (P Y).lift ((P X).ι ⋙ F) (fun M ↦ hF M.obj M.property)
  let LOrd := (Q Y).lift ((Q X).ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.obj.obj)
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
  have hG (K : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
      Y).FullSubcategory) :
      localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X (G.obj K.obj) := by
    exact AdjunctionTransfer.rightAdjoint_preserves_generators (P X) (P Y) F hF h R a G adj
      ⟨K.obj.obj, K.property⟩
  refine ⟨(fun M ↦ hF M.obj.obj M.property), hG, ?_, ?_⟩
  · let Ls := (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).lift
      ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X).ι ⋙
        localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h)
        (fun M ↦ hF M.obj.obj M.property)
    let Rs := (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X).lift
      ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙ G) hG
    let asmall : Ls ⊣ Rs := adj.restrictFullyFaithful
      (localizingDctfProperty _ X).fullyFaithfulι
      (localizingDctfProperty _ Y).fullyFaithfulι (Iso.refl _) (Iso.refl _)
    refine ⟨asmall, ?_⟩
    intro M K v
    dsimp only [asmall]
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
    change adj.unit.app M.obj ≫ G.map (𝟙 _) ≫ G.map v ≫ 𝟙 _ = _
    rw [G.map_id]
    erw [Category.comp_id, Category.id_comp]
    exact (adj.homEquiv_unit M.obj K.obj v).symm
  · intro d _ r hAr
    exact localizingExceptionalAdjoint_smoothLocalFormula ℓ k A f c h G adj d r hAr

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Transport through several concrete derived equivalences needs additional elaboration steps.
end AlgebraicGeometry.ProEtale.CondensedRing
