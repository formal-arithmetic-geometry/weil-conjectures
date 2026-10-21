/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.FiniteComparisonCoefficients
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.FiniteDiscreteCondensedRing
public import Sheaf.Paper.FiniteDiscreteSchemeRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Sheaf.Paper.FiniteComparisonPresentation
import Sheaf.Paper.FiniteComparisonFaithful

/-!
# Finite coefficient comparison on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-comparison/
sk-prop-ctf-finite-comparison-localizing.md
(blueprint: det-ctf-finite-comparison-localizing).

## Main definitions

* `finiteComparisonRealization`: the specified finite-discrete coefficient transport.
* `finiteComparisonEtaleClosure`, `finiteComparisonProEtaleClosure`: the two closures.
* `finiteComparisonOpenIso`, `finiteComparisonCompactSupportMap`: the canonical arrows.

## Main statements

* `finiteComparisonRealization_exact`: exactness of the specified coefficient transport.
* `finiteComparisonLocalizing`: the equivalence and its compatibility with operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject

section LocalizingArgument
universe w v₁ v₂
namespace CategoryTheory

variable {C : Type w} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem closureLocalizing (S : ObjectProperty C) :
    IsLocalizingSubcategory (localizingClosure S) := by
  have hiso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  let := hiso
  have hzero : (localizingClosure S).ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hzero
  have hshift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    rw [ObjectProperty.prop_shift_iff]
    intro P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)
  let := hshift
  have htri : (localizingClosure S).IsTriangulated := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    apply ObjectProperty.le_isoClosure
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS)
  refine ⟨htri, hiso, ?_⟩
  intro I F hF hK
  change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → _
  intro P hP hS
  exact hP.2.2 F hF (fun i ↦ hK i P hP hS)

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.2.2 (G ⋙ F) inferInstance hPG)

private theorem imageLocalizing (P : ObjectProperty C) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [Coreflective F] (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.map F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I H hH hPH
  let := hH
  have hHF (j : Discrete I) : F.essImage (H.obj j) := by
    obtain ⟨K, _, e⟩ := hPH j.as
    exact ⟨K, e⟩
  let G := Functor.essImage.liftFunctor H F hHF
  let e := Functor.essImage.liftFunctorCompIso H F hHF
  let : HasColimit (G ⋙ F) := hasColimit_of_iso e
  let : HasColimit G := hasColimit_of_coreflective G F
  have hPG (i : I) : P (G.obj (Discrete.mk i)) := by
    obtain ⟨K, hK, ⟨iK⟩⟩ := hPH i
    exact P.prop_of_iso (F.preimageIso (iK ≪≫ (e.app (Discrete.mk i)).symm)) hK
  refine ⟨colimit G, hP.2.2 G inferInstance hPG, ⟨?_⟩⟩
  exact (preservesColimitIso F G) ≪≫ HasColimit.isoOfNatIso e


private theorem closureEquivalence (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [Coreflective F]
    (hS : ∀ K, S K → localizingClosure T (F.obj K))
    (hT : ∀ K, T K → (localizingClosure S).map F K) :
    ∃ hpres : ∀ K, localizingClosure S K → localizingClosure T (F.obj K),
      ((localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence := by
  have hpres (K : C) (hK : localizingClosure S K) :
      localizingClosure T (F.obj K) := by
    exact hK ((localizingClosure T).inverseImage F)
      (inverseImageLocalizing _ _ (closureLocalizing T)) hS
  refine ⟨hpres, ?_⟩
  let H := (localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  have himage (K : D) (hK : localizingClosure T K) :
      (localizingClosure S).map F K :=
    hK _ (imageLocalizing _ F (closureLocalizing S)) hT
  have : H.EssSurj := by
    constructor
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := himage K.obj K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact { }

end CategoryTheory
end LocalizingArgument

namespace AlgebraicGeometry.ProEtale


variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]
variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- The canonical open-extension comparison, applied termwise and localized.
Source: blueprint finite comparison, Operations; Stacks Tag 09AF
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- For the chosen open/proper factorization, the compact-support comparison is exactly
alpha at j_! K followed by Rp_* of the open comparison. All values are ambient.
Source: blueprint finite comparison, final paragraph of proof
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonCompactSupportMap {X P Y : Scheme.{u}} (j : X ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :=
  unboundedDirectImageComparisonMap (ULift.{u + 1} B) p
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory.obj K) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) p).rightDerivedFunctor.map
      ((finiteComparisonOpenIso B j).hom.app K)

/-- The finite-Tor constructible generators correspond under the comparison functor.
Source: blueprint finite comparison, opening paragraph
(blueprint: lem-ctf-finite-comparison-generators).

Proof: apply the finite Noetherian coefficient comparison to the coefficient-sized small
site models, then transport its restricted equivalence through the constant-scalar
presentations, site equivalences, and the specified finite discrete scheme-ring
isomorphism. These transports preserve constructibility, finite Tor amplitude, and the
ambient derived comparison, yielding both generator inclusions. The empty scheme and
zero ring are included by the same equivalence argument. -/
theorem finiteComparisonGenerators_identification (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
      finiteComparisonEtaleGenerators B X K →
        finiteComparisonProEtaleGenerators B eR X
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory.obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))),
      finiteComparisonProEtaleGenerators B eR X K →
        (finiteComparisonEtaleGenerators B X).map
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory K) := by
  let A := ULift.{u + 1} B
  let : IsNoetherianRing A := inferInstance
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let E := (finiteComparisonEtaleModelRealization X A).mapDerivedCategory
  let G := (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  obtain ⟨D, hD, _, H, ⟨hH⟩⟩ := finiteTorComparisonNoetherian.{u, u + 1} X A
  obtain ⟨hE, hG⟩ := finiteComparisonPresentation B X eR
  obtain ⟨esquare⟩ := finiteComparisonModelDerivedSquare X A D hD
  constructor
  · intro K hK
    rw [← hE] at hK
    obtain ⟨L, hL, ⟨eL⟩⟩ := hK
    rw [← hG]
    let L' := H.functor.obj ⟨L, hL⟩
    refine ⟨L'.obj, L'.property, ⟨?_⟩⟩
    exact G.mapIso (hH.app ⟨L, hL⟩) ≪≫
      (esquare.app L).symm ≪≫ F.mapIso eL
  · intro K hK
    rw [← hG] at hK
    obtain ⟨M, hM, ⟨eM⟩⟩ := hK
    let M' := H.inverse.obj ⟨M, hM⟩
    refine ⟨E.obj M'.obj, ?_, ⟨?_⟩⟩
    · rw [← hE]
      exact ⟨M'.obj, M'.property, ⟨Iso.refl _⟩⟩
    · exact esquare.app M'.obj ≪≫ G.mapIso (hH.app M').symm ≪≫
        G.mapIso (ObjectProperty.ι _ |>.mapIso (H.counitIso.app ⟨M, hM⟩)) ≪≫ eM

/-- Comparison identifies the two localizing closures, exactly and with ambient sums,
and the canonical pullback, direct-image, open-extension and compact-support comparisons
are invertible on the indicated inputs. No stability assertion for direct images occurs.

Source: blueprint main-20261015, sk-prop-ctf-finite-comparison-localizing.md and its proof
(blueprint: det-ctf-finite-comparison-localizing).

Proof, following the node's five steps:
1. The finite-discrete condensed-ring and scheme-ring identifications transport module
   actions exactly, preserving sums, tensor and the finite constant models. The unbounded
   site comparison is exact, fully faithful and sum-preserving
   (lem-sfb-unbounded-site-comparison). The finite Noetherian coefficient comparison
   det-pe-finite-tor-comparison-noetherian identifies the Dctf generators.
2. The inverse image of the pro-etale closure is replete, triangulated and sum-closed.
   It contains the etale generators, so the defining intersection of
   sk-def-localizing-closure gives preservation of the etale closure.
3. The replete essential image of that closure is sum-closed and shift-closed.
   Fullness lifts any arrow between image objects, and exactness sends its cone to
   a cone of the given arrow. Thus the essential image is triangulated, including zero
   from the empty sum. It contains all pro-etale generators by step 1. Minimality gives
   the reverse inclusion. Full faithfulness restricts, giving the equivalence; triangles
   and sums are the ambient ones.
4. The pullback square is sk-thm-pe-direct-image-comparison. For open extension use
   lem-cbc-proetale-extension-zero-comparison and the two extension-exactness nodes:
   applying the sheaf isomorphism degreewise gives a natural complex isomorphism and
   exactness descends it through quasi-isomorphisms. For finite-type direct image use
   lem-sfb-unbounded-direct-image-comparison. Restrict these ambient maps to closure inputs.
5. For a chosen compactification compose alpha on j_! K with Rp_* of the open
   comparison. Both factors are isomorphisms in the ambient category, naturally in K.
   Their composite is exactly the stipulated comparison for Rf_! = Rp_* j_!; no closure
   stability of direct image is used. -/
theorem finiteComparisonLocalizing
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    ∃ hpres : ∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
        finiteComparisonEtaleClosure B X K →
          finiteComparisonProEtaleClosure B eR X
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.obj K),
      ((finiteComparisonProEtaleClosure B eR X).lift
        ((finiteComparisonEtaleClosure B X).ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence ∧
      (∀ T : Triangle (Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X T.obj₁ →
        finiteComparisonEtaleClosure B X T.obj₂ →
        finiteComparisonEtaleClosure B X T.obj₃ →
        T ∈ distTriang _ →
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          X).mapDerivedCategory.mapTriangle.obj T) ∈ distTriang _) ∧
      (∀ (I : Type (u + 2)) (K : I → Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        (∀ i : I, finiteComparisonEtaleClosure B X (K i)) →
        ∀ c : Cofan K, IsColimit c → finiteComparisonEtaleClosure B X c.pt ∧
          Nonempty (IsColimit
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.mapCocone c))) ∧
      (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (g : X ⟶ Y) [g.IsOver (Spec (.of k))] [LocallyOfFiniteType g] [QuasiCompact g],
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y,
          finiteComparisonEtaleClosure B Y K →
          IsIso ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g).hom.app K)) ∧
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
          finiteComparisonEtaleClosure B X K →
          IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} B) g K))) ∧
      (∀ (U : Scheme.{u}) [U.Over (Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
        (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) U),
        finiteComparisonEtaleClosure B U K → IsIso ((finiteComparisonOpenIso B j).hom.app K)) ∧
      (∀ (P Y : Scheme.{u}) [P.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (j : X ⟶ P) (r : P ⟶ Y) [j.IsOver (Spec (.of k))] [r.IsOver (Spec (.of k))]
        [IsOpenImmersion j] [IsProper r]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X K →
          IsIso (finiteComparisonCompactSupportMap B j r K)) := by
  let A : Type (u + 1) := ULift.{u + 1} B
  have hA : ∃ n : ℕ, (ℓ : A) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, ULift.ext _ _ hn⟩
  let : CharP k p :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap (ZMod p) k)) p
  have hunit : IsUnit (algebraMap ℤ k (ℓ : ℤ)) := by
    rw [map_natCast, isUnit_iff_ne_zero]
    change (ℓ : k) ≠ 0
    intro hzero
    exact hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
      ((CharP.cast_eq_zero_iff k p ℓ).mp hzero)).symm
  let : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  obtain ⟨hFF⟩ := finiteComparisonOrdinary_fullyFaithful A k
    (Or.inr inferInstance) hunit hA X
  let : F.Full := hFF.full
  let : F.Faithful := hFF.faithful
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  let : Coreflective F := { R := _, adj := adj }
  obtain ⟨hgen, hgen'⟩ := finiteComparisonGenerators_identification B eR X
  obtain ⟨hpres, hequiv⟩ := closureEquivalence
    (finiteComparisonEtaleGenerators B X) (finiteComparisonProEtaleGenerators B eR X) F
    (fun K hK P _ hP ↦ hP _ (hgen K hK))
    (fun K hK ↦ by
      obtain ⟨L, hL, e⟩ := hgen' K hK
      exact ⟨L, fun P _ hP ↦ hP _ hL, e⟩)
  refine ⟨hpres, hequiv, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _ _ _ hT
    exact F.map_distinguished T hT
  · intro I K hK c hc
    let S := finiteComparisonEtaleClosure B X
    have hloc : IsLocalizingSubcategory S := closureLocalizing _
    let := hloc.2.1
    let : HasColimit (Discrete.functor K) := ⟨c, hc⟩
    refine ⟨S.prop_of_iso
      ((colimit.isColimit _).coconePointUniqueUpToIso hc)
      (hloc.2.2 (Discrete.functor K) inferInstance hK), ?_⟩
    exact ⟨isColimitOfPreserves F hc⟩
  · intro Y _ _ _ g _ _ _
    constructor
    · intro K _
      infer_instance
    · intro K _
      exact unboundedDirectImageComparison k (Or.inr inferInstance) hunit A hA g K
  · intro U _ _ _ j _ _ K _
    infer_instance
  · intro P Y _ _ _ _ _ _ j r _ _ _ _ K _
    unfold finiteComparisonCompactSupportMap
    have := unboundedDirectImageComparison k (Or.inr inferInstance) hunit A hA r
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)
    infer_instance

end AlgebraicGeometry.ProEtale
