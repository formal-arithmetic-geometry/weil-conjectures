/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts
import Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Continuity of the open-proper-closed composite

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`, (2),
first paragraph on exact functors preserving sums.
(blueprint: lem-sfb-qcqs-proper-open-boundary-functor)

The coproduct assertion is preservation of every ambient discrete colimit with
summands in the localizing hull. This expresses invertibility of the canonical
coprojection comparison, including for the empty family, without choosing sums.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual module inverse images are exact lifts of abelian inverse image;
open extension and closed inverse image are triangulated and preserve ambient sums.
Open extension maps the constructible finite-Tor localizing hull into the target hull,
and the open-proper-closed composite is triangulated and preserves its ambient sums.

Source: blueprint main-20261015, `det-sf-comp-coherence-refinement.proof.md`, (2),
first paragraph (blueprint: lem-sfb-qcqs-proper-open-boundary-functor).

Proof plan:
1. `lem-weil-pbc-sheaf-tensor-closed` and `lem-sfb-modobj-grothendieck` make all
   module categories Grothendieck. `sk-def-sfb-derived-categories` supplies
   K-injective resolutions and the ambient unbounded derived categories and sums.
2. The untwisted part of `sk-prop-sfb-cartesian-coefficients` identifies the actual
   module inverse images with lifts of exact abelian inverse images.
   `sk-def-sfb-module-lower-shriek` gives exact open extension, left adjoint to
   open inverse image. `lem-sf-exact-functor-derived-triangulated` makes both
   exact termwise derived functors triangulated.
3. Their underived adjunctions, from `sk-def-sfb-module-lower-shriek` and
   `sk-def-sfb-module-pushforward-pullback`, imply preservation of small sums by
   `lem-weil-pbc-left-adjoint-preserves-colimits`. Apply
   `lem-pur-exact-derived-coproducts` to obtain preservation of ambient derived sums.
4. `lem-sfb-qc-open-extension-ctf` sends every finite constant-model constructible
   finite-Tor generator into the corresponding target generators.
   Pulling back each replete localizing property along open extension and using
   the defining intersection transports the localizing hull.
5. Apply `lem-sfb-qcqs-proper-localizing-coproducts` to the images of the summands
   under open extension. `lem-pc-right-derived-functor-triangulated` makes the
   proper middle factor triangulated. Compose the three coproduct isomorphisms.
   Their composites with each coprojection are the image of that coprojection,
   so the composite is the canonical comparison. The argument also applies to
   the empty family, without bounds, completeness, or a relation of the images. -/
theorem qcqs_proper_open_boundary_functor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S X Y V C : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f]
    (e : V ⟶ X) [IsOpenImmersion e] [QuasiCompact e]
    (c : C ⟶ Y) [IsClosedImmersion c] (hc : IsCompact (Set.range c)ᶜ) :
    (PreservesFiniteLimits (upperStar Λ e) ∧
      PreservesFiniteColimits (upperStar Λ e) ∧
      Nonempty (upperStar Λ e ⋙ Mod.forget (condensedRingObj Λ V) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ ProEtale.upperStar Ab.{u + 1} e)) ∧
    (PreservesFiniteLimits (upperStar Λ c) ∧
      PreservesFiniteColimits (upperStar Λ c) ∧
      Nonempty (upperStar Λ c ⋙ Mod.forget (condensedRingObj Λ C) ≅
        Mod.forget (condensedRingObj Λ Y) ⋙ ProEtale.upperStar Ab.{u + 1} c)) ∧
    (openImmersionLowerShriek Λ e).mapDerivedCategory.IsTriangulated ∧
    (upperStar Λ c).mapDerivedCategory.IsTriangulated ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (openImmersionLowerShriek Λ e).mapDerivedCategory) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (upperStar Λ c).mapDerivedCategory) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)),
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ V ⊓
        fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K →
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X ⊓
        fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
        ((openImmersionLowerShriek Λ e).mapDerivedCategory.obj K)) ∧
    (∃ (_ : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ V ⊓
          fun K ↦ DerivedCategory.finiteTorAmplitude _ K)).IsTriangulated),
      ((localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ V ⊓
          fun K ↦ DerivedCategory.finiteTorAmplitude _ K)).ι ⋙
        (openImmersionLowerShriek Λ e).mapDerivedCategory ⋙
        (lowerStar Λ f).rightDerivedFunctor ⋙
        (upperStar Λ c).mapDerivedCategory).IsTriangulated) ∧
    (∀ (I : Type (u + 1))
      (K : I → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))),
      (∀ t : I, localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ V ⊓
          fun L ↦ DerivedCategory.finiteTorAmplitude _ L) (K t)) →
      PreservesColimit (Discrete.functor K)
        ((openImmersionLowerShriek Λ e).mapDerivedCategory ⋙
          moduleObjectDerivedPushforward Λ f ⋙ (upperStar Λ c).mapDerivedCategory)) := by
  have _hc := hc
  let A (T : Scheme.{u}) :=
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  have hcop (T : Scheme.{u}) : HasCoproducts.{u + 1} (A T) := by
    have : HasColimitsOfSize.{u + 1, u + 1} (A T) :=
      IsGrothendieckAbelian.hasColimits (A T)
    exact fun I ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  let J := (openImmersionLowerShriek Λ e).mapDerivedCategory
  let R := moduleObjectDerivedPushforward Λ f
  let B := (upperStar Λ c).mapDerivedCategory
  have hJ (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) J := by
    have : PreservesColimitsOfSize.{u + 1, u + 1} (openImmersionLowerShriek Λ e) :=
      (openImmersionLowerShriekUpperStarAdjunction Λ e).leftAdjoint_preservesColimits
    exact Functor.mapDerivedCategory_preservesCoproducts _ I
  have hB (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) B := by
    have : PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ c) :=
      (upperStarLowerStarAdjunction Λ c).leftAdjoint_preservesColimits
    exact Functor.mapDerivedCategory_preservesCoproducts _ I
  have hexact {T T' : Scheme.{u}} (g : T ⟶ T') :
      PreservesFiniteLimits (upperStar Λ g) ∧
      PreservesFiniteColimits (upperStar Λ g) ∧
      Nonempty (upperStar Λ g ⋙ Mod.forget (condensedRingObj Λ T) ≅
        Mod.forget (condensedRingObj Λ T') ⋙ ProEtale.upperStar Ab.{u + 1} g) := by
    refine ⟨inferInstance, inferInstance, ⟨?_⟩⟩
    exact Functor.isoWhiskerRight (cartesianCoefficientPullbackIso Λ g) _
  let G (T : Scheme.{u}) : ObjectProperty (DerivedCategory (A T)) :=
    constantModelBoundedConstructible Λ T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L (T : Scheme.{u}) := localizingClosureOfSize.{u + 1} (G T)
  have htri (T : Scheme.{u}) : (L T).IsTriangulated := by
    refine {
      exists_zero := ⟨HasZeroObject.zero.choose, HasZeroObject.zero.choose_spec, ?_⟩
      isStableUnderShiftBy := fun n ↦ ⟨?_⟩
      ext₂' := ?_ }
    · intro P hP hgen
      have := hP.1
      have := hP.2.1
      exact P.prop_of_isZero HasZeroObject.zero.choose_spec
    · intro K hK P hP hgen
      have := hP.1
      exact P.le_shift n K (hK P hP hgen)
    · intro T' hT h₁ h₃
      refine ⟨T'.obj₂, ?_, ⟨Iso.refl _⟩⟩
      intro P hP hgen
      have := hP.1
      have := hP.2.1
      exact P.ext_of_isTriangulatedClosed₂ T' hT (h₁ P hP hgen) (h₃ P hP hgen)
  have hmap (K : DerivedCategory (A V)) (hK : L V K) : L X (J.obj K) := by
    intro P hP hgen
    have := hP.1
    have := hP.2.1
    apply hK (P.inverseImage J) ⟨inferInstance, inferInstance, ?_⟩
    · intro K hK
      exact hgen _ ((qcOpenExtension_constantModelConstructible_finiteTor
        ℓ Λ hΛ e).2.2.2.2 K hK)
    · intro I E hE hobj
      have : PreservesColimitsOfShape (Discrete I) J := hJ I
      have : HasColimit E := hE
      have : HasColimit (E ⋙ J) := inferInstance
      exact P.prop_of_iso (preservesColimitIso J E).symm
        (hP.2.2 (E ⋙ J) inferInstance hobj)
  refine ⟨hexact e, hexact c, inferInstance, inferInstance, hJ, hB, hmap, ?_, ?_⟩
  · have := htri V
    exact ⟨inferInstance, inferInstance⟩
  · intro I K hK
    have : PreservesColimitsOfShape (Discrete I) J := hJ I
    have : PreservesColimitsOfShape (Discrete I) B := hB I
    have hR : PreservesColimit (Discrete.functor (J.obj ∘ K)) R :=
      qcqs_proper_localizing_preservesCoproduct ℓ Λ hΛ q f I
        (fun i ↦ J.obj (K i)) (fun i ↦ hmap (K i) (hK i))
    have : PreservesColimit (Discrete.functor K ⋙ J) R :=
      @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ R
        (Discrete.compNatIsoDiscrete K J).symm hR
    exact comp_preservesColimit J (R ⋙ B)

end AlgebraicGeometry.ProEtale.CondensedRing
