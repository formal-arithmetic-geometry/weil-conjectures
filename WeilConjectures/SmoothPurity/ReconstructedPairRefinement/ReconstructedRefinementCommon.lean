/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing

/-! # Compactification independence on the native condensed constructible category

Source: latest blueprint, sk-thm-purity-transport, Step 3, first sentence;
det-sf-comp-coherence-single and det-sf-comp-coherence-cocycle.
(blueprint: lem-route-reconstructed-refinement-common).

The candidates are the ordinary unbounded derived compact-support composites restricted
to bounded constructible objects of finite Tor amplitude, with their ambient morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.ReconstructedPairRefinement

/-- Ordinary compact support restricts to Dctf, independently of compactification.
The isomorphisms ε identify the restricted functors with the actual composites Rp_* j_!.
The normalization against every common dense refinement specifies the comparisons;
invertibility of its second leg gives independence by cancellation. The last clauses
are identity and cocycle in the full constructible target category.

Source: latest blueprint sk-thm-purity-transport, Step 3, first sentence; the restriction
of det-sf-comp-coherence-single and det-sf-comp-coherence-cocycle.
(blueprint: lem-route-reconstructed-refinement-common).

Proof: single-compactification preservation lifts each ordinary composite through the
full Dctf target. Every Dctf object lies in its localizing closure by the defining
intersection. Evaluate the localizing coherence isomorphisms at these objects and lift
their components through the full target inclusion. Ambient naturality and inverse
identities give natural isomorphisms. Their dense-refinement normalization is the same
ambient equality. Fullness and faithfulness carry the ambient identity and cocycle
back to Dctf. This works also for empty schemes and nondense endpoint compactifications.
-/
theorem reconstructedRefinementCommon
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ F : Compactification.BoundaryCompactification f →
        (ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ Y),
    ∃ ε : ∀ c, F c ⋙ (constantModelBoundedConstructible Λ Y ⊓
          DerivedCategory.finiteTorAmplitude _).ι ≅
        (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ c.obj.obj,
    ∃ φ : ∀ c d, F c ≅ F d,
      (∀ (c : Compactification.BoundaryCompactification f)
        (d : Compactification.DenseBoundaryCompactification f) (r : d.obj ⟶ c)
        (K : ConstantModelConstructibleFiniteTor Λ X),
        IsIso (compactificationRefinementComponent Λ r K.obj)) ∧
      (∀ (c d : Compactification.BoundaryCompactification f)
        (z : Compactification.DenseBoundaryCompactification f)
        (r : z.obj ⟶ c) (s : z.obj ⟶ d) (K : ConstantModelConstructibleFiniteTor Λ X),
        (ε c).inv.app K ≫ ((φ c d).hom.app K).hom ≫ (ε d).hom.app K ≫
            compactificationRefinementComponent Λ s K.obj =
          compactificationRefinementComponent Λ r K.obj) ∧
      (∀ c, φ c c = Iso.refl _) ∧
      (∀ c d e, φ c d ≪≫ φ d e = φ c e) := by
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let P (T : Scheme.{u}) : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
    constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _
  let I : ConstantModelConstructibleFiniteTor Λ X ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK Q _hQ hPQ ↦ hPQ K hK)
  let F (c : Compactification.BoundaryCompactification f) :
      ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ Y :=
    (P Y).lift ((P X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c.obj.obj)
      (fun K ↦ (compactification_localizing Λ ℓ k f c hΛ).2.2.2 K.obj K.property)
  let ε (c : Compactification.BoundaryCompactification f) :
      F c ⋙ (P Y).ι ≅ (P X).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c.obj.obj := Iso.refl _
  obtain ⟨ψ, hi, hn, hid, hcomp⟩ := compactification_coherence_cocycle Λ ℓ hΛ k f
  let φ (c d : Compactification.BoundaryCompactification f) : F c ≅ F d :=
    NatIso.ofComponents (fun K ↦ (P Y).isoMk ((ψ c d).app (I.obj K))) (by
      intro K L a
      apply ObjectProperty.hom_ext
      exact (ψ c d).hom.naturality (I.map a))
  refine ⟨F, ε, φ, ?_, ?_, ?_, ?_⟩
  · intro c d r K
    exact hi c d r (I.obj K)
  · intro c d z r s K
    change 𝟙 _ ≫ (ψ c d).hom.app (I.obj K) ≫ 𝟙 _ ≫
        compactificationRefinementComponent Λ s (I.obj K).obj =
      compactificationRefinementComponent Λ r (I.obj K).obj
    simpa only [Category.id_comp] using hn c d z r s (I.obj K)
  · intro c
    apply Iso.ext
    ext K
    exact congrArg (fun t ↦ t.hom.app (I.obj K)) (hid c)
  · intro c d e
    apply Iso.ext
    ext K
    exact congrArg (fun t ↦ t.hom.app (I.obj K)) (hcomp c d e)

end WeilConjectures.ReconstructedPairRefinement
