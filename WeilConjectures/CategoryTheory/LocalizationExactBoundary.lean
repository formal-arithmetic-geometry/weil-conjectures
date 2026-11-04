/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The natural connecting boundary of an exact sequence of exact functors

Source: trace-additivity Step 2, Stacks Tag 0152
(blueprint: lem-trf-localization-exact-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (J I : C ⥤ C) [J.Additive] [I.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (a : J ⟶ 𝟭 C) (q : 𝟭 C ⟶ I)
  (hz : ∀ M, a.app M ≫ q.app M = 0)
  (hs : ∀ M, (ShortComplex.mk (a.app M) (q.app M) (hz M)).ShortExact)

/-- Apply the sequence of exact functors degreewise.
Source: Stacks Tag 0152 (blueprint: lem-trf-localization-exact-boundary). -/
def localizationExactSequence (K : CochainComplex C ℤ) :
    ShortComplex (CochainComplex C ℤ) where
  X₁ := (J.mapHomologicalComplex (.up ℤ)).obj K
  X₂ := K
  X₃ := (I.mapHomologicalComplex (.up ℤ)).obj K
  f := { f := fun n ↦ a.app (K.X n)
         comm' := fun m n _ ↦ (a.naturality (K.d m n)).symm }
  g := { f := fun n ↦ q.app (K.X n)
         comm' := fun m n _ ↦ (q.naturality (K.d m n)).symm }
  zero := by
    ext n
    exact hz (K.X n)

include hs in
omit [HasDerivedCategory C] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I] in
/-- The degreewise exact sequence is short exact as a sequence of complexes.
Source: Stacks Tag 0152. Proof: evaluate in each degree and apply the sheaf sequence.
(blueprint: lem-trf-localization-exact-boundary). -/
theorem localizationExactSequence_shortExact (K : CochainComplex C ℤ) :
    (localizationExactSequence J I a q hz K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact hs (K.X n)

/-- The connecting maps form a natural transformation on complexes.
Source: Stacks Tag 0152. Proof: use the morphism of degreewise short exact sequences
induced by a complex map and naturality of the short-exact-sequence boundary.
(blueprint: lem-trf-localization-exact-boundary). -/
def localizationExactConnecting :
    I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      (J.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
        shiftFunctor (DerivedCategory C) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ
    (localizationExactSequence_shortExact J I a q hz hs K)
  naturality K L f := by
    let t : localizationExactSequence J I a q hz K ⟶
        localizationExactSequence J I a q hz L :=
      { τ₁ := (J.mapHomologicalComplex (.up ℤ)).map f
        τ₂ := f
        τ₃ := (I.mapHomologicalComplex (.up ℤ)).map f
        comm₁₂ := by ext n; exact a.naturality (f.f n)
        comm₂₃ := by ext n; exact q.naturality (f.f n) }
    exact (DerivedCategory.triangleOfSESδ_naturality
      (localizationExactSequence_shortExact J I a q hz hs K)
      (localizationExactSequence_shortExact J I a q hz hs L) t).symm

/-- Descend the actual connecting transformation along quasi-isomorphisms.
Source: Stacks Tag 0152. The fully faithful localization universal property
constructs this map from the natural chain boundary, without choosing cone data.
(blueprint: lem-trf-localization-exact-boundary). -/
def localizationExactBoundary :
    I.mapDerivedCategory ⟶ J.mapDerivedCategory ⋙
      shiftFunctor (DerivedCategory C) (1 : ℤ) :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (DerivedCategory C)).preimage
      (I.mapDerivedCategoryFactors.hom ≫ localizationExactConnecting J I a q hz hs ≫
        Functor.whiskerRight J.mapDerivedCategoryFactors.inv (shiftFunctor _ (1 : ℤ)))

/-- The descended map is normalized by the actual chain short exact sequence: with
`φ : I (Q K) ≅ Q (I K)` and `φ' : J (Q K) ≅ Q (J K)` the realization isomorphisms
`mapDerivedCategoryFactors` and `δ` the connecting map of `0 → J K → K → I K → 0`,
the square
```
            boundary_{Q K}
  I (Q K) ────────────────→ (J (Q K))[1]
     │                           │
    φ_K                       φ'_K[1]
     ↓                           ↓
  Q (I K) ──────── δ ──────→ (Q (J K))[1]
```
commutes.
Source: Stacks Tag 0152. Proof: the localization preimage equation, followed by
cancellation of the exact-functor realization isomorphism.
(blueprint: lem-trf-localization-exact-boundary). -/
theorem localizationExactBoundary_Q (K : CochainComplex C ℤ) :
    (localizationExactBoundary J I a q hz hs).app (DerivedCategory.Q.obj K) ≫
        (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
          (J.mapDerivedCategoryFactors.hom.app K) =
      I.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.triangleOfSESδ
        (localizationExactSequence_shortExact J I a q hz hs K) := by
  let τ : DerivedCategory.Q ⋙ I.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ (J.mapDerivedCategory ⋙
        shiftFunctor (DerivedCategory C) (1 : ℤ)) :=
    I.mapDerivedCategoryFactors.hom ≫ localizationExactConnecting J I a q hz hs ≫
      Functor.whiskerRight J.mapDerivedCategoryFactors.inv (shiftFunctor _ (1 : ℤ))
  have h := congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (DerivedCategory C)).map_preimage τ) K
  change (localizationExactBoundary J I a q hz hs).app (DerivedCategory.Q.obj K) =
    I.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.triangleOfSESδ
      (localizationExactSequence_shortExact J I a q hz hs K) ≫
        (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
          (J.mapDerivedCategoryFactors.inv.app K) at h
  let d : DerivedCategory.Q.obj ((I.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj
        (DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj K)) :=
    DerivedCategory.triangleOfSESδ (localizationExactSequence_shortExact J I a q hz hs K)
  change (localizationExactBoundary J I a q hz hs).app (DerivedCategory.Q.obj K) ≫
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        (J.mapDerivedCategoryFactors.hom.app K) =
    I.mapDerivedCategoryFactors.hom.app K ≫ d
  change (localizationExactBoundary J I a q hz hs).app (DerivedCategory.Q.obj K) =
    I.mapDerivedCategoryFactors.hom.app K ≫ d ≫
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        (J.mapDerivedCategoryFactors.inv.app K) at h
  rw [h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  change I.mapDerivedCategoryFactors.hom.app K ≫ d ≫
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        (𝟙 (DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj K))) =
    I.mapDerivedCategoryFactors.hom.app K ≫ d
  rw [(shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id, Category.comp_id]

end CategoryTheory
