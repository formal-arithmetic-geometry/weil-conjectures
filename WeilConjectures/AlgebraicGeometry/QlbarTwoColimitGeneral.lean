/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The constructible finite-Tor algebraic-closure coefficient 2-colimit

This is the statement of the current blueprint unit `sk-prop-qlbar-two-colimit`.
It is stated for a finite or algebraically closed base field of characteristic
different from `ℓ`, with condensed coefficients pulled back to the pro-étale
site.  The objects are the finite-constant-model bounded constructible
finite-Tor complexes used for `D^b_{ctf}`.

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors/sec-n-change/sk-prop-qlbar-two-colimit/_section.md`,
unit statement (order 383), and its
proof paragraph (blueprint: sk-prop-qlbar-two-colimit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 0

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section FiniteTorCocone

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] (hfield : Finite k ∨ IsAlgClosed k)
  (hchar : ringChar k ≠ ℓ)
  (X : Scheme.{u}) [hOver : X.Over (Spec (.of k))]
  [hft : LocallyOfFiniteType (X ↘ Spec (.of k))]
  [hqc : QuasiCompact (X ↘ Spec (.of k))]
  [hsep : IsSeparated (X ↘ Spec (.of k))]

include hfield hchar hOver hft hqc hsep in
/-- Scalar extension preserves the finite-constant-model bounded constructible
finite-Tor subcategories, both between finite fields and into the algebraic closure.

Source: `part-six-operations/sec-six-functors/sec-n-change/`
`sk-prop-qlbar-two-colimit/sk-prop-qlbar-two-colimit.proof.md`, scalar extension;
DAG proof step 2 (blueprint: sk-prop-qlbar-two-colimit).

Proof: The field scalar extensions are flat, so their derived functors are computed
termwise and commute with cohomology. On the pro-étale cover of each constructible
stratum, a finite constant model over a field is finite free. Tensoring preserves
that model, its rank, the finite stratification and the cohomological bounds.
Step 1's rational finite-Tor identification then supplies finite Tor amplitude
for the resulting bounded constructible field-coefficient complexes.
-/
theorem constantModelFiniteTor_scalarExtension_preserves :
    (∀ {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
      (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((derivedExtendScalarsSubfield X ℓ h).obj K.obj)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X),
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj)) := by
  sorry

/-- Scalar extension on the actual finite-Tor constant-model subcategories.
Source: the scalar-extension clause and DAG step 2 of the current unit
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorExtendScalars
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X ⥤
      ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj F) X :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    ((constantModelFiniteTor_scalarExtension_preserves ℓ k hfield hchar X).1 h)

/-- Extension to the algebraic closure on finite-Tor constant-model complexes.
Source: the object map in the current unit and DAG step 2
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorToPadicAlgCl (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X ⥤
      ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) X :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    ((constantModelFiniteTor_scalarExtension_preserves ℓ k hfield hchar X).2 E)

/-- Restriction of the canonical ambient scalar transitivity isomorphism, using
full faithfulness of the inclusion of the finite-Tor constant-model subcategory.
Source: the category-of-pairs construction, DAG step 5
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorToPadicAlgClCompIso
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    constantModelFiniteTorExtendScalars ℓ k hfield hchar X h ⋙
        constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X F ≅
      constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X E :=
  Functor.fullyFaithfulCancelRight
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι
    ((Iso.refl ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) :
      (constantModelFiniteTorExtendScalars ℓ k hfield hchar X h ⋙
          constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X F) ⋙
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
          DerivedCategory.finiteTorAmplitude _).ι ≅
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) ≪≫
      Functor.isoWhiskerLeft
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
          DerivedCategory.finiteTorAmplitude _).ι
        (derivedExtendScalarsCompIso X ℓ h))

/-- The scalar-extension cocone with finite-Tor constant-model categories at every
finite field and at its vertex, constructed directly from their ambient inclusions.
Source: the unit's category of pairs and DAG steps 5--6
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorCocone :
    CategoryCocone
      (fun E : PadicAlgCl.FiniteIntermediateField ℓ ↦
        ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X)
      (ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) X) where
  T h := constantModelFiniteTorExtendScalars ℓ k hfield hchar X h
  Φ E := constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X E
  iso h := constantModelFiniteTorToPadicAlgClCompIso ℓ k hfield hchar X h

end FiniteTorCocone

/-- The ordinary filtered 2-colimit of the finite-Tor constant-model categories.
Source: `part-six-operations/sec-six-functors/sec-n-change/`
`sk-prop-qlbar-two-colimit/_section.md`, order 383, and its proof
(blueprint: sk-prop-qlbar-two-colimit).

Proof follows DAG steps 1--6:
1. A separated finite-type scheme over a field is qcqs. For finite field coefficients
   and the algebraic closure, rational bounded constructibility equals finite-Tor
   bounded constructibility inside the same ordinary derived category.
2. Flat scalar extension preserves the finite constant models, the constructible
   stratification and the cohomological bounds; step 1 gives finite Tor amplitude.
   This is the named preservation theorem used to construct the cocone above.
3. Descend an object by the finite-coefficient descent theorem: descend its lisse
   sheaves and transition matrices and then the connecting maps of a finite
   Postnikov tower. Step 1 puts the finite-stage representative in Dctf.
4. Apply the morphism clause at degree zero. Fullness identifies the Hom sets with
   ambient derived Hom sets, and constructible Ext continuity gives surjectivity
   and eventual equality for their finite-stage representatives.
5. For different initial fields move to their finite compositum. The ambient
   scalar transitivity isomorphisms restrict by the fully faithful inclusions.
   Transport identities and composition through the Hom bijections; injectivity
   gives independence of representatives, associativity and the unit laws.
6. Object descent and the cross-stage Hom bijections give essential surjectivity
   and full faithfulness of the comparison from pairs. Equivalently they give
   Obj, Hom-surj and Hom-inj of the actual Dctf cocone, so it is a filtered
   2-colimit of ordinary categories.
-/
theorem qlbarTwoColimitGeneral
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hfield : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ K : ConstantModelConstructibleFiniteTor
        (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (K_E : ConstantModelConstructibleFiniteTor
          (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K L : ConstantModelConstructibleFiniteTor
        (Profinite.continuousMapRingObj E) X),
      (∀ ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj ⟶
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj L.obj,
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (f : (derivedExtendScalarsSubfield X ℓ h).obj K.obj ⟶
            (derivedExtendScalarsSubfield X ℓ h).obj L.obj),
          finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj K.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj L.obj)
        (g : (derivedExtendScalarsSubfield X ℓ a).obj K.obj ⟶
          (derivedExtendScalarsSubfield X ℓ a).obj L.obj),
        finiteDescentDerivedHomToAlgCl X ℓ h f =
            finiteDescentDerivedHomToAlgCl X ℓ a g →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
          finiteDescentDerivedHomTransition X ℓ h b f =
            finiteDescentDerivedHomTransition X ℓ a c g)) ∧
    (constantModelFiniteTorCocone ℓ k hfield hchar X).IsFilteredTwoColimit := by
  sorry

end AlgebraicGeometry.ProEtale
