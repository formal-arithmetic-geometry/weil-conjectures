/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Descent to a finite coefficient field

Source: latest blueprint,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-descent-to-a-finite-coefficient-field/sk-thm-sfb-qlbar-two-colimit/_section.md`,
lemma `sk-thm-sfb-qlbar-two-colimit`, order 249 (blueprint: sk-thm-sfb-qlbar-two-colimit).

The displayed filtered-colimit isomorphism on shifted Hom sets is recorded in the
canonical representative form supplied by the finite-coefficient descent interface:
every algebraic-closure morphism has a finite representative, and two finite
representatives with the same algebraic-closure image become equal after a common
finite extension.  Scalar extension is the recorded derived scalar extension along
the condensed coefficient maps; no alternative coefficient model is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.CommShift.ofIso Functor.leftDerivedFunctor Functor.mapDerivedCategory
  finiteDescentDerivedHomToAlgCl finiteDescentDerivedHomTransition
  coefficientDescentHomToAlgCl coefficientDescentHomTransition

-- The existing descent results apply to all Noetherian schemes, so the stated field
-- restrictions are retained in the interface but are not needed by the proof.
set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- Canonical derived scalar and zero-shift comparisons require additional elaboration.
/-- Finite coefficient descent for bounded constructible condensed complexes.

Source: latest blueprint,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-descent-to-a-finite-coefficient-field/sk-thm-sfb-qlbar-two-colimit/_section.md`,
assertions (1) and (2), with the proof in `sk-thm-sfb-qlbar-two-colimit.proof.md`
(blueprint: sk-thm-sfb-qlbar-two-colimit).  The displayed Hom colimit is stated in its
representative form: surjectivity of finite representatives and eventual agreement after a
common finite extension, through the specified scalar-extension maps.

Proof (the node's three steps):
1. The finite extensions of `ℚ_ℓ` in `ℚ̄_ℓ` form a filtered directed set, and
   `QbarX = colim_E E_X` (sk-prop-sfb-qlbar-colimit-x).  Flatness of `E'_X` and `QbarX`
   over `E_X` (lem-sfb-subfield-flat, lem-sfb-qlbar-flat) identifies the ordinary tensor
   extensions with the derived scalar extensions.
2. Assertion (1): the natural adjunction isomorphisms of det-lem-coefficient-finite-descent-hom
   (1) rewrite both sides as Hom over `E` into the restrictions of `D_{E'}[r]`, resp.
   `D_{ℚ̄_ℓ}[r]`.  A bounded representative `D^•` gives the filtered diagram
   `D^• ⊗ E'_X`, uniformly bounded below with colimit `D^• ⊗ QbarX` (clause (2) there);
   sk-lem-constructible-ext-continuity (1) with source `C` and shift `r` identifies the
   colimit of Hom groups.  Naturality of the adjunctions in `E'` makes this the
   scalar-extension map.
3. Assertion (2): `X` is Noetherian and qcqs.  A constructible `QbarX`-module has the finite
   filtration of sk-lem-coefficient-heart (3) with subquotients `a_!L`; each lisse `L`
   descends (sk-lem-lisse-finite-descent, det-lem-coefficient-finite-descent-lisse (1)),
   and `a_!` commutes with scalar extension
   (lem-sfb-condensed-locally-closed-scalar-extension).  After enlarging to a common finite
   field, the connecting class `N_k/N_{k-1} → N_{k-1}[1]` descends by (1) and its fibre
   models `N_k`.  For bounded constructible `K`, induct on the largest degree `q` with
   `H^q(K) ≠ 0`, descending the connecting map `H^q(K)[-q-1] → τ_{<q}K` by (1) and taking
   its cone; cones and shifts stay bounded constructible
   (det-cor-coefficient-heart-ii-triangulated).
-/
theorem finiteCoefficientDescentTwoColimitStatement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hchar : ringChar k ≠ ℓ)
    (hbase : Finite k ∨ IsAlgClosed k)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (C D : ConstantModelBoundedConstructible
        (Profinite.continuousMapRingObj E) X) (r : ℤ),
      (∀ (ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj (D.obj⟦r⟧)),
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
            (derivedExtendScalarsSubfield X ℓ h).obj (D.obj⟦r⟧)),
          finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj (D.obj⟦r⟧))
        (g : (derivedExtendScalarsSubfield X ℓ a).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ a).obj (D.obj⟦r⟧)),
        finiteDescentDerivedHomToAlgCl X ℓ h f =
            finiteDescentDerivedHomToAlgCl X ℓ a g →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
          finiteDescentDerivedHomTransition X ℓ h b f =
            finiteDescentDerivedHomTransition X ℓ a c g)) ∧
    (∀ (K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ℓ) X),
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (K_E : ConstantModelBoundedConstructible
          (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  constructor
  · intro E C D r
    have hE : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
        boundedConstructible (padicSubfieldRingObj X ℓ E) :=
      constantModel_eq_of_localFree _ (finite_lf ℓ E) X
    let : (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated :=
      finiteBoundedTriangulated X ℓ E
    let C' : PadicSubfieldConstructible X ℓ E :=
      ⟨C.obj, (congrFun hE C.obj).mp C.property⟩
    let D' : PadicSubfieldConstructible X ℓ E :=
      ⟨D.obj⟦r⟧, (boundedConstructible _).le_shift r D.obj
        ((congrFun hE D.obj).mp D.property)⟩
    constructor
    · intro ψ
      obtain ⟨F, h, a, f, hf⟩ := constructibleCocone_homSurj X ℓ E E C' D'
        (ObjectProperty.homMk ψ)
      refine ⟨F, h, f.hom, ?_⟩
      have hh := congrArg (·.hom) hf
      dsimp only [constructibleCocone] at hh
      simp only [ObjectProperty.FullSubcategory.comp_hom, tensorComp_inv, tensorComp_hom,
        constructibleToPadicAlgCl_map_hom] at hh
      have hcomp (b : E ≤ F) : finiteCoefficientDerivedTensorCompIso X ℓ b =
          derivedExtendScalarsCompIso X ℓ b := rfl
      rw [hcomp h] at hh
      dsimp only [C', D', constructibleToPadicAlgCl, ObjectProperty.lift,
        ObjectProperty.ι, ObjectProperty.homMk, Functor.comp_obj] at hh
      simpa only [finiteDescentDerivedHomToAlgCl] using hh.symm
    · intro F G h a f g heq
      let H := IsFiltered.max F G
      have b : F ≤ H := leOfHom (IsFiltered.leftToMax F G)
      have c : G ≤ H := leOfHom (IsFiltered.rightToMax F G)
      refine ⟨H, b, c, ?_⟩
      have heq' : coefficientDescentHomToAlgCl X ℓ h C.obj (D.obj⟦r⟧) 0
          (f ≫ (shiftFunctorZero _ ℤ).inv.app _) =
        coefficientDescentHomToAlgCl X ℓ a C.obj (D.obj⟦r⟧) 0
          (g ≫ (shiftFunctorZero _ ℤ).inv.app _) := by
        apply (cancel_mono ((shiftFunctorZero _ ℤ).hom.app _)).mp
        simpa only [finiteDescentDerivedHomToAlgCl_zero] using heq
      have he : coefficientDescentHomTransition X ℓ h b C.obj (D.obj⟦r⟧) 0
          (f ≫ (shiftFunctorZero _ ℤ).inv.app _) =
        coefficientDescentHomTransition X ℓ a c C.obj (D.obj⟦r⟧) 0
          (g ≫ (shiftFunctorZero _ ℤ).inv.app _) := by
        apply descentHomToAlgCl_injective X ℓ (h.trans b) C.obj (D.obj⟦r⟧) 0
        rw [descentHomToAlgCl_transition, descentHomToAlgCl_transition]
        exact heq'
      have he' := congrArg (fun q ↦ q ≫ (shiftFunctorZero _ ℤ).hom.app _) he
      simpa only [finiteDescentDerivedHomTransition_zero] using he'
  · exact (coefficient_finite_descent_objects_of_isNoetherian ℓ X).1

end AlgebraicGeometry.ProEtale
