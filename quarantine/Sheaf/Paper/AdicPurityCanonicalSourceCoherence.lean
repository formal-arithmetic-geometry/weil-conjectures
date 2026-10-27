/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.Paper.AdicPurityScalarNaturalityData

/-! # Integral purity assembly

Source: purity transport Steps 2--3.
(blueprint: lem-pur-adic-purity-scalar-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.AdicPurityScalarNaturality

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

attribute [local irreducible] source target scalar associator scalarUnit
  targetShift composeShift

/-- The canonical pullback/twist/shift scalar comparison obeys the ordinary tensor
unit, associator and shift equations, independently of any purity orientation.
Source: purity transport Step 3; operation-domains/source-comparison Steps 8--10
(blueprint: lem-pur-adic-canonical-source-coherence).

Proof: identify ordinary scalar extension on complete finite-Tor inputs with the
strict-tower functor by scalarCompletionIso. Apply source_identity, source_composition
and source_shift from AdicOperationSource to its sourceComponent. Expand the latter
once: scalar shift, twist beta, then pullback balancing. Naturality of chi identifies
this composite with sourceScalarComponent, including the inverse chi on the input.
The unit and associator of ordinary tensor are integralOrdinaryDerivedScalarUnit
and integralOrdinaryDerivedScalarComp. Their pure-tensor multiplication formulas
cancel the intermediate chi factors. For shifts use the recorded pullback, exact
twist and scalar shifts; their lifted full-subcategory structures are exactly
sourceShift and scalarShift. Apply aCanonical and full-inclusion faithfulness to
transport these three equations. This works for the zero object, empty schemes,
d=0 and identity coefficient inclusions; no finite-reduction detection is used. -/
theorem canonicalSourceCoherence (hC : ScalarClosed D C X Y)
    (a : ∀ (E F : Field D C) (h : E ≤ F),
      source D C f d E ⋙ scalar D C hC E F h true ≅
        scalar D C hC E F h false ⋙ source D C f d F)
    (ha : ∀ (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y),
      ((a E F h).hom.app K).hom = (sourceScalarComponent D C f d hC E F h K).hom) :
    (∀ (E : Field D C) (K : Cat D C E Y),
    (a E E le_rfl).hom.app K ≫
        (source D C f d E).map ((scalarUnit D C hC E false).hom.app K) =
      (scalarUnit D C hC E true).hom.app ((source D C f d E).obj K)) ∧
    (∀ (E F L : Field D C) (h : E ≤ F) (k : F ≤ L) (K : Cat D C E Y),
    (associator D C hC E F L h k true).hom.app ((source D C f d E).obj K) ≫
        (a E L (h.trans k)).hom.app K =
      (scalar D C hC F L k true).map ((a E F h).hom.app K) ≫
        (a F L k).hom.app ((scalar D C hC E F h false).obj K) ≫
        (source D C f d L).map ((associator D C hC E F L h k false).hom.app K)) ∧
    (∀ (E F : Field D C) (h : E ≤ F),
    ShiftCompatibility
      (source D C f d E ⋙ scalar D C hC E F h true)
      (scalar D C hC E F h false ⋙ source D C f d F)
      (composeShift (source D C f d E) (scalar D C hC E F h true)
        (sourceShift D C f d E) (scalarShift D C hC E F h true))
      (composeShift (scalar D C hC E F h false) (source D C f d F)
        (scalarShift D C hC E F h false) (sourceShift D C f d F)) (a E F h)) := by
  sorry

end WeilConjectures.AdicPurityScalarNaturality
