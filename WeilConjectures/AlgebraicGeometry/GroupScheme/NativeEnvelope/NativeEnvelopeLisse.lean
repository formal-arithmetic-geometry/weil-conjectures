/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope

/-! # Lissity of the native normalized envelope

The lisse clause of `lem-wf-envelope-real`.
(blueprint: lem-wf-envelope-real-native-lisse)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeEnvelope

/-- The native normalized envelope of a lisse module is lisse.
Source: the lissity step of `lem-wf-envelope-real`; finite-free local models are
refined for the tensor unit, internal dual, and the two-term finite sum.
(blueprint: lem-wf-envelope-real-native-lisse).

Proof: choose a finite-free pro-etale cover trivializing the input module.
Pull it through the right unitor for the constant line and the canonical
tensor-unit comparison. Refine the cover with the finite-free dual chart,
then take a common refinement and the finite biproduct chart for the two
summands. The coefficient-heart closure theorem gives closure under the
finite product, and the induced isomorphism transports each chart to the
real envelope. The same argument works for rank zero and for every connected
component, so no nonempty or constant-rank hypothesis is used. -/
theorem normalizedEnvelope_lisse
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (b : (PadicAlgCl l)ˣ) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (realEnvelope D l X₀ hl F b).carrier := by
  sorry

end WeilConjectures.NativeEnvelope
