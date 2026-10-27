/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation

/-! # Common finite sequences of marked-ideal tests

Source: Bierstone--Milman, Functoriality in resolution of singularities,
Definitions 2.2--2.5; the open-restriction convention of the numerical recovery lemma
(blueprint: def-trf-common-marked-test-sequence).

This records paths in the existing geometric test relation, adding open restrictions.
It does not redefine a blowup, its controlled transform, or test equivalence.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- A finite sequence of common actual transforms. The empty sequence is allowed.
Each geometric step is admissible for both current cosupports and uses the existing
controlled or ordinary transform according to its kind. An open step pulls back both
marked data and the ordered boundary along the same open immersion over the base.
Source: BM, Definitions 2.2--2.5, and the local-test convention of the recovery lemma
(blueprint: def-trf-common-marked-test-sequence). -/
inductive CommonTestSequence {k : Type u} [Field k] :
    {S T : Embedded k} → Marked S → Marked S → Marked T → Marked T → Prop
  | nil {S : Embedded k} (M P : Marked S) : CommonTestSequence M P M P
  | geometric {S T U : Embedded k} {M P : Marked S} {M' P' : Marked T}
      {M'' P'' : Marked U}
      (prior : CommonTestSequence M P M' P') (s : Step T U)
      (admissibleM : s.Admissible M'.cosupport)
      (admissibleP : s.Admissible P'.cosupport)
      (transformM : s.Transforms M' M'') (transformP : s.Transforms P' P'') :
      CommonTestSequence M P M'' P''
  | restriction {S T U : Embedded k} {M P : Marked S} {M' P' : Marked T}
      {M'' P'' : Marked U}
      (prior : CommonTestSequence M P M' P') (f : U.Z ⟶ T.Z)
      (openImmersion : IsOpenImmersion f) (overBase : f ≫ T.p = U.p)
      (boundary : U.boundary = T.boundary.map (fun D ↦ D.comap f))
      (pullbackM : MarkedPullback f M' M'') (pullbackP : MarkedPullback f P' P'') :
      CommonTestSequence M P M'' P''

end AlgebraicGeometry.HilbertSamuel
