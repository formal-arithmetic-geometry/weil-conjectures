/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData

/-! # The canonical geometric identification in the Weil fundamental representation

Source: blueprint def-wf-fundamental-representation, its arithmetic fibre path and
geometric fundamental group identification (blueprint: def-wf-fundamental-representation).

The upstream fundamentalRep takes a geometric-group identification as data. Here it is
specialized to the existing upstream data BasePointData.weilMonodromyData of the base
point: geomEquiv is BasePointData.geomEquiv, whose image in the arithmetic fundamental
group is B.geomAut (the homotopy exact sequence along B.path), and frobLift is
BasePointData.frobLift, whose image is B.frobAut (the lift of the Frobenius path).
Thus inertia is evaluated through the actual geometric inclusion, with no arbitrary
group relabelling and no new choice.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.WeilGroup
open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
  [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))}

/-- The recorded fundamentalRep with its geometric identification and degree-one lift
fixed by the base point: the existing upstream BasePointData.weilMonodromyData, built from
the homotopy exact sequence (geomEquiv) and the Frobenius path (frobLift).
The stalk transport M is the lisse monodromy of cor-galois-lisse-representations.
Source: def-wf-fundamental-representation (blueprint: def-wf-fundamental-representation). -/
def canonicalFundamentalRep {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
    (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
    (B : BasePointData W) (F : WeilSheaf K l C) (hF : F.IsLisse) :
    Representation (PadicAlgCl l) W.carrier (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :=
  fundamentalRep M B.weilMonodromyData F hF

end AlgebraicGeometry.WeilGroup
