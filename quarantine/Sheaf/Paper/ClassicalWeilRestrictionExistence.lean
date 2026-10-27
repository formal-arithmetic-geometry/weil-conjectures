/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.ClassicalLisseWeilFrontierData

/-! # Classical Weil restriction along finite-field frontiers

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-weil-restriction-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The actual restricted Weil map has a finite classical lift with the pinned point
comparison, independently of any choice of frontier.
Source: blueprint thm-zl-real-mixed-by-curves, paragraph 7;
BS 6.8.4(1),(4), 6.8.14(2), 6.8.15
(blueprint: lem-zl-classical-weil-restriction-exists).

Proof: the canonical finite-field base-change inclusion intertwines the geometric
Frobenius of V with the mth ambient power. Use this square and the two normalized
pullback compositors to restrict the actual iterate of K.str. The supplied
identification of the restricted lattice conjugates it to a map between realizations
of classical lisse objects. The quotient-normalized automorphism comparison supplies
its source. Full faithfulness lifts this map and its inverse; faithfulness gives the
two inverse equations. Represent these two maps and equations at one common finite
coefficient enlargement of P.field. Enlarge again to represent the restricted sf Weil
object and its identification. At a geometric point use the normalized finite
realization fibre comparison followed by R.identifiedFiber. On each finite quotient,
its point transport and pullback unit are the same ordinary inverse-image maps.
Passing to the inverse limit and rationalization preserves these equations. Iterating
the pullback compositor equation identifies the restricted local rth iterate with
the ambient mrth iterate, so the comparison intertwines the actual sf and classical
local operators. This produces all fields of WeilRestrictionResult, including the
specified equality of fibre identifications. The empty scheme and rank-zero lattice
use the same functors and equations without selecting a point.
-/
theorem classical_weil_restriction_exists
    (R : Realization D l Ω) (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (M : sfCommonStageHeart l (fiberBase D Y₀).scheme Ω)
    (P : PartitionData D l Ω R (fiberBase D Y₀) M)
    (K : sfCommonStageWeilComplex D l (Fact.out : l ≠ D.p) Y₀ Ω)
    (hK : K.carrier = M.obj) (m : ℕ) (hm : 1 ≤ m)
    (V : RestrictionModel D l Ω R Y₀ (fiberBase D Y₀) M P m hm)
    (hj : V.intoSupport = V.geometricMap D l Ω)
    (square : V.intoSupport ≫
      localPositivePower (D.geometricFrobenius Y₀).hom (m - 1) =
        (V.frobenius D l Ω).hom ≫ V.intoSupport) :
    Nonempty (WeilRestrictionResult D l Ω R S A C Y₀ M P K hK m hm V hj) := by sorry

end WeilConjectures.ZlFrontier
