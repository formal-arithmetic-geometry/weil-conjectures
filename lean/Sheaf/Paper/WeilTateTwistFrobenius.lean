/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.WfTateTwist
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.Paper.WeilInternalHom
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.FiniteCoefficientPoint

/-! # Frobenius on the stalk of a finite-coefficient Tate twist

Source: blueprint main-20261015, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
`lem-wf-tate-twist-frobenius.md` and its proof
(blueprint: lem-wf-tate-twist-frobenius).

The signed line is the existing rationalization of the completed integral root line,
with its root-normalized Weil map. The stalk operator is the existing closed-point
operator, including residue-degree iteration and the semilinear point return.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- At every closed point, geometric Frobenius on the signed Tate line E(m) acts
by the negative m-th power of the actual residue-field cardinality.

Source: blueprint main-20261015, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
`lem-wf-tate-twist-frobenius.md`, entire statement and proof
(blueprint: lem-wf-tate-twist-frobenius).

Proof, following the eight steps of the DAG node:
1. Use lem-sc-primitive-root to choose compatible primitive ell-power roots in k.
Lift each root through the ell-th power map; the lift has the required exact order.
2. On the pro-etale site, each root section is uniquely locally a power of the
chosen primitive root: factor its defining polynomial into distinct linear factors.
These coordinates respect the power transitions. Their inverse limit trivializes
Z_ell(1) before taking a stalk, as in def-wf-tate-twist.
3. Extend this basis to the completed O_E-module lattice. Its positive tensor powers
and internal duals are free rank-one modules in degree zero. The K-flat and
K-injective models in def-wf-tensor-product and def-wf-internal-hom compute their
actual derived tensor and Hom, and completion fixes the coefficient unit.
4. The strict root pullback of lem-wf-tate-twist-compatibility and
 def-pur-roots-of-unity-inverse-image raises roots to the inverse q-th power:
 geometric Frobenius is z -> z^(1/q). Thus the first line's scalar is q^(-1).
 The compatible inverse residues define this same unit before rationalization.
5. The coefficient unit has scalar one. Tensor comparisons preserve pure tensors,
so induction gives q^(-m) for nonnegative m, including the separately defined unit.
6. Internal Hom uses the inverse positive Weil map contravariantly. Evaluation
therefore forces scalar q^h on the dual of the h-th positive power, for h > 0.
7. At a closed point of degree d, use lem-kun-closed-point-field and the local
operator of def-weil-local-frobenius-trace. The normalized equivalence of
lem-fd-rational-coefficient-category-comparison identifies the completed-pullback
Weil pairs with the framework pairs on the same integral lattices. Point transport
preserves the coefficient-unit basis; its naturality identifies the transports
under a line trivialization. The semilinear return is Phi^d xbar = xbar gamma^d,
not a fixed scheme map. The iterated Weil map consequently has scalar q^(-md).
8. The residue field has q^d elements, so this is Q_x^(-m). Changing the auxiliary
root basis conjugates a scalar endomorphism and leaves it unchanged. The empty
scheme has no closed points, so that case is vacuous. -/
theorem wfTateTwist_closedFrobenius
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (X₀ : Over (Spec (.of D.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℤ) (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    localClosedFrobeniusCohomology c.l (pbcFiniteField.{u} c.l c.Qbar E) D c.different X₀
        (wfTateTwistLocalModel D c X₀ E m)
        x ι hι 0 =
      (Nat.card (X₀.left.residueField x.val) : pbcFiniteField.{u} c.l c.Qbar E) ^ (-m) • 𝟙 _ := by
  sorry

end WeilConjectures
