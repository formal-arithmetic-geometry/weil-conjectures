## What changed

Retained and repaired the earlier attempt's private abstract evaluation proofs in
Sheaf.Paper.CoefficientEvaluationNaturality. The main theorem now combines the
explicit evaluation transpose, two-variable naturality, contravariant theta
naturality and its evaluation equation with the canonical twist-interchange map.
The remaining stage-specific line argument is isolated in
Sheaf.Paper.ShiftedCoefficientLinesInvertible. All public signatures and
non-theorem constructions of the item remain unchanged.

## Proved and sorry left

Closed the original hole of WeilConjectures.sfCoefficientEvaluationNaturality
(node lem-sf-coefficient-evaluation-naturality) by a genuine decomposition.
Added one hole, WeilConjectures.sfShiftedCoefficientLinesInvertible
(node lem-sf-shifted-coefficient-lines-invertible). No other sorry remains in the
delivered files. Thus one upper hole is closed and one strictly simpler line
property is split off; this is a decomposition, not a net hole reduction.
The abstract formula, naturality in both variables, theta naturality, theta's
inverse evaluation equation, and equality with the canonical twist comparison
are proved in private helpers without sorry.

## No longer needed

Removed the private import Mathlib.CategoryTheory.Monoidal.Closed.Basic:
only general adjunction laws and braided identities are used, already available
through the existing public imports. Its node lem-pod-closed-uncurry-laws is
retained as the general adjunction/evaluation ingredient. No planned geometric
node or module is withdrawn. The coefficient-twists-detailed node is now needed
through the new shifted-line lemma rather than directly in the abstract proof.
No unit route is bypassed; twist-interchange is used explicitly. The existing
RingedSiteDualityMaps naturality theorems are generic categorical tools; this
proof does not invoke the module's existence or geometric normalization theorem.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had no report and its helpers had not compiled: tensor
notation needed explicit normalization, inverse cancellation needed the actual
asIso maps, and Iso.symm_injective is not a declaration of this Mathlib.
The previous server temporary-directory failure no longer prevents compilation.
The declared twist definitions do not by themselves provide invertibility of
these literal shifted objects in the supplied finite-Tor closed presentations.
The existing perfect-dual-pair stability theorem supplies normalized line pairs,
but further representative identification and transport are required, isolated
in the new lemma instead of silently treating invertibility as definitional.

## New nodes

lem-sf-shifted-coefficient-lines-invertible states only domain membership and
tensor invertibility of the four specified shifted signed Tate lines. It has no
internal Hom comparison or naturality conclusion and does not repackage the
original theorem. Its proof in words follows the final paragraph of the current
blueprint twist-interchange proof and the normalized line-pair theorem already
stated in the same unit. Edge cases checked: zero and negative twist, arbitrary
negative shift, odd shift, characteristic two, and empty scheme. No interface
change record is needed: existing signatures and definitions are unchanged.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
