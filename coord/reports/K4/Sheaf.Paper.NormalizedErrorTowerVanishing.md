## What changed

`Sheaf.Paper.NormalizedErrorTowerVanishing` proves its original theorem from the
strict chain-level tensor-fiber construction, with an explicit derived-limit argument.
Private, proved helpers construct evaluation-at-zero ⊣ constants, prove that constants
preserve K-injectives, prove invertibility of the actual constant/limit diagonal on a
K-injective resolution, transport the ringed strict-tower limit theorem to the specified
right-derived functor, and compute powered transitions by induction on their gap.
The main proof uses naturality of the levelwise quasi-isomorphism to establish pro-zero
vanishing and applies exactness to the displayed triangle; it then composes the actual
augmentation, strict normalized reduction, and inverse diagonal.

The existing definitions move verbatim to `Sheaf.Paper.NormalizedErrorTowerData`,
publicly re-exported by the item, so that `Sheaf.Paper.NormalizedStrictTensorFiber` can
state the chain-level construction without an import cycle. No existing declaration is
removed, renamed, weakened, or given a different body. The construction lemma states
only the strict triangle, tensor-coordinate formulas, K-flat comparison, normalized
strict reduction, and eventual zero powered transitions. It has no inverse-limit
functor, comparison, diagonal or limit conclusion, and is strictly part of the original
seven-step argument. Its source is the unit's coefficient-fiber calculation, steps 1–5.

Searches actually run through msearch: LeanFinder for normalized coefficient towers,
Loogle for right-derived comparisons, grep for semilinear tensors, and LeanSearch for
pro-zero derived limits and constant-tower diagonals. The relevant general limit and
K-injective theorems already exist and are used. No existing theorem supplies the
strict changing-coefficient tensor construction with these coordinate formulas.
The imported blueprint was searched for normalized coefficients, strict tensor fibers,
and coefficient fibers; no duplicate blueprint statement was found.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.sp_normalized_error_tower_vanishing` (the item's
one original hole). Its proof is complete relative to the stated construction lemma.

Added: `AlgebraicGeometry.ProEtale.sp_normalized_strict_tensor_fiber`, node
`lem-sp-normalized-strict-tensor-fiber`, in its own module. Its body is exactly
`:= by sorry`; its docstring includes the source and complete mathematical argument.
The delivery is a decomposition, closing one upper hole and adding one strictly
smaller chain-level hole, net zero. The data module has zero holes. The private
powered-transition, evaluation/constant adjunction, K-injective constant preservation,
constant diagonal, and transported derived-limit lemmas have no holes.

The constant diagonal and generic powered-transition proofs were checked separately
with lcompile. The complete main theorem also compiled without warnings (58.2 seconds);
the transported limit helper compiled independently (6.2 seconds). Full packet
compilation and delivery preflight are performed by deliver3.
The original statement compiled as a baseline. Edge cases checked mathematically:
zero Q, n=m, equal transition indices, m=0 (positive exponent one), the gap m+1,
and unbounded Q. No boundedness or termwise-flatness is introduced.

## No longer needed

No original mathematical dependency is pruned: the strict construction still needs
the coefficient-fiber and signed tensor-cone results. In particular no upstream
source-library declaration is removed. The explicit derived argument uses the existing
triangle zero-object criterion directly. The original five proof-only imports are no
longer present in the relocated data module; the main proof imports its actual needs.
All original public imports remain transitively re-exported through the data module.
The original node's definitions now belong to `def-sp-normalized-error-tower-data`;
this is ownership relocation, not withdrawal. No module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing derived-limit theorem applies after fixing
an essentially-small instance and the coefficient-universe sheafification instances
explicitly. These instances must match the completed-coefficient interfaces even
when the site and coefficient universes differ. The constant-tower diagonal must be
checked for the specified comparison κ; an arbitrary abstract isomorphism would not
establish the required normalization. The proof checks precisely that comparison.

## New nodes

`lem-sp-normalized-strict-tensor-fiber` isolates the genuinely separate strict
coefficient-fiber tensor construction before taking any inverse limit. It retains the
unit's coefficient-fiber route and uses the existing coefficient, signed tensor and
levelwise-abelian declarations. It leaves one named public theorem to prove.

`def-sp-normalized-error-tower-data` owns the verbatim relocated existing definitions,
including the explicit diagram predicate. It introduces no new mathematical object
or axiom. Change record: `coord/changes/normalized-error-tower-data.md`.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
