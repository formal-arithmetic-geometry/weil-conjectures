## What changed

Proved `AlgebraicGeometry.finite_affine_proetale_refinement` with its signature unchanged.
The local refinements come from Mathlib's quasi-compact cover API after base change.
Weak etaleness follows from Mathlib instances. The global covering clause uses finite
spectral maps, with quasi-compactness supplied by affine sources and the quasi-separated
base. Updated the proof description and the node's proof, proof_deps and proof_origin.
No definition or public import changed; no consumer adaptation is required.
Change record: `coord/changes/K4-finite-affine-proetale-warning-option.md`.
It documents the removed file-level warning option. A fresh `tools/downstream.py` scan
on the current tree reports zero downstream modules and no external textual use of
`finite_affine_proetale_refinement`; no consumer adaptation is required. The earlier
record named `Sheaf.Paper.InternalHomDualConstructibleModels`, which no longer imports
this module in the current tree. The assigned DAG lemma remains the item being proved.

Repair of returned head be70f32eb: removed the unnecessary file-level
`set_option warn.sorry false`. The landing ledger's token matcher treated the option
name's `sorry` component at line 18, character offset 529 as an unattributed hole.
The retained proof itself had no hole. Removing the option repairs the reported
landing failure and restores the default warning behavior. The delivery tool rebases
the retained packet onto current sheaf-dag; no launcher or project tool was modified.

Repair of returned head `30fc924054` (reviewer `C-30fc9`): the mathematical review
passed, but landing failed while reading the unrelated missing module
`Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap`. Retained the accepted proof
and compared its signature and public imports with current sheaf-dag sources: both
are unchanged. Refreshed the node's non-proof metadata from the current tree while
preserving the reviewed proof route. Recompiled the retained module on the project
server through `lcompile.py`: exit 0, 2.9 seconds, no warnings. `deliver3.py` fetches
current sheaf-dag and constructs the rebased delivery commit before preflight.
No unrelated file is added or restored by this repair.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.finite_affine_proetale_refinement`
(node `lem-sfb-finite-affine-proetale-refinement`). The item's original 1 sorry is now 0.
Holes added: 0. Split off: 0. No sorry remains in the delivery.
The module compiled successfully through lcompile.py, including after removing both
proof imports. The delivery gate checks the declaration's axioms independently.
The repair adds no theorem or proof hole; the count remains 1 original hole closed,
0 holes added, and 0 holes remaining.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`: its bundled theorem is unnecessary;
  Mathlib supplies the needed open-immersion and composition instances directly.
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`: no affine pro-etale
  presentation or ind-etale ring theory is used.

Removed proof dependencies:

- `sk-lem-pe-weakly-etale-stability`: use Mathlib instances directly.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`:
  no explicit affine intersections are formed.
- `lem-weil-pbc-qcqs-finite-affine-open-cover`: no auxiliary finite affine cover is formed.
- `lem-weil-pbc-fibre-product-affine-spectra`: no tensor-product description is needed.

Added the existing Mathlib leaf `lem-weil-pbc-qcqs-morphism-permanence` for the
quasi-compactness and base-change instances. The unit's statement and steps are retained;
the changed route is internal to this auxiliary node. These removals describe this item's
proof needs, not a claim that the modules are globally unreachable from all other parents.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than necessary: quasi-separatedness makes every
map from a selected affine source quasi-compact, so the entire base change to any affine
W is a compact open witness. The finite spectral-family API packages this argument.
The CompactSpace S and IsLocallyNoetherian S assumptions are not needed by this proof;
the signature retains them unchanged. Empty schemes, t = 0 and empty local refinements
are covered by the same finite-union argument without nonemptiness assumptions.
The returned landing's unattributed marker was the warning option name, rather than
a Lean proof hole; its removal addresses the precise reported location. The resumed
dry run required a change record for that file-level command removal; the record above
now documents the change and all downstream consumers.

The latest return (`30fc924054`) identifies a landing failure on an unrelated missing
file, rather than a proof defect. This retry follows the requested rebase, fresh server
compile and delivery procedure; it preserves the proof that the reviewer passed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
