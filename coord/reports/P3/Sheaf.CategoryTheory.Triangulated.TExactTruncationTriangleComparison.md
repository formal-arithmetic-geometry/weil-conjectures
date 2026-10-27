## What changed

Proved `CategoryTheory.Triangulated.TStructure.texact_truncation_triangle_comparison` without
changing its signature. `Triangle.functorIsoMk` assembles the existing `F.eTruncLTIso`, identity,
and `F.eTruncGEIso`; the two normalization equations and upstream `F.eTruncGEδLT_comm` provide
all three squares. `TStructure.triangle_map_ext` proves uniqueness over the middle identity.
Naturality of `truncGEδLT` supplies the final boundary equation. The proof uses neither boundedness
assumption but keeps both exactly as stated.

The module compiles through lcompile.py in 2.6 seconds after import pruning, without errors or
warnings. No helpers, axioms, definitions, or other modules were added or changed. Updated the
existing node's proof and proof_origin to match the shorter assembly. The four proof dependencies
remain the same mathematical notions and results. Change record:
`coord/changes/P3-texact-truncation-triangle-imports.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Triangulated.TStructure.texact_truncation_triangle_comparison`
(node `lem-pod-texact-truncation-triangle-comparison`). Zero holes remain; zero holes added;
zero split off. This is a complete proof, not a decomposition.

## No longer needed

Removed public imports:
- `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`;
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.

The first module's packaging theorem `texact_truncation_comparison` is unnecessary here: its
canonical objects and normalization API are already upstream. The second module's homology,
heart, and adjunction developments are unnecessary: Mathlib's `triangle_map_ext` suffices.
The sole retained import is
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`, which defines
the comparison isomorphisms and IsTExact appearing in the unchanged statement and proves their
boundary compatibility. The four declared DAG dependencies remain applicable through their
existing upstream/Mathlib realizations; no node or module is withdrawn. In particular the
unfinished parent can continue to use this item. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan was valid but longer than necessary: the upstream boundary lemma is already
proved, Mathlib assembles the natural triangle isomorphism, and boundary naturality is built
into `truncGEδLT`. Thus no fresh TR3 extension or explicit adjunction cancellation is needed.
The archived unit record's sk-lem-finite path no longer exists in the current blueprint;
its recorded realized statement and step lists are empty. The current operations proof was
read at `literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/prop-weil-operations.proof.md`.
There is no statement dispute, source-library edit, or consumer adaptation.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
