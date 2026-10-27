## What changed

Completed `AlgebraicGeometry.finiteCenterOpen_closure_kernel_data` without changing its
statement or `finiteCenterOpen`. Three proved private helpers establish quasi-coherence of
an ideal module, the kernel formula on every open for a quasi-compact map, and
quasi-compactness of the complement of a finite-type ideal on an arbitrary scheme.

On an affine open, finite module sections give a finitely generated image ideal. The affine
spectrum chart identifies the complement with the complement of its zero locus, which is
compact. Base change gives quasi-compactness of the required open. Existing image-factor
instances provide openness, density and section injectivity. The canonical affine quotient
isomorphism supplies the quotient clause. An explicit pullback inverse supplies the
scheme-theoretic open restriction. Kernel cancellation and the closed-immersion lift give
the comparison subscheme and both ambient ideal formulas.

Validation: the complete module compiles cleanly through `lcompile.py` in 16.5 seconds.
The added private imports pass the import-cycle checks.

Only the assigned module and its own DAG node change. Private proof imports now use the
existing quasi-coherent pushforward/kernel and scheme-theoretic image APIs. The DAG proof
and dependencies describe the implemented argument. No targets, definitions, public
signatures, or public imports change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteCenterOpen_closure_kernel_data`
(node `lem-trf-finite-center-open-closure-kernel-data`).

Proved 1 of 1 original sorries; 0 remain; 0 added; 0 split off.
All private helpers are proved. The proof handles the zero ideal, unit ideal, empty schemes,
and schemes with no global compactness or separation assumptions.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage` and the dependency
`lem-pc-closed-subscheme-base-change-ideal-image`, including its obsolete `tool_uses` entry.
The second pullback projection has an explicit inverse from the image factorization and
monicity, so neither the tensor-pullback ideal formula nor an ideal comparison with the
identity is needed there. No module is withdrawn; the generic base-change ideal theorem
may remain needed by other consumers.

The planned `lem-weil-pbc-open-immersion-base-change` dependency is unnecessary: the open
is already represented as an open subscheme, and the factor through its image is covered
by the existing Mathlib theorem `lemma-nagata-immersion-open-in-scheme-image`.
Its quasi-compactness and density clauses are used directly.

A temporarily added direct import of
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` was removed because the
scheme-theoretic dominance complement publicly imports that API.
No other planned module or node is claimed to be globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The proof plan was longer than necessary
for the pullback and image-factor clauses. The actual Lean representation permits a direct
categorical pullback inverse and existing Mathlib image instances. The arbitrary-open
kernel formula follows by cancelling the injective image-factor map on sections; it does
not require surjectivity on arbitrary-open sections. The affine quotient formula is used
only on affine opens, exactly as stated.

For ideal-module quasi-coherence the proof explicitly uses the already proved generic
quasi-coherent pushforward and kernel theorems
(`pqf-lem-pushforward-qcoh`, `lem-weil-pbc-quasi-coherent-module-kernel`). They are tools for
the ideal-module bridge; they replace no step of the trace-formula unit route.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
