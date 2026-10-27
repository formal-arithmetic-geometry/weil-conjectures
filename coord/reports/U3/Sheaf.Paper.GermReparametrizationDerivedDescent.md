## What changed

Replaced the proof hole in `WeilConjectures.trfGermReparametrizationDerivedDescent`
with a proof from the existing bounded quotient-stalk realization theorem and two
proper intermediate steps in new modules:

- `Sheaf.Paper.StrictQuotientStalkReindexing` states the strict tower, germ,
  cocone-coordinate, truncation, and strict action part of parent steps 1--4 and 8.
- `Sheaf.Paper.QuotientStalkNaturalDescent` states natural descent for one given
  strict tower isomorphism between two arbitrary points, assuming the realization
  isomorphisms and their chain-map naturality. It is parent steps 5--7 only.

The main proof constructs the normalization witnesses and proves the realization
arrow is invertible from the existing bounded realization theorem. It then
obtains the descended natural isomorphisms from the second step. The proved private
helper `trfNormalizedMapHEq` uses essential surjectivity of good-complex localization
and cancellation against one realization isomorphism to identify normalized maps.
The main proof uses this helper to prove the derived opposite composition and unit
laws, using the strict laws, the functoriality of the published Roos map and derived
quotient, and the actual contravariant Spec endpoint identities.

The original public theorem signature and all original public imports are
unchanged. `import all Sheaf.Paper.IntegralOperationsWellDefined` makes the existing
proved private good-complex localization theorem available to the proof. This is a
proof import. No existing definition, instance, or statement is changed.

The two remaining steps have complete proof docstrings and DAG nodes, and the
parent node's proof and proof dependencies follow the new proof. No source-library
module or consumer needs adaptation; no change record is necessary.

Validation: `lcompile.py --all` compiled all three delivered Lean modules in
import order, with exit code zero and no Lean diagnostics. Static checks also
verified the unchanged original signature and public imports, the exact new
Lean/node statement matches, the proof-dependency unions, and the 100-character
Lean line limit.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.trfGermReparametrizationDerivedDescent`
(node `lem-trf-germ-reparametrization-derived-descent`). No sorry remains in the
assigned module, including its private helper.

Added two holes, each the entire proof of a public named theorem in its own module:

- `WeilConjectures.trfStrictQuotientStalkReindexing`
  (`lem-trf-strict-quotient-stalk-reindexing`).
- `WeilConjectures.trfQuotientStalkNaturalDescent`
  (`lem-trf-quotient-stalk-natural-descent`).

This delivery is a decomposition: one upper hole closed, two strictly smaller
holes added, not an axiom-free proof of the original result. The existing bounded
quotient-stalk realization theorem is used as stated and is not reproved here.
The strict step asserts no derived descent; the natural descent step accepts one
already specified tower isomorphism and asserts neither strict data nor any action
law. Thus neither is the parent theorem renamed or its full hypotheses repackaged.

## No longer needed

Removed these original direct proof imports from the assigned module:

- `Sheaf.Paper.PointProEtaleSectionsExactOfUniverses`.
- `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.

Exact point sections are already accounted for by the existing bounded realization
interface. Roof fractions and K-flat resolutions remain mathematical dependencies
of the new descent step; they are not globally pruned. The corresponding original
parent proof dependencies and tool-use approvals are removed where the parent no
longer uses them directly. The definition of the integral constructible category
also remains a statement dependency and a dependency of the new descent proof.
`lem-pur-integral-operations-well-defined` remains directly used through the proved
good-complex localization and the Roos functor laws. No module is withdrawn and no
unit statement or unit proof step is bypassed. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The parent already records
that one cannot simply restrict a localization to an arbitrary full subcategory.
The new descent step explicitly retains its reviewed roof argument: resolve the
roof apex, use isomorphism invariance of constructibility, invert the denominator
square, and compose with the numerator square. Essential surjectivity alone is
used only for the proved cancellation helper, where it suffices to choose a
representative of an individual object.

Checked the current blueprint at `literature/blueprint/latest/`, Step 1, Local
powers (b), and Stacks `sites.tex`, Tag 05V1. The new statements are subarguments
of the already reviewed parent expansion. Edge cases retain zero complexes,
empty schemes, positive exponent n+1, all p,q (including p=q and p>q), the identity
automorphism, and noncommuting automorphisms. The generic descent step needs no
relationship between its two given geometric points. No witness from an
unproved existence theorem is used in a new data definition.

A dependency sanity traversal also found an existing two-node cycle in the shared
DAG: `lem-pc-ring-hom-extension-differential` has proof dependency
`lem-pc-ring-hom-extension-differential-adjacent`, whose statement dependency points
back to the former node. This is already reachable from the original parent,
before this packet. Neither node is changed here. Neither new node has a
dependency path back to the assigned parent. The existing cycle needs maintainer
attention independently of this proof reduction.

## New nodes

`lem-trf-strict-quotient-stalk-reindexing`, in the parent's chapter and unit,
records the strict, germ-normalized reindexing argument. Its module is
`Sheaf.Paper.StrictQuotientStalkReindexing`. Its complete proof plan constructs
reindexing first on all integral module stalks, then whiskers with quotient and
truncation functors and checks both cocone coordinates and strict laws.

`lem-trf-quotient-stalk-natural-descent`, in the same chapter and unit, records
natural descent for a fixed strict tower isomorphism with prescribed realization
squares. Its module is `Sheaf.Paper.QuotientStalkNaturalDescent`. Its proof plan
is the parent's reviewed homotopy and roof argument; composition and unit laws
are instead proved in the assigned module. Both new nodes record the three
required kinds of Mathlib search. The generic integral-operation, saturated
quasi-isomorphism, and K-flat-resolution nodes are tools inherited from the
reviewed parent route: the trace-formula unit does not re-establish the general
localization or resolution results. Their uses are explained in the new nodes'
`split_report.tool_uses`; maintainer approval entries are not added here.
No change records are added.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
