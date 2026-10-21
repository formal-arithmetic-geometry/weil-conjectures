# Strict filtered-colimit internal-Hom reduction

## Reason

`filteredColimit_comparison` combined finite-free homological calculations,
continuity, exact colimits, and two strict cocone identities in one hole. The
finite-free and continuity calculations are separate arguments of the source
plan. They now have separate statement modules, and the parent contains the
complete categorical argument combining them.

## Old

The strict representative definitions and `comparison_existsUnique` were in
`Sheaf.Paper.DerivedInternalHomFilteredColimit`, as was the unfinished
`filteredColimit_comparison` theorem.

## New

The initial declarations from `Modules` through `Continuous` move, with their
signatures and bodies unchanged, to
`Sheaf.Paper.DerivedInternalHomFilteredColimitData`. The original module publicly
imports this data module. This extraction prevents an import cycle: the two new
proof dependencies need the representative definitions, and the original module
needs the proof dependencies. It is not a change to a representative, a choice,
a normalization, or a target statement.

`InternalHomFiniteFreeStage` states the basis calculation for a single finite-free
module, with no filtered diagram, continuity or boundedness hypothesis.
`InternalHomFilteredContinuity` states the colimit denominator, continuity after
the resolution augmentation, and ordinary tensor-colimit preservation. Their two
proofs remain named holes, with sources, complete proof plans and DAG nodes.
The original hole is replaced by exact filtered-colimit preservation of
quasi-isomorphisms, strict naturality proved using `colimit.hom_ext`, and
`quasiIso_of_comp_left`. The two-out-of-three step derives the comparison at the
colimit; it is not assumed in either new statement.

## Users

`tools/downstream.py Sheaf.Paper.DerivedInternalHomFilteredColimit` reports zero
Lean modules downstream. A direct import search agrees. The original module
publicly reexports every moved declaration, and its public imports are retained.
All existing public signatures, definition bodies and theorem statements are
unchanged. No source-library module is edited, and no forced adaptation is made.
The semantic target review can check the verbatim moved definitions; their
meaning has not changed.

| module | current holder | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R6 | Complete reduction proof |
| Sheaf.Paper.DerivedInternalHomFilteredColimitData | new, R6 | Unchanged shared declarations |
| Sheaf.Paper.InternalHomFiniteFreeStage | new, R6 | Single finite-free stage lemma |
| Sheaf.Paper.InternalHomFilteredContinuity | new, R6 | Continuity/augmentation lemma |

## Validation

The complete four-module packet compiles via `lcompile.py --all`; the parent
compiled in 37.1 seconds. The generic exact-colimit theorem used by the parent is
already proved in `WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim`.
No axioms or holes inside definitions were added. This is a decomposition:
one old hole is closed and two new holes are added; the other three old holes
remain, including the unchanged hole moved into the data module.

## Status

landed 20261021T005750-L-1889871 2026-10-21 (merge of deliver/R6/Sheaf.Paper.DerivedInternalHomFilteredColimit)
