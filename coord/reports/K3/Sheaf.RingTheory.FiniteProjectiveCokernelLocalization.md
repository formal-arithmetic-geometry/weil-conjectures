## What changed

Retired Sheaf.RingTheory.FiniteProjectiveCokernelLocalization, listed in
coord/retire-items.tsv. Its stronger finite-source result is preserved, with the
same complete proof, as
Module.finiteProjectiveCokernel_residue_localization_of_finite in the new module
Sheaf.RingTheory.FiniteSourceProjectiveCokernelLocalization. This distinct name
allows it to coexist with the official upstream projective-source specialization.

Updated the one remaining direct consumer,
Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero: only its proof import and one
application name change. Updated the existing node's Lean attachment; its statement,
proof steps, dependencies and unit route stay unchanged. No source-library file,
definition or target statement changes.

Change record: coord/changes/K3-finite-source-cokernel-retirement.md.

## Proved and sorry left

This is a retirement/interface repair with zero original holes: proved 0 of 0
sorries, added 0 holes, split off 0 unproved statements. There are no sorries left
in the withdrawn item or the new extension. The complete existing proof is
preserved as Module.finiteProjectiveCokernel_residue_localization_of_finite
(node lem-pc-finite-projective-cokernel-localization), with proved private helpers
Module.split_atPrime and Module.spread_split. The adapted consumer adds no sorry.

The extension and adapted consumer compile individually through lcompile.py.
The import-coexistence check imports both the official upstream specialization
and the new extension and prints their axioms. Both theorem axiom lists contain
only propext, Classical.choice and Quot.sound.
The unchanged transitive consumer PerfectCutComplexDegreeZero also compiles
against the adapted consumer (15.2 s). The extension and direct consumer compiled
in 5.9 s and 6.0 s respectively.

## No longer needed

The old module Sheaf.RingTheory.FiniteProjectiveCokernelLocalization and its import
in AffinePerfectCutDegreeZero are withdrawn. No module refers to that old path.
Its stronger mathematics remains necessary, so it is preserved with a distinct
name in FiniteSourceProjectiveCokernelLocalization; no net theorem or proof
reduction is claimed. No DAG node or mathematical dependency is pruned. No new
unproved dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief described a sorry-bearing item; the actual item is a
zero-hole retirement from coord/retire-items.tsv. The official theorem has an extra
source-projectivity assumption, which the E7 extension removed on 2026-10-18.
Consequently this strengthened node cannot simply point at the upstream theorem:
that would lose the finite-source statement needed for the image of a differential.
Its attachment instead follows the preserved, distinctly named extension.
An isolated compile with just the upstream import replacement fails at line 262:
`failed to synthesize instance of type class Module.Projective R ↥d.range`.
The delivered extension and two-line consumer adaptation compile cleanly.

The retirement table's additional consumer
Sheaf.Algebra.Homology.ResidueBottomDifferential has already been retired; its
upstream replacement uses the upstream theorem and needs no edit. The current
whole-tree search and downstream.py find only AffinePerfectCutDegreeZero directly
and PerfectCutComplexDegreeZero transitively.

Short-route searches via msearch.py (LeanFinder, Loogle and grep) confirm Mathlib's
local split-injectivity criterion and finite-presentation spreading lemmas used by
the existing proof. No complete finite-source localization theorem was found.
Read literature/stacks-project/algebra.tex, lemma-cokernel-flat (Tag 00O0), and
Mathlib.RingTheory.LocalRing.Module:334 onward. The finite-source extension follows
from that Mathlib criterion and denominator clearing, as the existing proof shows.
The zero-source, zero-target and zero-ring cases need no new assumptions; the
unchanged theorem has no nonzero-rank requirement. No new node is introduced.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
