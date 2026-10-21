## What changed

Reapplied the retained locality proof to the current source of
`WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization`, addressing the
2026-10-21 return of delivery `50eb9f13e03` (old base `04c139b6f`). The current
source has one hole in the locality theorem. This packet starts from that file,
keeps its complete etale-surjection descent proof unchanged, and fills the
locality theorem without changing any signature, attribute, public import,
docstring or non-theorem body.

Two private proof imports provide unbounded compact-support composition and
the canonical etale graph comparison. The composition module publicly imports
the compactification-from-immersion construction. The proof follows the existing
node's three steps: compactify the etale map by its immersion into the proper pullback of a compactification of
the composite; identify compact support with exact etale extension; compose
adjunctions and apply uniqueness of right adjoints. It explicitly supplies the
open-immersion and proper-pullback instances. The empty-scheme and zero-ring
cases require no extra hypotheses. No node or unit route changes.

Validation: single-file compilation through `lcompile.py`, followed by the
compilation and axiom probes of `deliver3.py`.

## Proved and sorry left

Closed 1 of 1 current holes:
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
(node `lem-etale-exceptional-locality-arbitrary-schemes`). Added 0 holes;
split off 0 statements. No sorry remains in the item module.
The etale-surjection isomorphism-descent theorem is unchanged. Dependencies may
still have transitive proof obligations; this packet does not claim to close them.

## No longer needed

The retained packet's redundant private import of
`WeilConjectures.Compactification.Constructions` is omitted: the composition
module already publicly imports it. No existing source import, declaration,
node or module is removed, and no transitive-closure pruning is claimed.
The proof needs no additional private
imports of `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`, or
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: the adjunctions are
available through retained imports.
All existing proof dependencies remain used:
`lemma-nagata-immersion-into-proper`,
`lem-asd-compact-support-graph-derived-isomorphism`,
`lem-weil-pbc-etale-restriction-injectives`,
`lem-etale-unbounded-compact-support-composition`, and
`thm-amb-etale-exceptional-adjoint`.

## Where the brief, the DAG or earlier work was wrong

The returned delivery predates the upstream sync and changed overlapping lines.
The repair reconstitutes the item from the current source and reapplies only
its locality proof and private proof imports. The retained report incorrectly
said the current source had zero holes and referred to a different return;
this report records the actual one-hole baseline and the current return.
The existing DAG describes the implemented argument, so no node update,
statement change, definition repair or consumer adaptation is needed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
