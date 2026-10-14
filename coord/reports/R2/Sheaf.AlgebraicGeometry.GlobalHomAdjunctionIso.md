## What changed

The assigned module already had zero direct sorries and compiled in 23.4 seconds.
Its queue entry is a class-2 choice-data repair. Read the earlier Q3 tensor repair
and Y3 original-counit normalization record before making this partial repair.

Added the proved generic theorem `AlgebraicGeometry.internalHomMate_counit_transport`
in `Sheaf.AlgebraicGeometry.InternalHomMateCounitTransport` and its scheme
specialization `AlgebraicGeometry.schemeHomDirectImageComparison_counit_transport`
in the item. Also proved
`AlgebraicGeometry.schemeHomPullbackAdjunction_counit_transport`: the transported
adjunction satisfies the representative Hom equation for the new counit. A plain
proof import connects the generic calculation and its scheme specialization. The fixed comparison now has a
proved mate equation under simultaneous adjunction and tensor transport, including
the comparison iso from the composition counit to the original counit.

The proof expands Mathlib's actual transported Hom equivalence, inverse equivalence
and counit. Test-object tensor-Hom naturality and tensor-composition laws cancel
all four comparison factors. The scheme theorem combines that calculation with
the existing characterization of the SAME chosen direct-image comparison. The
adjunction theorem uses the original chosen representative equation and the
factorization equation of the new counit; it needs no additional derived-functor
existence assumption. It does
not choose replacement data. Identity automorphisms and arbitrary scalar twists
are covered without hypotheses; zero objects and empty schemes require no exceptions.

This is an enabling partial repair. Replacing the legacy adjunction, tensor and
base-change normalization together remains outstanding, as in Y3's record. In
particular, changing the adjunction alone cannot justify the existing base-change
mate equation in MixedTensorPairingBaseChangeTransport. No other module is adapted.

Change record: `coord/changes/global-hom-mate-counit-transport.md`.

## Proved and sorry left

Proved `AlgebraicGeometry.internalHomMate_counit_transport` and
`AlgebraicGeometry.schemeHomDirectImageComparison_counit_transport`, and
`AlgebraicGeometry.schemeHomPullbackAdjunction_counit_transport`, with complete
Lean proofs. Closed 0 pre-existing holes out of 0; added 0 holes; split off 0 holes.
There is no sorry left in either delivered module. This is a partial repair,
not net sorry-ledger progress and not a completed normalization repair.

## No longer needed

None. All existing imports and the existing global-Hom proof route are retained.
The new generic module imports only Mathlib's monoidal functor and adjunction APIs;
it needs no geometric, resolution or derived-category dependency. The exploratory
Mathlib monoidal-functor import was replaced by the smaller monoidal-category
import after a successful compile. No library import or DAG node is pruned.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief describes the module as still containing sorry, but the actual
source has none. `coord/repairs.txt` instead names two undetermined-data wrappers.
Y3's landed change is explicitly partial: the original-counit tensor API alone does
not normalize the legacy adjunction or prove base-change compatibility. The new
proof supplies the previously missing simultaneous-transport calculation for the
internal-Hom mate, while leaving that remaining coordinated work explicit.

The new formal lemma is a calculation for the evaluation construction in Stacks
Tags 08I3 and 08I4, rather than a quotation of a standalone theorem in those tags.
The source files are absent from this clone, so the official Stacks pages were read:
[08I3](https://stacks.math.columbia.edu/tag/08I3),
[08I4](https://stacks.math.columbia.edu/tag/08I4), and
[06YJ](https://stacks.math.columbia.edu/tag/06YJ).
LeanFinder/Loogle/source grep supplied the transport API. LeanSearch returned an
Internal Server Error and is recorded as unavailable, not as a negative search.
The blueprint search found no internal-Hom counit-transport node; the ancestor
script identifies `lem-sc-finite-duality`. The unit's realized route is unchanged.

## New nodes

`lem-pc-internal-hom-mate-counit-transport` records the generic, proved cancellation
of simultaneous adjunction and tensorator transport. Its module is
`lean/Sheaf/AlgebraicGeometry/InternalHomMateCounitTransport.lean`. The existing
global-Hom node gains both scheme specializations and the formal transport proof
dependency, without
changing its statement. Change record: `coord/changes/global-hom-mate-counit-transport.md`.

Validation: both delivered modules compile in import order with no warnings.
The final dry run checks every delivered declaration with the project axiom probe.


## Second reading by R2

1. PASS: Compared the complete existing module with the repository using `diff -u`.
   The only edits are one plain proof import and two new public theorems. Every
   existing signature, visibility, proof and definition body is byte-for-byte
   unchanged. The new generic module and its change record introduce only a proved
   theorem; no target meaning or chosen object is changed.
2. PASS: Read both modules, including the existing mate, tensor and Leray route.
   Neither delivered source contains `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by` or `extern`. Compiled in import order through `lcompile.py`;
   scratch copies additionally print axioms for all three added theorems and the
   existing global-Hom invertibility theorem. The delivery probe checks all
   declarations. Existing open dependencies are not claimed as newly proved.
3. PASS: No statement is split off and no hole is added. Checked the cancellation
   argument directly against Mathlib's `ofNatIsoLeft` implementation: the forward
   Hom map inserts delta, its inverse and counit insert delta inverse, and tensor
   composition cancels all factors in the displayed order. For delta = identity
   this is the original equation; for an invertible scalar twist the factors
   cancel without imposing a scalar normalization. Zero objects and empty schemes
   add no cases because the argument uses only category laws. The representative
   theorem retains its explicit counit-factorization hypothesis and applies the
   original representative specification to that exact composite.
4. PASS: Independently searched with Loogle query `CategoryTheory.Adjunction,
   CategoryTheory.Iso` and source searches for evaluation mates and tensor
   transport. The Mathlib transport formulas are already used by the proof; no
   existing theorem in the library found by these searches replaces the complete
   simultaneous-transport calculation. Both public imports of the new generic
   module supply types occurring in its signature; the item imports that module
   only for its proof. No old dependency is removed, so `No longer needed: None`
   is complete. The unit `sk-thm-picard-duality` and its existing `realized` record
   are unchanged; no unit step is bypassed.
5. PASS: Compared the existing node JSON with the repository. Only stage-3-owned
   fields change: proof, proof_deps, proof_origin and lean. The additional proof
   step describes both scheme specializations, and the generic node records the
   actual transport formulas and cancellations with no proof dependency or hole.
   Its Lean signature agrees verbatim, and it has source, agent proof origin,
   searches, creation, chapter, unit and blueprint provenance. The original
   global-Hom statement is unchanged.

Second reading changed only this report: added the independent checks and their
verdicts. No Lean proof repair was needed. Confirmed the delivery is an enabling
partial repair: 0 of 0 existing holes closed, 0 holes added, 0 split off, no
pruning; the coordinated legacy normalization repair remains outstanding.


Second-reader validation: both sources compiled without warnings (generic 1.1 s,
item 43.9 s). Scratch `#print axioms` confirms all three added theorems use only
`propext`, `Classical.choice` and `Quot.sound`. The unchanged
`AlgebraicGeometry.schemeGlobalHomAdjunctionMap_isIso` additionally uses `sorryAx`
through existing dependencies; this delivery does not claim that closure proved.
