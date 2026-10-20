## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge in favor of
WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge, as required
by its row in coord/retire-items.tsv. Updated its sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison, to import the twin.

The consumer proves that the two exterior restriction maps agree using their
pure-wedge formulas and uniqueness. Their identity section maps give a presheaf
morphism. Composing its linear stalk map with the upstream alternating wedge map
recovers the required wedge-germ formula. All existing consumer signatures,
public definitions, docstrings, and public imports stay identical. The private
exteriorGermMap data is now irreducible and unexposed; its wedge lemma unfolds it
once, and the rest of the proof uses the linear-map API. The new private stalk
map has the same protection and an explicit germ lemma. The transported alternating
map also has a private irreducible construction with its own germ formula.
Restriction compatibility now uses explicit equalities on wedge generators,
avoiding expensive quotient rewriting. Updated the wedge node's Lean attachment and the comparison node's first proof step. Change record:
coord/changes/J5-retire-exterior-presheaf-stalk-wedge.md.

## Proved and sorry left

The assigned module has zero original holes. Closed 0 holes; added 0 holes;
0 holes remain in the adapted consumer. This is a retirement, not a new proof
counted against an original hole. The upstream
AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_stalk_wedge is already proved.
The new private exteriorSheafRestriction_eq helper, the general commutative-ring
stalk-map construction and its germ formula, and the transported wedge map are
proved, and AlgebraicGeometry.Scheme.Modules.exteriorSheaf_stalk_comparison
retains its complete proof. No statement is split off.

Validation: the delivered comparison and its unchanged immediate downstream
consumer ExteriorTensorStalkKernelSpan compiled together against the sandbox
overlay, in 46.8 and 11.8 seconds respectively, without errors or warnings.
After replacing the expensive generator rewrite by explicit equalities, the
final comparison compiled in 22.8 seconds, again without errors or warnings.
A fresh overlay compile followed by a separate axiom audit compiled the final
comparison in 33.4 seconds and reported exactly propext, Classical.choice, and
Quot.sound for exteriorSheaf_stalk_comparison. The dry run passed; its combined
probe exceeded the file limit, so this separate audit checks the final compiled
theorem rather than relying on the deferred merge probe.
Verified the public theorem signature and all public imports against the
original, checked all changed Lean lines are at most 100 characters, and found
no new Sheaf/upstream twin pairs in the consumer import closure. The retired
module is absent from that closure.

## No longer needed

Deleted lean/Sheaf/AlgebraicGeometry/Modules/ExteriorPresheafStalkWedge.lean and
removed the consumer's import of that module. Its private commonGerms,
commonEquality, and exteriorWedge_res proofs no longer need a second copy.
The node lem-sc-exterior-presheaf-stalk-wedge stays and points to the upstream
implementation. All original mathematical dependency nodes remain needed.
No other module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a hole, but this item is a zero-hole
retirement in coord/retire-items.tsv. The old and upstream theorem statements
use different exterior-presheaf definitions, as the retirement inventory warns.
They cannot be substituted by an import edit alone. The identity-on-sections
morphism supplies the necessary conversion without changing the retained
exteriorSheaf definitions or the unit's route. The ring-presheaf stalk-map API
is linear over the RingCat stalk, so the consumer constructs its stalk map
over the CommRingCat stalk with the germ scalar law. This private construction
has a separate germ formula and does not expose its body, keeping the concrete
exterior-presheaf data from being unfolded during the comparison proof.

Only the unclaimed direct consumer is adapted; no held module is changed.
The Riemann--Roch unit has empty realized statement/step lists here. Its
mathematical route and every target statement remain unchanged.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
