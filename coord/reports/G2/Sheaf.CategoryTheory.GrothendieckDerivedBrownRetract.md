## What changed

The original theorem now follows from localization/Brown data and a fully proved private
categorical helper `localization_retract`. The helper inverts the representing Hom map on
the adjunction unit, producing its retraction. It then applies lifted Yoneda, precomposes
with the right adjoint, and transports both endpoints using the counit and the fully
faithful Hom equivalence. Every naturality and splitting equation is proved in Lean.

Added `Sheaf.CategoryTheory.GrothendieckDerivedBrownRetractData` as a proof-only import.
Its sole theorem is the source's first-paragraph localization and Brown construction,
before splitting the unit. The original signature and all public imports are unchanged.

## Proved and sorry left

Closed the original hole `CategoryTheory.grothendieckDerived_brown_retract`
(node `lem-grothendieck-derived-brown-retract`). The private helper is fully proved.

Added one hole: `CategoryTheory.grothendieckDerived_localization_brown_data`
(node `lem-g2-grothendieck-derived-localization-brown-data`). This is a decomposition,
not a sorry-free proof of Brown representability: one hole closed, one added, net zero.
There are no sorries left in the original module and no other holes added.

Both files compile without warnings through lcompile.py. The remaining hole deliberately
asserts only representation after pullback along a localization. The proof from that data
to the retract is complete and does not merely unpack a repackaged Retract hypothesis.

## No longer needed

No original imports removed; no existing nodes or modules become unnecessary. The
planned distinguished unit triangle, vanishing of its first term, and contravariant
Hom exact sequence are unnecessary: invertibility after localization and naturality
of the representation already give the splitting. No modules for those steps were
imported. The unit record has no realized steps that this shortcut bypasses.

## Where the brief, the DAG or earlier work was wrong

The original node's sole proof step had no dependencies despite containing the whole
localization construction. The new node isolates its genuinely unformalized first
paragraph; the rest is now a Lean proof. No assertion is disputed or changed.

The localization model's Hom universe is max(w,vH), allowing module complexes in the
value universe rather than incorrectly assuming that small w-modules support Brown's
large sums. Its object universe is correspondingly enlarged. The new docstring records
this choice; no target signature or visibility is changed.

Edge-case checks: the zero category and the zero homological functor satisfy the new
assertion (with zero representing object); for module categories use the identity
localization. The categorical helper has no nonzero-object assumption and works for
these cases unchanged. It requires an invertible counit, not compact generation of D(A).

## New nodes

`lem-g2-grothendieck-derived-localization-brown-data` states the localization model and
representation of the pulled-back functor only. Its source is Tag 0F5X's first paragraph
and the derived Gabriel-Popescu lemma Tag 0F5V. Its proof plan names the existing Brown
representability and universe-transfer nodes. Searches found underived Gabriel-Popescu
and generic localization interfaces, not this combined derived construction. LeanSearch
was unavailable (HTTP Internal Server Error); LeanFinder and Mathlib grep ran successfully.
No change records or forced adaptations are needed.

## Second reading by G2

1. Interface: diff against the repository confirms the existing theorem signature is
byte-for-byte unchanged. No definition changed, and all existing public imports remain.
Both additions to the original module are proof-only imports. Verdict: pass.

2. Kernel proof: both modules compile cleanly through lcompile.py. A scratch copy with
`#print axioms` shows only propext, Classical.choice and Quot.sound for the private
localization_retract helper. The main theorem and data theorem additionally use sorryAx,
from the sole reported data hole. There are no definitions, hidden holes, or prohibited
commands in either delivered file. The existential data is eliminated only within a
proof of an existential proposition; no definition selects an arbitrary witness from it.
Verdict: pass as a decomposition, with one closed hole and one added hole, net zero.

3. Split statement: read the localization/Brown data assertion against
[Tag 0F5X](https://stacks.math.columbia.edu/tag/0F5X), first paragraph, and
[Tag 0F5V](https://stacks.math.columbia.edu/tag/0F5V). It omits the split unit and retract;
these require the substantial independently proved categorical helper. Checked the
zero functor, zero category, and module-category identity-localization cases. The common
Hom/value universe and enlarged object universe allow the module presentation and Brown
construction; no nonzero assumption is used. Independent searches through msearch.py
(LeanFinder, Loogle and Mathlib grep) with reflective-localization and exact derived
embedding terminology found generic adjunction and derived-functor interfaces, not this
combined theorem. Project and upstream searches likewise found only its downstream
consumers and the separate Brown/underived Gabriel-Popescu ingredients. The full derived
localization construction remains substantial and was not closed in this reading.
Verdict: pass; a proper sourced reduction, not a renamed target.

4. Route and pruning: checked the map directions, both triangle-identity cancellations,
the inverse Hom-map applied to the identity, Yoneda retract, whiskering, counit transport,
and fully faithful Hom equivalence including naturality. All retained imports support
signatures or these proof steps. The old proof_deps is empty, so there are no omitted
old dependency nodes to list. The unit sk-prop-sf-cbc has empty realized statement and
steps lists; no realized unit step is bypassed. Verdict: pass.

5. DAG: the existing node's three steps match the reduction, direct unit splitting and
natural transports. Its only proof dependency is the added data node. The new node has
its source, complete verbal proof plan, searches, creation/provenance fields, matching
verbatim Lean signature, chapter/unit and split status. Verdict: pass.

Second-reading change: replaced the stale original theorem docstring's triangle argument
with the actual direct splitting proof. Statements, definitions, imports and node records
were left unchanged. Added this review and recorded the independent searches.
