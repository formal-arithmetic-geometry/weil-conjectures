Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-lying-over.json`: statement, Mathlib leaf (`RingHom.IsIntegral.comap_surjective`, exact match).
- `citations.json`: empty, because the item is a Mathlib leaf and has no proof steps.

Attachments:

None. No project declaration under `WeilConjectures/` carries the blueprint tag or states this item.

WANTED:

None.

What was wrong or changed:

The imported node was marked `imported` with an agent-written localization proof and no Mathlib searches. The statement itself is correct, but the localization proof is unnecessary at stage 1 because Mathlib already states the result exactly. I changed the copy to `status: mathlib`, removed the proof steps, recorded the exact declaration and source line, filled `blueprint.same_as` with the empty search result, and retained the original statement and source metadata.

What could not be finished:

Nothing. The required LeanSearch service was unavailable; this is recorded in `mathlib_searches` as `unavailable`. LeanFinder and source grep supplied the exact match, and Loogle was also run as required.

## Review by M1

I read the imported item statement and its blueprint proof, then checked the project source for a tagged or sorry-free project declaration; none exists. I read Mathlib's `RingHom.IsIntegral.comap_surjective` declaration in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` at line 1226. Its hypotheses are an integral ring homomorphism and injectivity, and its conclusion is surjectivity of `PrimeSpectrum.comap`, exactly equivalent to every prime of the source being the contraction of a prime of the target. The commutative-ring assumptions match the item's ring convention. I ran LeanFinder, Loogle, grep, and LeanSearch with the queries recorded in the node; LeanSearch reported service unavailability. Since the item is a Mathlib leaf, there are no proof steps or cited nodes to quote and no new nodes or small-case proof obligations.

## Second reading by M1

- Item statement: checked against Stacks Project Algebra, Lemma 10.36.17, Tag 00GQ; its injective integral extension and surjectivity on spectra are exactly the stated contraction property. Verdict: correct after correcting the source tag from 00GU (going-up) to 00GQ (lying-over).
- Proof steps: there are none because the item is a Mathlib leaf; `proof` and `proof_deps` are empty. Verdict: valid.
- New nodes: none; the only node is the item itself, and its statement-only Mathlib status satisfies the leaf form. Verdict: valid.
- Mathlib leaf: checked `RingHom.IsIntegral.comap_surjective` in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1226`; its `IsIntegral` and injectivity hypotheses and surjective prime-spectrum comap conclusion match the item exactly. Verdict: valid.
- Edge cases: the zero ring, fields, and the empty prime spectrum are covered by the theorem's commutative-ring assumptions; for a field extension the unique source prime has a target prime, and the zero-ring case is vacuous. Verdict: consistent.
- Searches and provenance: reviewed the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results; set `blueprint.from` to the item's proof paragraph and retained `same_as: []`. Verdict: complete.
- Changes: corrected external source Tag 00GU to Tag 00GQ and filled the required blueprint provenance; no proof or statement content was otherwise changed.
