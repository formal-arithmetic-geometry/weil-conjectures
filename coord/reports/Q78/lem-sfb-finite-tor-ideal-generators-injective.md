# Stage-1 delivery: lem-sfb-finite-tor-ideal-generators-injective

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-finite-tor-ideal-generators-injective.json — item, statement, split into four steps; no Mathlib match.
   - dag/nodes/sec-six-functors-basics/lem-sfb-square-zero-relation-tor-obstruction.json — new statement-only node, unsplit; Stacks 09PU, no Mathlib match.
   - citations.json — verbatim statement excerpts for all five step/node citations.
   - report.md — this report. searches.jsonl holds the actual search-command results; write_split.py is sandbox-local preparation only.
2. Attachments: none. Searched the live read clone's WeilConjectures/ for the exact blueprint tag, ideal-generator injectivity, finite Tor terminology, 09PV, 09PU, square-zero Tor obstructions, and Gulliksen. No declaration states this item or the new obstruction. A project sorry is not used as a finished proof.
3. WANTED: none. Both sources are present in literature/stacks-project/dpa.tex, and the tag/label mapping was checked in tags/tags.
4. What was wrong: the item had no proof. Its mathematical statement is correct and remains byte-for-byte unchanged. The proof now includes the reductions omitted in the short source proof: an explicit hyperplane quotient, the equality of the annihilator with the residue maximal ideal, the zero-variable presentation, and the coefficient g = 1. No statement dispute or replacement route was needed.
5. Unfinished: the newly exposed general obstruction is deliberately statement-only, for the next stage-1 item. Its future proof is the Tate-resolution/divided-power derivation argument of 09PU, using 09PN, 09PS and 09PT. That future proof is not embedded in its statement or its proof fields. There is no unfinished part of the present assembly proof.

## Sources and blueprint searches

Read dpa.tex, Tag 09PV (lemma-injective), statement and proof at lines 1572–1591, and its cited Tag 09PU (lemma-not-finite-pd), statement and proof at lines 1537–1566; also read the preceding derivation computation to understand the obstruction. The new statement spells out the action on the square-zero kernel and writes the coefficient as the image of an actual polynomial g′, avoiding an implicit choice of lift.

Read the chapter sec-six-functors-basics, the unit sk-thm-sf-ctf-stability, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This is a local algebra supporting input in the already assigned branch through nested regular ideals and the lci fibre comparison; no chapter or unit is changed. The ancestry command returns None, matching the item's inherited null root; the new node retains that ancestry and prepends the item to via. Its place names precisely the application of 09PU in the proof of 09PV.

Ran tools/blueprint_refs.py search for finite Tor, 09PV, divided power, square-zero, minimal generator, Gulliksen and 09PU; searched the whole DAG for these tags and the lifted-relation obstruction, and searched the current blueprint text. No blueprint node gives the item or the obstruction. The square-zero blueprint hit is a compactification setup, with no homological obstruction. Existing self-Tor/conormal exterior nodes concern regular immersions, not this theorem. same_as is therefore empty.

## Mathlib assessment

All new-node searches and fresh item searches were made through the prescribed msearch.py command and their exact records were copied from searches.jsonl. The inherited item's searches were retained. The obstruction was searched in two semantic phrasings, with LeanSearch, LeanFinder, Loogle and two source grep patterns. All services answered. The returned infinitesimal lifting and cotangent statements contain no higher-Tor obstruction. Read Mathlib/RingTheory/Derivation/ToSquareZero.lean:48: it constructs a derivation from an algebra lift, rather than a nonvanishing Tor class.

For the item, inspected Mathlib/RingTheory/Ideal/Cotangent.lean:100 and CotangentBaseChange.lean:87: the former embeds I/I² into A/I², and the latter proves injectivity after flat base change. Neither concerns two generator spaces under a finite Tor bound. Flat tensor criteria and the ramification filtration hits also have different maps and hypotheses. No node is declared a Mathlib leaf merely on the strength of a search hit.

## Not duplicates

lem-sfb-square-zero-relation-tor-obstruction vs lem-sfb-finite-tor-ideal-generators-injective: the new node concerns an arbitrary square-zero cyclic extension and polynomial relation, and concludes failure of a uniform Tor bound for its algebra; the item concerns nested ideals of a single local ring and injectivity of their generator spaces. The item's steps construct the extension, identify its annihilator, and construct the relation. The obstruction is the independent source lemma 09PU, not a rewording of the generator-space assertion.

No existing node has the source tag 09PU or the statement of lemma-not-finite-pd. Existing nested-regular-ideal nodes use regular sequences and neither state nor replace this obstruction.

## Review by Q78

I checked delivery-errors B–E with both node statements and dpa.tex open. The new node introduces every ring, map, ideal, polynomial and lift; gives an explicit definition of the annihilator, square-zero condition and nonnilpotence; and expands finite Tor dimension using the existing Tor definition. It has empty proof/proof_deps and no proof hidden in its statement. Its source is the verified tag and label. JSON uses single TeX backslashes. The original statement and all maintainer-owned fields are retained. The new node is a real independent lemma, with no dependency on the item and thus no return edge.

Step 1 cites def-weil-pbc-noetherian-ring, whose statement says every ideal is finitely generated. Hence the images of finite generators of K span K/mK over k. Finite-dimensional coordinate selection then supplies a functional taking the nonzero kernel vector to 1. Its inverse-image kernel is an ideal because the action of A on K/mK factors through k. This is the routine linear algebra and ideal construction actually written in the step, not an uncited homological assertion.

Step 2 again cites exactly the Noetherian definition. The direct ideal-preimage argument establishes Noetherianity of both quotients. I checked K² ⊆ mK using K ⊆ m, so the cyclic kernel is square-zero. All elements of m kill its generator, and an element outside m is a unit, so it cannot kill that nonzero generator. Consequently the annihilator is exactly m/K, rather than merely containing it. This verifies the hypotheses the new lemma needs.

Step 3 cites the same definition for the finite generators of J. Membership f ∈ mJ gives coefficients b_j ∈ m after expansion in those generators. The stated lifts satisfy the relation in R and give exactly ε upstairs. The obstruction's polynomial-variable count is n = 0, its relation count is t, its f is ε, its g′ is 1, and its S is A/J. The quotient S/IS is A/m since K ⊆ J ⊆ m. It is nonzero by the local-ring hypothesis, so 1 is not nilpotent. Every hypothesis of the obstruction has now been verified explicitly.

Step 4 cites the new obstruction's exact no-finite-Tor conclusion and def-weil-pbc-tor-modules, whose statement defines the same Tor groups by a projective resolution. The coefficient ring is R = A/K throughout; no scalar-extension claim or finite-projective-dimension equivalence is assumed. Thus the conclusion contradicts exactly the uniform bound in the item. I copied the actual conclusion into citations.json and checked all other quoted excerpts against their cited statements; there are no tag-only non-elementary citations.

Small cases checked: K = 0 gives the zero-source injection; K = J gives the identity; J = 0 forces K = 0. If A is a field both ideals are zero. For A = k[[t]], K = (t²), J = (t), the generator map fails to be injective, as expected: k has nonzero Tor in all degrees over k[t]/(t²), so the finite-Tor hypothesis fails. For the new node take R′ = k[t]/(t³), R = k[t]/(t²), f = t², I = (t), h = r = t, and S = k; the lifted product is f and g = 1, and the periodic t-multiplication resolution confirms the obstruction. If f = 0, then I = R and S/IS = 0, so the nonnilpotence hypothesis is impossible. The same applies if S = 0. Empty relation sets cannot produce a nonnilpotent scalar; zero polynomial variables are expressly permitted and are the case needed here.

No proof step exceeds 2000 characters (lengths 532, 460, 542 and 331; total assembly 1865). I kept the finite coordinate and quotient calculations as elementary steps and exposed the homological obstruction as a separate node. No SGA source, Lean editing, compilation, local DAG check, repository write, launcher modification or direct git command was used.
