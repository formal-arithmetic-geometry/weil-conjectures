# Stage-1 report: def-exc-excellent-ring

## Files written

- `dag/nodes/sec-smooth-purity/def-exc-excellent-ring.json`: existing definition, now split. Mathematical content retained; added the direct localization definition citation and completed the split report. Fresh Mathlib searches found no match for the complete excellent/quasi-excellent predicates.
- `citations.json`: empty list, since this definition has no proof steps.
- `mathlib-search-results.json` and `searches.jsonl`: actual fresh search outputs and the search command's audit log.

No new nodes and no new Mathlib leaves. The required notions already have nodes or are defined inline; a definition needs its constituent notions, not artificial theorem steps proving a predicate.

## Attachments

None. Searched the project Lean source by `def-exc-excellent-ring` and the notions excellent, quasi-excellent, catenary, G-ring, and J-2. There is no declaration defining this item under `WeilConjectures/`; the only relevant occurrence is the illustrative quasi-excellent comment in `SixFunctors/Etale/Derived/Stability.lean:174`. The upstream master was also checked as reference material, not treated as evidence of a completed proof. No upstream-name entry for this notion was found.

## Wanted sources

WANTED: `literature/stacks-project/more-algebra.tex`, Tags 07QT (`definition-excellent`) and 07P7 (`definition-J`), for def-exc-excellent-ring; the local literature checkout is absent.

WANTED: `literature/stacks-project/algebra.tex`, Tags 00NI (`definition-catenary`) and 00NL (`definition-universally-catenary`), for def-exc-excellent-ring; the local literature checkout is absent.

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-exc-punctured-curve-branches.md`, for the ancestor's original proof; the local blueprint checkout is absent. Its imported DAG record and unit/chapter records are available and were read.

I read the primary online Stacks pages and upstream TeX source instead, without creating a literature checkout or downloading files:

- https://stacks.math.columbia.edu/tag/07QT and https://stacks.math.columbia.edu/tag/07P7
- https://stacks.math.columbia.edu/tag/00NI and https://stacks.math.columbia.edu/tag/00NL
- https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex (labels `definition-excellent`, `definition-J`)
- https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex (labels `definition-catenary`, `definition-universally-catenary`)

There is no proof to mark agent-written: these are predicate definitions, with `proof: []` and `proof_origin: null`.

## Issues found and corrections

The inherited item already contains the correct mathematical definition. Its direct dependency list omitted the localization-at-a-prime notion used explicitly in the J-2 clause. Added `def-weil-pbc-localization-at-prime` both inline and in `stmt_deps`. This changes no hypothesis or predicate. The existing Noetherian requirement applies throughout; the inline universally catenary clause is used for this already-Noetherian R, exactly the domain of Stacks 00NL. No statement dispute or source error was found.

The inline catenary condition includes a finite bound for every fixed interval of primes. That bound must not be dropped: it excludes an unbounded interval even if there happened to be no finite saturated chain. The bound depends on the pair of endpoints, not globally on the ring. Thus the definition does not impose finite global Krull dimension.

## Unfinished work

None for the one-level split. The G-ring node remains an existing dependency, as required by the task's one-level scope; it is not resplit or copied into this delivery. The sandbox is left for the fresh second reader; no delivery is pushed.

## Not duplicates

No new nodes are created, hence there are no new/existing same-tag pairs. Whole-DAG tag searches for 07QT, 07P7, 00NI, and 00NL and concept searches found this item and users of excellence, not a second definition. Whole-blueprint searches `excellent`, `catenary`, `J-2`, and `excellent universally catenary` were run. The two blueprint matches for `excellent`, `lem-exc-punctured-curve-branches` and `lem-exc-dvr-galois`, assume excellence in their statements; neither defines it. Therefore `blueprint.same_as` is empty. The ancestor command gives `lem-exc-punctured-curve-branches`, matching the preserved precise `from.place`.

## Review by Q44

I read Stacks 07QT with its two clauses, 07P7 with its J-1/J-2 clauses, and 00NI/00NL with the bounded-chain and finite-type definitions, together with the corresponding TeX labels. Quasi-excellence is the conjunction of Noetherianity, the G-ring predicate, and the openness requirement for every finite type algebra. Excellence adds universal catenarity. All quantified rings and primes occur in the item, and the regular locus uses the localization of the finite type algebra A at its own prime, not a base localization or a fibre ring. There is no assertion that openness follows from Noetherianity alone.

I opened each cited definition's statement. `def-weil-pbc-noetherian-ring` defines Noetherianity by finite generation of ideals. `def-weil-pbc-g-ring` actually defines the G-ring predicate via the regularity of every prime-localization-to-completion map, including Noetherianity; it is not merely a lemma assuming a G-ring. `def-weil-pbc-finite-type-algebra` gives finite generation as an algebra over R, the exact quantifier required here. `def-weil-pbc-localization-at-prime` constructs A_p by inverting A minus p and identifies its local maximal ideal. `def-weil-regular-scheme`, despite its scheme title, explicitly includes the definition of a regular local ring, which is what the J-2 clause uses. `def-weil-affine-spectrum` gives the prime spectrum with its Zariski topology, which supplies the meaning of open. The latter five are existing Mathlib leaves; the G-ring node is an existing split definition. Every direct dependency exists, is unmerged, and is used; none depends on the item.

There are no proof steps, so C1/C4 have no step citations to quote: `citations.json` is `[]`. The definition takes no theorem from a cited definition and asserts no well-definedness, closure under finite type extensions, Nagata property, or regularity of a completion map without hypotheses. Those would require theorem nodes; the ancestor already uses separate nodes for stability and the Nagata implication. J-2, universal catenarity, saturated chains, and chain length are expanded inline instead of creating clause-only nodes. No other-unit theorem replaces the unit's route; this is a notion needed by the existing route.

For B1-B10 I checked self-contained objects, explicit definitions or correct definition citations, ordinary TeX escaping, all four tags and labels, no unsupported leaf or attachment claim, exact fresh search queries and outputs, and precise blueprint provenance. For C1-C8 and D1-D5 I checked that this is a definition with no hidden theorem, proof citation, transferred clause, cycle, induction, or off-route proof. For E1-E7 I checked the Noetherian scope and finite-type quantifiers and tested the boundary conventions: the zero ring has empty spectrum and vacuous prime conditions; the zero finite type algebra has empty regular locus, which is open; an equal-endpoint prime interval has its single length-zero chain; a field's interval is length zero; an adjacent prime pair has chain length one; and interval bounds are not a uniform dimension bound over all primes. These checks introduce no theorems claiming that arbitrary fields or other examples are excellent. I found no new false claim or missing hypothesis.

I ran fresh logged searches using only `msearch.py`: two LeanFinder phrasings, Loogle `"Excellent"`, source grep `excellent|quasiExcellent|catenary|IsJTwo|J2Ring`, and LeanSearch. The semantic candidates concern Noetherian local criteria, smooth loci, quasi-finiteness, or DVR criteria, not excellence. Loogle has no hits. The sole grep hit is the English adjective in `Mathlib/Algebra/Lie/InvariantForm.lean:32`. LeanSearch reports Internal Server Error and is recorded as unavailable. The fresh results are appended to the inherited searches rather than claiming the inherited searches as mine.

## Validation

Required validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q44 def-exc-excellent-ring --no-push`. The sandbox is handed over only after this command prints OK; its stdout is the acceptance record. No Lean was written or compiled and no Lake/build tool was run. All authored files are confined to the designated sandbox.


## Second reading by Q44

- Item `def-exc-excellent-ring`: checked both clauses against Stacks 07QT, `more-algebra.tex`, `definition-excellent`; PASS: quasi-excellent is precisely Noetherian plus G-ring plus J-2, and excellent adds universal catenarity. Read the upstream raw TeX directly because the local literature checkout is absent.
- Inline J-2 clause: checked 07P7, `more-algebra.tex`, `definition-J`; PASS: every finite type R-algebra A has open regular locus in Spec A, with localization at a prime of A. No nonempty-locus requirement from J-0 was imported.
- Inline chain clauses: checked 00NI, `algebra.tex`, `definition-catenary`, and 00NL, `definition-universally-catenary`; PASS after explicitly limiting the latter terminology to Noetherian R. The common finite bound is for each fixed prime interval, not the entire ring; maximal chains in that interval are exactly the saturated ones described here.
- Statement dependency `def-weil-pbc-noetherian-ring`: opened its statement; PASS: every ideal is finitely generated, exactly the Noetherian predicate used here.
- Statement dependency `def-weil-pbc-g-ring`: opened its full statement; PASS: it defines Noetherian G-rings using regular maps from each prime localization to its completion. The item takes only this predicate, no unproved closure theorem.
- Statement dependency `def-weil-pbc-finite-type-algebra`: opened its statement; PASS: finitely many algebra generators, equivalently a quotient of a polynomial algebra, with n=0 allowed.
- Statement dependency `def-weil-pbc-localization-at-prime`: opened its statement; PASS: the fractions A_p and their maximal ideal are defined for primes of A, exactly as required by J-2.
- Statement dependency `def-weil-regular-scheme`: opened its statement despite its scheme title; PASS: its first sentence defines regular local rings, which is the notion actually used here.
- Statement dependency `def-weil-affine-spectrum`: opened its statement; PASS: it specifies the prime ideals with the Zariski topology, giving the meaning of the open regular locus.
- Proof steps: none (`proof: []`); PASS under stage 1 section 3(2): this item defines predicates, so there is no proof, unstated theorem, elementary inference, or step citation to audit. `citations.json` correctly remains `[]`.
- New nodes: none; PASS: J-2 and catenarity remain inline definitions rather than clause-only nodes. All six direct dependencies exist and none cites the item; their displayed dependency lists introduce no cycle.
- Duplicate and attachment search: ran whole-DAG tag and concept searches, whole-blueprint searches for excellent and catenary, and the blueprint ancestor command; PASS: the only two blueprint matches assume excellence rather than defining it, and the ancestor is `lem-exc-punctured-curve-branches`. Read the unit and chapter records. The slopmaster2 source has only a relevant English comment, not an excellent-ring declaration; master remains reference material.
- Independent Mathlib search: ran msearch.py with a new semantic phrasing about local completions and finitely generated algebras, Loogle `"catenary"`, and two grep patterns; PASS: the semantic hits concern Noetherianity, smoothness and quasi-finiteness. The first broad grep was inconclusive (25 irrelevant hits); the refined whole-word grep found only the adjective in `Mathlib/Algebra/Lie/InvariantForm.lean:32`. Each actual result is retained in searches.jsonl and recorded with an honest verdict in the item.
- Small cases: PASS: the zero ring and zero algebra have empty spectra and vacuous prime conditions; a field has only the length-zero interval; equal endpoints admit length zero; an adjacent pair has length one. Zero-generator algebras are included. These check conventions and do not assert that arbitrary Noetherian rings have open regular loci or that field excellence has been proved.
- Form B1-B7: PASS: the only node is the existing item, whose statement is self-contained, has the six appropriate notion references, uses single TeX escapes, and names all four tags and TeX labels. It contains no proof sketch or unsupported Mathlib-leaf claim.

Changes made by the second reader:

1. Made the Noetherian scope of universally catenary explicit, exactly as in 00NL. This clarifies the terminology for a general commutative R; it changes no case of the excellence predicate, which already implies Noetherianity. No statement dispute was found.
2. Removed an unrelated inherited search-verdict fragment about parameter existence, and appended the independent searches with their actual recorded outcomes.
3. Added this independent clause-by-clause and dependency-by-dependency reading. Kept the author's `## Review by Q44`, the empty proof and citations, and the correct existing definitions.

The required delivery wrapper accepts two positional arguments; the trailing period in the brief is punctuation, not an argument. The final dry run and delivery use that documented interface. No Lean source was written and no compiler or build tool was run.

Final second-reader dry run: `deliver.py Q44 def-exc-excellent-ring --no-push` printed `OK (not pushed) deliver/Q44/def-exc-excellent-ring at 6e184b2b59: preflight passed`. The captured output is `second-reading-dry-run.log` in the sandbox.
