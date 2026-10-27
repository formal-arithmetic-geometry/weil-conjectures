# Q89: lem-sf-bc-field-mate-domain

## Files written

- dag/nodes/sec-six-functors/lem-sf-bc-field-mate-domain.json: statement, split; no Mathlib match; six assembly steps using existing nodes.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report. searches.jsonl is the search command's actual log; write_split.py is a sandbox-only JSON preparation script.

No new nodes; no Mathlib leaves. The imported statement, statement dependencies, creation provenance and blueprint ancestry are retained.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint id and rational exchange/common-stage terminology found no project declaration stating this whole item. The existing common-stage construction and coefficient pointers do not prove the geometric theorem, the admissibility conditions, or all its clauses. The paper-specific smooth coefficient modules under lean/Sheaf are reference material, not an attachment under the brief.

## WANTED

None. Sources needed for the assembly are present locally.

## What needed work

The item was statement-only, not a reviewed split; no released repair note exists. Its statement already distinguishes raw rational, ambient Karoubi, and common-stage categories and includes the necessary smooth lattice and four-family interval hypotheses. No statement correction is needed. Reusing the existing proper and smooth coefficient theorems avoids new nodes which would merely repeat individual clauses.

The original smooth E and Qbar blueprint files print the output corner as S, although their exchange has target on X. The live cited DAG statements already repair that typing. The original Qbar proof also describes a derived inverse limit over finite coefficient fields; the live node correctly uses common-field morphism classes, not such an inverse limit. This split follows those corrected statements and explicitly describes representatives and inverse classes. Neither old error is copied into the argument.

## Mathlib and blueprint searches

Ran the required msearch commands for this item: LeanFinder with two distinct formulations, Loogle for CategoryTheory.Functor.IsLocalization, LeanSearch for scalar localization and coefficient representatives, and grep for rational exchanges and adic/etale base change. All results were read; all five queries are recorded from searches.jsonl without changing their text. LeanFinder returned condensed-module structures/adjunctions and abelian localizations; LeanSearch returned localized-module scalar formulas; Loogle returned ordinary categorical localization constructions; grep returned stability of etale scheme/ring morphisms and finite-etale algebra base change. None states the geometric completed exchange on admissible rational lattices or the common coefficient stages, and none is a one-line specialization giving this theorem. Previously recorded searches on the live item are retained as provenance; the current group's actual searches were added separately.

Whole-DAG keyword searches identified the exact existing proper and smooth coefficient theorems, canonical completed mate, geometric hypotheses, and common-stage descent/calculus nodes. blueprint_refs.py ancestor reports prop-functor-package. Whole-blueprint searches for rational exchange and smooth base change identified the same proper/smooth inputs; no blueprint node states this combined proper/smooth domain and specified-map assertion. A further scalar localization search was run to check the coefficient-transport terminology. No new node was created.

## Not duplicates

No new nodes or new/existing pairs. The split cites thm-weil-pbc-finite-extension, thm-weil-pbc-qbar, sbc-thm-e-coefficient-smooth-base-change and sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch directly instead of creating their specializations.

## Review by Q89

I read the item's live statement and prop-functor-package.proof.md in main-20261015, the sec-six-functors chapter record, the sk-thm-sf-package unit record, and the original master blueprint files for the proper E/Qbar and smooth E/Qbar theorems. These give exactly the unit's route: completed integral exchange, rationalization, then coherent scalar-field descent. The proof is marked agent-written because this is an assembly from the blueprint and the corrected DAG interfaces, not a claimed direct transcription of a human proof. No SGA source is used. There are no new nodes requiring independent sources.

For step 1 I opened lem-sf-bc-geometry-hypotheses. Its statement gives all four corners Noetherian and finite-dimensional, invertibility of ell, qcqs arrows, properness of f' when f is proper, and a uniform geometric fibre dimension bound. Thus the extra hypotheses of the proper finite-extension theorem and the smooth E theorem are actually discharged, rather than inferred from a definition citation. This sibling has no dependency on the item.

For step 2 I opened the full statements of lem-sbc-completed-operations-linear-natural-exchange and def-exchange-projection. The first supplies the actual integral adjunction, pullback compositor, unit/counit exchange and its finite-reduction identification. With its f,g,h,e renamed g,f,f',g', that formula has precisely source Lg* Rf* and target Rf'* Lg'*. The definition's higher-coefficient paragraph explicitly takes rationalizations and common-field classes of these maps. This checks equality of the specified map, not merely the existence of some isomorphism between the same endpoints.

For step 3 I read thm-weil-pbc-finite-extension and thm-weil-pbc-qbar. The first states invertibility of the rationalization of the completed integral exchange under exactly the geometric hypotheses supplied in step 1. Its raw rational category is the same category named in the item. The second states invertibility of the descended exchange and explicitly its M-coefficient representative and independence of all fields and representatives. Both statements provide what the step takes from them.

For step 4 I read sbc-thm-e-coefficient-smooth-base-change and sbc-def-admissible-lattices. The smooth theorem's input corner T becomes our X, its output corner X becomes our Y', and its smooth arrow f becomes our g. The other arrow is qcqs by step 1. The source lattice is supplied by the item, and the theorem requires exactly finite-level etale admissibility for ambient invertibility. Only its square-admissible clause grants constructible landing. I checked that this includes one interval for all four listed finite operation families; no separate intervals, constructibility inferred from definition alone, or finite reduction of a rational object is used. The explicit conjugation by the specified lattice isomorphism proves how the intrinsic exchange value is recovered. The n versus m+1 indexing is stated.

For step 5 I read the live smooth Qbar theorem and def-sbc-ambient-complete-coefficient-categories. The theorem requires hypotheses for every representative under consideration and preservation under finite overfields: these are exactly stipulated in the item. It states the raw-to-identity-idempotent representation and the further-field representatives. The definition carefully distinguishes raw rationalization from its ambient Karoubi envelope. The proof uses the inclusion on raw objects and maps, and does not assert that the whole ambient envelope is equivalent to the raw category.

For step 6 I reopened the square-admissible clause of the smooth E theorem, prop-weil-pbc-scalar-extension, prop-weil-pbc-descent-functors and prop-weil-pbc-common-stage-calculus. The first gives the finite-stage constructible endpoints. Scalar extension's statement supplies the canonical comparison maps and their compatibility with this exchange, explicitly conditioned on constructible landing where needed. Descent's statement gives the value on a representative and descent of compatible transformations and equations. Common-stage calculus gives representative independence. I wrote out the inverse representative argument, so no unsupported assertion that a colimit preserves isomorphisms is hidden. Conditional constructible operations here mean the finite-stage values in the item's stated domain, and do not assert an unconditional global preservation theorem for ambient direct image.

I checked delivery-errors B through E against the files: no new proof disguised as a statement-only node, no duplicate, no clause moved into a new node, no definition used as a missing theorem, no altered imported statement, and no citation of a proof's internal construction. Every use appears in proof_deps, and each quotation in citations.json is copied literally from the cited statement. I checked the transitive dependency closure of every main candidate input for a path back to this item: none exists. Each proof step is under 900 characters, well below the long-step review threshold.

Small cases: identity squares have the same specified mate and fit both branches; empty schemes and empty fibres are allowed by the geometry input; the raw zero object and identity coefficient extension cause no extra field change or idempotent choice. A lattice with only finite-level etale admissibility still gives only ambient smooth invertibility. Dropping the common uniform interval never produces a constructible conclusion. The inverse class at a common stage uses the same endpoints and field as its component, so no further admissibility for an unrelated object is needed.

## Unfinished

No mathematical part of this one-level split remains. All lower-level inputs are existing DAG nodes and keep their own proof obligations.
