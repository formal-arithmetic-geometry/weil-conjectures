## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-excellent-normal-surface-local-data.json`: statement, now split into ten proof steps; not a Mathlib leaf. All hypotheses and conclusions are unchanged. Added `def-kun-topological-krull-dimension` to statement dependencies because the dimension of X is topological dimension, rather than the ring dimension alone.
- `citations.json`: 29 verbatim statement quotations for all node citations in the ten steps.
- `report.md`: this report. `searches.jsonl` records the actual search-command calls; `prepare.py` is a sandbox-only JSON-writing helper.

New nodes: none. New Mathlib leaves: none.

Attachments: none. The project-source searches for the exact id/docstring tag and for excellence, normal surfaces, singular loci and regular loci found no declaration proving this conjunction. The two keyword hits concern a smooth locus and a comment on etale finiteness, not this statement. The upstream master reference is not treated as evidence of finished proofs.

WANTED: none. All source material used is present in the repository.

The original item had no proof. Its source mentions 0BGN, but that tag is resolution of a complete normal local surface, not the elementary finite-singular-set observation. The proof sources now locate the surface observation in the discussion of 0BGP and explicitly write its prime-chain argument. No source assertion or item statement needed correction; there is no statement dispute. No unit or chapter record was changed. The item is a supporting input to the existing 0BGP (4) implies (3) resolution route, along its recorded potential-dualizing-complex ancestry to Step 1 of `lem-per-artin-gabber-affine-curve`.

Nothing mathematical is left unfinished at this split level; the generic inputs already have nodes. This is a one-level split, not a claim that every generic input is already proved in Lean.

## Searches and reuse

I searched the whole DAG by the exact id, normal-surface/local-data phrases, regular and singular locus keywords, completion/normal keywords, and the tags 07QT, 07QU, 0C23, 07NV and 031S. I opened every node ultimately cited. In particular, the existing closed-point finiteness lemma avoids a new topological lemma; Serre's criterion and its existing R1 definition avoid a special surface-regularity node; and regular-completion, regular-implies-normal, and flat-normal-fibre ascent avoid a duplicate excellent-normal-completion node. None of the input statements has the surface-local-data lemma as a prerequisite.

`tools/blueprint_refs.py ancestor` identifies `lem-per-artin-gabber-affine-curve` as the ancestor. Whole-blueprint searches for `excellent normal surface local data`, `0C23 07NV 07QT 07QU`, `normal surface`, and `completion normal` found no equivalent node. The broader `singular` search found only two unrelated curve-cohomology nodes. Thus `same_as` is empty.

The item's existing Mathlib searches were retained. I ran and read the logged LeanFinder, Loogle, grep and LeanSearch queries recorded in `searches.jsonl`, including a second LeanFinder phrasing. The hits give integral and Noetherian scheme properties, the closed point of a local spectrum, finite dimension of a Noetherian local ring, a DVR criterion and the smooth locus. None states J-2 openness plus codimension-two singular-point finiteness and normal completed stalks. No service was unavailable in these calls. No new node requires its own searches.

## Off-unit tool uses

The split declares the following generic tools in `split_report.tool_uses`; it does not write the maintainer's `tool_uses` field. These are the same commutative algebra and topology arguments called for by the item's Stacks sources, not replacement routes for the unit.

- `lem-exc-finite-type-localization-excellent`: localize the excellent affine coordinate ring to obtain excellence of the stalk (07QU).
- `lem-sc-noetherian-closed-points-finite`: after the surface argument proves closedness of every singular point, deduce finiteness of this closed subset.
- `lem-weil-pbc-serre-criterion-normal`: extract R1 for the Noetherian normal affine rings (031S).
- `lem-weil-pbc-adic-completion-noetherian`: obtain Noetherianity of the completed stalk (0316).
- `lem-weil-pbc-completion-dimension`: preserve its dimension (07NV).
- `lem-weil-pbc-g-ring-completion-regular`: obtain flatness and geometrically regular formal fibres (0AH2).
- `lem-weil-pbc-regular-ring-normal`: turn the regular formal fibres into normal fibres (0567).
- `lem-weil-pbc-flat-normal-fibres-noetherian-normal`: ascend normality to the completion (0C22), exactly as the proof of 0C23 does.

## Not duplicates

No new nodes were created. There are no new/existing same-tag pairs requiring a distinction.

## Review by Q15

I read `more-algebra.tex` at 07QT (`definition-excellent`), 07QU (`lemma-finite-type-over-excellent`), 0C23 (`lemma-completion-normal-local-ring`), 07NV (`lemma-completion-dimension`), and 0AH2 (`lemma-map-G-ring-to-completion-regular`). I read `algebra.tex` at 031S (`lemma-criterion-normal`), 0567 (`lemma-regular-normal`), 0C22 (`lemma-normal-goes-up-noetherian`), 00E3 (`lemma-spec-localization`), 00GY (`lemma-localize-normal-domain`), the completion-Noetherian and completion-complete lemmas and 05GI (`lemma-radical-completion`). I also read 0BGP (`theorem-resolve`) in `resolve.tex`, and the finite-component argument in `properties.tex` at 0BA8 together with the existing closed-point finiteness node. The chapter and unit records and the current blueprint ancestor were read. The source hypotheses do not require separatedness, finite type over a field, Jacobsonness, or that every closed point have local dimension two. Our proof uses none of those extra assumptions.

1. Step 1 uses the affine-open-stalk localization statement for the precise ring isomorphism to a prime localization; the localization-Noetherian statement applies to each Noetherian cover ring. Normality is the local normal-domain property assumed of X, so the normal-ring definition gives normality of each cover ring. I checked that the citation is an actual localization statement, not merely a definition of a stalk.
2. Step 2 takes J-2 from the statement of the excellence definition. The identity algebra is finite type using an empty generator set. The regular-scheme definition identifies the terminology with regular local stalks. Taking the union of these locally open regular loci is elementary; no general theorem asserting an open regular locus is silently assumed.
3. Step 3 uses the spectrum irreducible-closed-subset dictionary and the prime-localization bijection, with the two dimension definitions. It writes out why a prime chain in an affine open gives a chain in X: closures remain irreducible, and restriction back to the open proves strictness. For the irreducibility assertion, a separation of a closure by two closed sets would separate its dense irreducible subset, forcing that subset and then its closure into one set. The bound for a stalk follows by contracting its prime chain. This is a short dimension-definition argument and is marked elementary, not promoted to a node.
4. Step 4 uses exactly the normal iff R1 and S2 statement of Serre's criterion; only R1 is used, and the cited R1 definition says regularity for all prime localizations of dimension at most one. No implication from normality to regularity in dimension two is assumed. Combined with Step 3 this forces each singular stalk to have dimension exactly two.
5. Step 5 cites the statements giving specialization as prime inclusion and the prime-localization bijection. A proper specialization would append one prime to a length-two chain ending at the original prime, giving length three in an affine neighbourhood of the specialization. Such a neighbourhood contains both points. The endpoint assertion follows because in a local ring every prime is below its unique maximal ideal; otherwise that maximal ideal could itself be appended. This is the missing closedness argument, written explicitly rather than assuming X Jacobson or equidimensional. No resolution theorem is used here.
6. Step 6 opens and uses `lem-sc-noetherian-closed-points-finite`: its statement requires a Noetherian scheme, a closed subset, and every point of that subset closed in the ambient scheme. These are precisely the hypothesis on X, Step 2, and Step 5. I did not cite the finite-components statement as though it directly asserted finiteness of points.
7. Step 7 applies 07QU through its existing node, with R_i excellent, the identity finite type algebra, and the complement of the stalk prime as multiplicative set. The localization-normal-domain statement gives normality at every prime of A, so A is a normal ring as well as the normal domain given by the scheme hypothesis. This checks the precise normal-ring hypothesis needed in Step 9.
8. Step 8 uses five statements: completion is Noetherian; local completion has maximal ideal mB; a Noetherian ring has finitely generated ideals; completion along a finitely generated ideal is complete for the extended ideal; and local completion preserves dimension. The extended ideal mB really is the unique maximal ideal, so completeness is for the topology asserted in the item. The quoted dimension node is for the maximal-ideal completion of a Noetherian local ring, exactly our A.
9. Step 9 first gets the G-ring property from excellence. The completion-regularity node states both flatness and Noetherian geometrically regular fibres for arbitrary ideal completion. The geometric-regularity definition allows the identity extension (degree one, purely inseparable), hence yields regular fibres. The regular-normal node then gives normal fibres. I checked each of the five hypotheses in the flat-normal-fibre ascent statement: A and B Noetherian, the map flat, its fibres normal, and A normal as a ring. This is the actual proof of 0C23, not a new node restating the item's completion clause.
10. Step 10 uses the definition of normal ring at the unique maximal ideal. It explicitly gives the inverse to localization at that ideal, since all inverted elements are already units. It thereby obtains a normal domain, not just a ring that is normal at its prime localizations. All other completed-ring clauses are supplied by Step 8.

I checked the small and boundary cases: if X is regular, the singular set is empty and all statements about singular stalks are vacuous; no singular point is forced to exist. A field or a one-dimensional normal local ring cannot be a singular stalk by R1; the argument therefore does not accidentally assign dimension two to every closed point. A non-Jacobson two-dimensional scheme is allowed because Step 5 proves closedness without a Jacobson assertion. The need for excellence is retained at regular-locus openness and normality of formal fibres; the proof would not incorrectly make arbitrary normal local rings analytically normal. The completion is the maximal-ideal completion throughout, not an arbitrary ideal completion when using dimension equality. No new statements were introduced, so there are no additional new-node edge cases. I retained all original statement clauses, removed no hypotheses and made no unsupported attachment.

Against delivery-errors B--E: no new statement-only node is needed; all non-elementary facts have existing cited statements, and every quote in citations.json is verbatim. The split carries the prime-chain surface argument rather than moving clauses into new nodes. Source tags and labels were checked in the local TeX. No step exceeds 2000 characters (the maximum is 769). I corrected the initial possibility of citing 0C23 directly by using the existing regular-completion/normal-ascent inputs, avoiding a duplicate completion lemma. The closedness proof was expanded before delivery to include the affine-neighbourhood and maximal-chain endpoint arguments. No Lean source, compiler, library build, live node or launcher file was written or run.
