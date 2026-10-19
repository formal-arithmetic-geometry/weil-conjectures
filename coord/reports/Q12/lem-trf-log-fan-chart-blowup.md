# Worker report: lem-trf-log-fan-chart-blowup

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-fan-chart-blowup.json`: statement node, now split in ten steps; no Mathlib match.
- `citations.json`: verbatim statement passages for every node citation in those ten steps.
- `searches.jsonl`: five actual searches in this attempt; the item's inherited searches are preserved in its record.
- `report.md`: this report. The sandbox also contains the local writer script; it is not a delivered project file.

There are **0 new nodes and 0 Mathlib leaves**. No Lean files, shared files, launcher files, unit records or chapter records were changed.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id and for fan charts, fine fans, log blowups and logarithmic schemes. The hits concern logarithmic derivatives and category-theoretic fans, not logarithmic schemes or this statement. No project declaration states the item.

## WANTED

None. The required ILO volume is available locally.

## Problems found and changes made

The item arrived unsplit and had no earlier sandbox proof or report. Its statement agrees with ILO VIII 3.3.4(ii), 3.3.12 and 3.3.13(i),(iii), with finite-cover extraction as in the proof of 3.3.15. I retained it verbatim. I made the source locator explicitly include 3.3.12 and the monoid chart construction in 3.1.1--3.1.25.

There are two potentially misleading shortcuts to avoid in proving this item. First, a fan chart need not have a global lift to a monoscheme chart; ILO 3.3.13(ii) specifically warns about that. Steps 3--5 instead construct the required lifts Zariski locally, and step 8 proves that the induced fan maps do not depend on those lifts. Second, fs base change is not asserted to be the ordinary scheme fiber product. Step 10 proves the representing property in the fs category directly.

The locally Noetherian hypothesis used by the existing log-ideal construction is already part of the fs-log-scheme convention of `def-trf-fs-log-blowup` (and of ILO VI 1.1), so it is available for both V and every constructed fs log scheme. There is no extra log regularity or regular-strata assumption. The separate torsion-free assumption in (i) is harmless: the fs face-sharpening statement actually shows that these characteristic groups are free already.

No statement dispute or route change is asserted. The current unit's contracting-correspondence proof is not replaced: the item belongs to the retained historical nearby-duality alteration branch recorded in its blueprint ancestry. I read the chapter and unit records and the current `main-20261015` unit text. The nearest blueprint ancestor remains `lem-trf-local-term-locality`, with its existing `via` chain preserved.

## Searches and reuse

Whole-DAG keyword searches found the existing `lem-trf-fs-face-sharpening`, `lem-trf-associated-log-universal-stalks`, and `lem-trf-coherent-log-ideal-chart-construction`. Their complete statements were read. The last of these already supplies the actual affine saturated log-blowup charts, their gluing, their descent and their universal property; a new node for existence of these blowups would duplicate it. The strict fan comparison and functorial tower-descent nodes depend on this item and are not used. The stronger log-regular sharp-chart node has an unnecessary log-regularity hypothesis and is not used either.

I ran `tools/blueprint_refs.py search` for `fan chart`, `log blow`, `logarithmic blowup` and `monoidal space`, with no blueprint match, and inspected the broader `monoid` search and the ancestor result. No new node is needed. The two ordinary scheme facts used to extract the finite cover already have Mathlib leaf nodes: `lem-weil-pbc-affine-scheme-qcqs` and `lem-weil-pbc-etale-morphism-open-map`.

All five Mathlib queries in this attempt ran through the prescribed `msearch.py` command and were read: two LeanFinder phrasings, LeanSearch, Loogle for `"LogStructure"`, and a whole-Mathlib grep for logarithmic structures and monoidal fans. The semantic hits are ordinary etale maps, scheme gluing, affine transition limits, projective spectra and normalization; none supplies the logarithmic statement. Loogle and grep returned no hits. The actual log records, tools, exact query texts and results are appended to the item without replacing its inherited searches.

## Not duplicates

No new nodes. All support is reused; no clause of the item has been moved into a new statement.

## Review by Q12

I read ILO Expose VIII, printed pp.98--102 (3.1.1--3.1.25), pp.106--109 (3.3.2--3.3.13 and the beginning of 3.3.15), and Expose VI printed pp.69--70 (fs convention and characteristic monoids). The proof follows that affine-chart route, with the local lift and overlap argument that 3.3.13 leaves implicit written out. I opened every cited node's statement, rather than taking facts from its proof. In particular the log-ideal construction node explicitly supplies saturated charts for *all* locally Noetherian fs log schemes and arbitrary nonempty coherent log ideals, not merely log regular schemes. The monoid saturation node explicitly supplies finite generation and commutation with localization, which are the only parts used in step 8.

Step 1 uses the fs definition for etale-local monoid charts; the associated-log node for the stalk pushout; the face-sharpening node for the localized characteristic quotient and its free group; and the fan definition for the target spectrum. The prime ideal is explicitly the complement of the unit face, so the continuity and stalk identifications can be checked from those definitions. A constant prelog chart is Zariski, and its etale associated log structure has exactly the cited stalk formula.

Step 2 uses precisely the affine qcqs statement for quasi-compactness of the affine sources, and the etale-open-map statement for openness of their images. Refinement and finite selection are the scheme affine-open basis and the stated definition of quasi-compactness. This does not assume quasi-separatedness of X or quasi-compactness of an etale covering morphism.

Step 3 uses the fan definition and face-sharpening statement to identify the affine localization at c(v), including the fact that its sharp monoid has a free finite-rank group. A face of a finitely generated monoid is generated by the original generators it contains; inverting their sum gives the required basic open. This explains the affine localization instead of citing a definition as if it were a localization theorem.

Step 4 uses the fs definition for integral log monoids and the quotient by units, and the *free-group conclusion* of face-sharpening. Choosing basis lifts splits the group extension. Each positive monoid generator differs from its lift by a unit at v; finitely many generators let one spread that positivity and agreement with c on one Zariski neighborhood. The original log structure is Zariski by the fan-chart hypothesis, so these are Zariski germs and no unnoticed etale-to-Zariski descent is invoked. No arbitrary choice of units needs to be consistent with separate monoid relations: the map is defined first on the free group.

Step 5 uses the associated-log node's universal property and stalk formula, together with face sharpening, to verify that this lift is a genuine chart. The elementary injectivity check uses integrality and identity on units; surjectivity is lifting a characteristic class then correcting by a unit. Thus the proof does not confuse a characteristic chart with a log chart.

Step 6 uses the fan definition for finite nonempty generators of J and the log definition for the pullback ideal. The formula for its preimage in N is checked by lifting the residual characteristic summand and correcting by a unit. This proves coherence and nonemptiness before applying the log-ideal construction theorem. Its Noetherian and fs hypotheses hold, and it supplies existence and the precise universal property used here.

Step 7 uses the log-ideal construction's actual monoids R_a and tensor-product ring charts, the defining saturated fan charts, and the associated-log and face-sharpening statements for the characteristic at every point. The two sides are the *same* localized sharp monoid. No regularity, flatness or ordinary blowup comparison is hidden in this identification.

Step 8 uses the fan definition's chart gluing, integral fs monoids from the log definition, and finite generation/localization from the saturation node. The uniqueness argument is explicit: a principal ideal generated by finitely many images has a generator among them at the stalk, differences determine the map on P[E-a], and saturation determines the remaining elements inside the group completion. Where two generators work their difference is a unit, exactly the gluing localization. This checks different monoid lifts as well as overlaps of the blowup charts. The resulting maps and sheaf isomorphisms glue in the ordinary Zariski topology, so the source remains Zariski.

Step 9 applies the preceding construction inductively with the ordered centers. The induction has an explicit zero-length base and one-step construction; no conclusion is assumed to construct its predecessor. The log-ideal theorem supplies the fs schemes at each stage, and their characteristic charts and center coherence were proved in steps 6--8. Concatenation uses the same ordered centers and their universal factorization.

Step 10 uses the log definition's universal property and pulled-back ideals, the construction theorem's existence on W, and the associated-log stalk pushout to pass through strictness. The scheme representing the fs fiber product is identified by its functor of maps from fs test objects, and the equality of centers is checked on the actual generators. Uniqueness from step 8 identifies the fan maps. Applying that universal property again establishes coherence for composite strict base changes and for towers; ordinary scheme fiber products are not substituted.

For edge cases I checked the empty scheme and empty cover, trivial characteristic P=0, a unit center J=P (the corresponding chart is unchanged), a principal nonunit center (also an identity log blowup), and the zero-length tower. For a concrete nontrivial chart P=N^2 and J=(e1,e2), the two monoids are the saturated submonoids generated by P and e2-e1, respectively P and e1-e2; their overlap inverts the difference, exactly as step 8 requires. This check also allows a log point with all nonzero monomials sent to zero: the argument never assumes the algebraized ideal is nonzero. A non-saturated target fan away from the image causes no problem, since every localization at an image point is the fs characteristic monoid given by c.

I checked B--E of the delivery-errors document: no new-node form issues or duplicate clauses, complete statement citations, no use of another node's proof, no cited SGA source, and no extra hypotheses. A read-only traversal found no dependency path back to this item among the reused support. All ten proof steps have fewer than 2000 characters. No independent reader is claimed by this signature; this is Q12's direct-delivery self-review.

## Unfinished work

No mathematical part of the split is deferred beyond the existing cited DAG nodes. Server dry-run and delivery results are recorded below when available.
