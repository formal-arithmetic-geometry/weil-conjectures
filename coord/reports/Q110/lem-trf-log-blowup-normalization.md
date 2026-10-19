# Worker report: lem-trf-log-blowup-normalization

## Files written

- dag/nodes/sec-trace-formula/lem-trf-log-blowup-normalization.json: split statement, six proof steps; original statement retained.
- dag/nodes/sec-trace-formula/lem-trf-log-regular-divisorial-structure.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-coherent-log-ideal-chart-construction.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-log-regular-monomial-tor.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-log-regular-toric-refinement.json: statement only, unsplit; no Mathlib match.
- report.md and citations.json; the latter quotes the statements used in every proof-step citation.

- Repair: reread the current live `def-trf-fs-log-blowup` node after the maintainer return and replaced the stale Step 2 and Step 4 citation quotes with its exact current statement. The split arguments still use only the universal-property and local-log-structure clauses, so no proof step or dependency changed.

## Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 for the blueprint tag, log-blowup spellings, log regularity, logarithmic normalization, the four prospective new ids, and monomial ideals. The ordinary normalization and regular-curve declarations do not state this logarithmic result. No compiler, Lean editor, Lake or git command was run.

## WANTED

None. All source passages used are available in the ILO volume already in literature. The references to Kato and Niziol are references quoted by ILO; the nodes cite the ILO passages actually read, not an unavailable original paper.

## What needed work

The item was an unsplit node created by Q126, with no proof. Its statement is consistent with ILO VIII 3.4.6(i), VI 1.4 and VI 1.8; I found no statement dispute and changed neither its hypotheses nor its conclusions. There was no earlier sandbox attempt to reuse. I retained its source, blueprint ancestry and existing Mathlib-search record.

The comparison must not be justified by arbitrary nonflat base change of ordinary blowups. I expanded the degree-by-degree monomial tensor-injectivity calculation, the denominator/localization description and the overlap maps. Likewise, a normal finite source alone does not suffice to recognize normalization: the proof first establishes the exact triviality locus and its density, then integrality and the common function field. Finiteness of the saturation map comes from the explicit monoid chart input, not a nonexistent assumption that all locally Noetherian schemes have finite normalization. Neither excellence nor finite type over a field is assumed in this item.

The unit and chapter records were read. The item is not the key node of sk-i-curve-zero. I preserved its existing binding and its ancestor lem-trf-local-term-locality through the nearby-duality alteration/resolution chain. The current blueprint proof was read as well; this delivery splits the existing logarithmic geometric input below that ancestry and does not change the unit or chapter route. The affine blowup cover is declared as a generic off-unit tool use.

## Not duplicates

lem-trf-log-regular-divisorial-structure vs lem-trf-free-characteristic-regular-boundary: the latter's density conclusion assumes the underlying scheme is regular (free characteristic everywhere); the new statement gives divisorial structure, density and normality for arbitrary log regular fs schemes, including singular toric schemes.

lem-trf-log-regular-divisorial-structure vs def-trf-log-regular-pair: that definition starts with a divisorial log structure on a pair. It does not prove that an arbitrary log regular fs structure is divisorial or normal.

lem-trf-coherent-log-ideal-chart-construction vs def-trf-fs-log-blowup: the definition gives the fs universal property and explicitly postpones existence. The new statement supplies explicit monoid-algebra charts, their gluing/descent, the fine-category construction, and the finite saturation map for arbitrary fs log schemes, without asserting a normalization comparison or log regularity.

lem-trf-coherent-log-ideal-chart-construction vs lem-trf-monoidal-resolution-tower: that statement produces a desingularizing tower, without giving individual log blowup charts or finite saturation maps.

lem-trf-log-regular-monomial-tor vs lem-trf-log-blowup-normalization: this is the monomial-ideal injection for every ideal in a log regular chart, not a blowup comparison or any clause of the item. The item's Step 3 derives the blowup comparison from its applications to all powers.

lem-trf-log-regular-toric-refinement vs lem-trf-log-blowup-normalization: the new statement concerns any saturated extension P into its own group completion on one chart. It mentions neither log ideals nor blowups nor normalization; it is the general log-regularity preservation input used on the saturated blowup charts.

Before creating these nodes I searched the entire DAG by log regularity, log blowup, saturation, monoid, divisorial, Tor/monomial and the exact source places, and ran blueprint_refs search for log regular, log blowup, monoidal ideal, monomial, monoid, log smooth, saturated log and logarithmic. No blueprint node gives these statements. I read the statements of the existing logarithmic candidates listed above instead of relying on proof-text matches. No new node carries a Stacks tag shared with an existing node.

## Review by Q110

For this repair I reread the live `def-trf-fs-log-blowup` statement and checked that Steps 2 and 4 use clauses it still states: the fs saturated-log-blowup universal property and the local condition identifying nonunits through the structure map. The exact current statement is copied verbatim in `citations.json` for both citations.

I read the ILO volume, Expose VI 1.1--1.8 (printed pp. 69--70), VIII 3.1.17--3.1.21 (printed p. 101), 3.2.9 (printed p. 104), 3.3.5--3.3.11 (printed pp. 107--108), 3.4.1--3.4.7 (printed pp. 110--111), and 3.5 (printed pp. 114--115). VIII 3.4.6 proves the comparison by a chart and Rees calculation, and the present split follows that calculation. VI 1.4 gives the dense divisorial description, VIII 3.5 explicitly identifies saturation with normality in the log regular setting, and VI 1.8 gives the preservation input for the toric chart maps. No SGA source is used.

For the new divisorial node I checked that it assumes fs and log regularity, not regularity of the underlying scheme. Its normality clause means normal local domains, and its integral affine clause is integrally closedness in the fraction field; it asserts no finiteness of normalization. The new construction node assumes only fs and local Noetherianity, defines Q_h and its saturation in P^gp explicitly, and gives both fine and fs universal properties. The chart maps are from the common original P, not a mistaken base change along an unrelated monoid. The finite saturation statement is the base-changed finite monoid-algebra saturation of VIII 3.2.9. Its finite-type quasi-coherent ideal clause includes strict-etale pullback compatibility, so Step 1 does not cite just a definition for a descent theorem. For the monomial tensor node I checked VIII 3.4.3: Tor_1(Z[P]/Z[H], A)=0 gives exactly the injection stated. The image is the generated ideal. It does not assert flatness of A over Z[P]. The refinement node keeps the group completion unchanged; thus the chart criterion has zero kernel and cokernel on groups, and VI 1.8 applies. Finite generation gives finite-type chart algebras over the locally Noetherian base. All four new nodes contain statements only, with no hidden proof or proof dependencies.

I checked every citation against the actual statement, and supplied verbatim quotes in citations.json. Step 1 uses the construction node for finite-type quasi-coherence and the divisorial node for density and units, from which nonzeroness follows. Step 2 uses the construction node for actual charts and finiteness, the definition for the requested universal property, and the refinement node for log regularity; these are different assertions. Step 3 uses the monomial tensor node for each power, not an unjustified flatness claim. Products of basis monomials show compatibility with multiplication. The localization colimit describes the actual chart ring, and the ordinary cover and chart-ring definitions say exactly what is identified. The construction node states strict-etale descent and compatibility, so the canonical maps agree on both ordinary chart overlaps and changes of log chart. Step 4 cites only the definition, and writes the universal-property and local-maximal-ideal arguments out; it does not suppose that the image of a nonunit remains nonunit under an arbitrary nonlocal ring map. Step 5 uses only the cover and the subalgebra definition to prove integrality of the ordinary blowup. Step 6 uses the divisorial node on the locally Noetherian log regular source already obtained, and uses the normal integral affine clause on D. Finiteness came from Step 2 and survives the isomorphism of Step 3. The two inclusions between D and the integral closure of C are written explicitly, so the normalization-definition citation really supplies only the normalization object, not an unstated theorem.

I checked the hypotheses and small cases as follows. For trivial log structure, U=X, every nonempty log ideal is the unit ideal, both blowups are the identity and normality of the log regular base agrees with regularity. For a locally principal log ideal the universal property gives the identity and the normalization comparison is consistent because the log regular base is normal. For the standard N^2 chart of the coordinate axes in A^2 and the ideal generated by the two basis elements, the charts are k[x,y/x] and k[y,x/y], their boundary complement is the same torus, and the blowup exceptional divisor has nontrivial log structure. For (x^2,y^2), saturation adds y/x and x/y on the two charts, illustrating why unsaturated and saturated charts must be distinguished. A singular saturated toric cone has normal, possibly singular base, so the divisorial node cannot be replaced by the existing free-characteristic regular-boundary statement. Empty chart spectra and rank-zero monoids are allowed. No characteristic restriction is introduced; in particular the monomial injection is not inferred from ordinary flatness over Z[P].

All Mathlib searches for new nodes were run through msearch.py, including two natural-language phrasings and Loogle plus grep, and the returned types were read. The source of the plausible tensor-flatness and Tor-projective hits was opened: Flat/Basic.lean 410--421, Smooth/IntegralClosure.lean 51--57, and CategoryTheory/Monoidal/Tor.lean 56--64 require flat/projective hypotheses absent here. The broad Tor grep had substring noise (toRingHom etc.); I ran and recorded a word-boundary grep too, whose one hit is only a comment on categorical Tor. The other hits are ordinary normalization, ordinary scheme/Proj charts, unit logarithms of number fields, ordinary etale morphisms or category-theory coherence. None states a new node even by a one-line specialization.

No proof step exceeds 2000 characters. I checked B1--B9, C1--C7, D1--D5 and E1--E6 against the actual node statements and cited source text: no proof moved wholesale into a new node, no cycle through the already split parent, no new target statement, no false coefficient identification and no missing field-base or excellence hypothesis. The server review_split check passed before this report was completed. The complete delivery dry run passed at ec39995ce1. A final citation audit then added the existing Mathlib leaf lem-weil-pbc-finite-algebra-is-integral to Step 6 (Stacks 00GK, lemma-finite-is-integral, read in algebra.tex), and made explicit that the charts use fs P and that Q_h and Q_h^sat are finitely generated with group completion P^gp. This corrects a potential C1/C4 ambiguity without changing any mathematical claim. Citations were regenerated; the final dry run is repeated after these changes.

## Unfinished

No unresolved argument in the item's six-step split. The four deliberately unsplit input nodes are the next stage-1 tasks. No Lean proof is claimed.
