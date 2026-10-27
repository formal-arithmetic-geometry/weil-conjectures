# Q119: lem-pur-sequence-kflat-comparison-shifts

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-sequence-kflat-comparison-shifts.json`: statement item, now split in seven steps; not a Mathlib leaf. The statement, statement dependencies, creation record and inherited blueprint provenance are retained.
- `citations.json`: 17 literal statement excerpts, one for every step/node citation.
- `searches.jsonl`: actual msearch records; existing imported search records in the item are preserved and the six searches of this dispatch are appended to the item.
- `report.md`: this review and delivery report. `write_split.py` is sandbox-only drafting material.

New nodes: **0**. New Mathlib leaves: **0**. No unit record is changed: this item is not the unit's key statement.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, K-flat quotient-system notions, `StrictRingSystem`, `SystemScalarModel`, ringed sequence/projection names and sequence pullbacks found no declaration stating the whole item. Generic pro-etale pullback/K-flat infrastructure does not identify this quotient-sequence reduction and all its prescribed shifts.

## WANTED

None. The necessary Stacks sources and current blueprint are available locally.

## Corrections and source comparison

There is no statement dispute. The item arrived statement-only, so the work supplies the proof rather than replacing a previous split. Its historical `source.document` and ancestry are retained as provenance. I read the current route at `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/_section.md` and `fix-prop-coherence.proof.md`, particularly clause (7) and the paragraph about coefficient comparisons preserving the individual maps. The latest blueprint organizes this under compatibility, not the older package directory in the item's source record. The item remains the ordinary unbounded strict-system tool required by that route; no condensed/complete coefficient category is silently substituted for it.

Two potentially misleading shortcuts are avoided in the argument. An isomorphism after each finite evaluation alone is not used to identify system maps: the identification is made in the derived category of strict systems by normalized resolving descent. Also, shifting the second tensor factor needs the sign depending on the first factor's degree; the identity for scalar extension instead comes from a degree-zero coefficient factor. These are checked separately.

## Not duplicates

No new node is created. In particular, the already existing `lem-sp-strict-coefficient-tensor-descent` supplies the generic strict-system descent and its uniqueness, and `lem-weil-pbc-ringed-topoi-derived-pullback` supplies the universal pullback computation. The broader sequence-projection and finite change-of-rings nodes were read, rather than reintroduced. Searches with `tools/blueprint_refs.py search` for sequence projection, quotient-projection, coherent shifts, K-flat quotient, strict coefficient and tensor shifts found no blueprint node with the item's whole statement; `same_as` stays empty.

## Mathlib assessment

I ran LeanFinder twice with different descriptions, Loogle, LeanSearch and two msearch greps, and read the returned relevant sources. `SheafOfModules.pullbackIso` (`PullbackContinuous.lean:106`) describes ordinary sheaf pullback, and `pullbackComp` (line 167) describes composition. The free-sheaf pullback identities in `PullbackFree.lean:125` are ordinary identities. `CategoryTheory.Functor.commShiftMapCochainComplex` (`HomotopyCategory/Shift.lean:255`) has the expected identity components for an additive functor; exact-functor derived factorizations in `DerivedCategory/ExactFunctor.lean` require exactness and do not derive a nonflat coefficient extension. The second LeanFinder search returned generic right-derived comparison machinery (`Localization/DerivabilityStructure/PointwiseRightDerived.lean:64`) and left derived functors of abelian objects, not the present normalized strict quotient-system comparison. K-projective shift closure is about a different class. None is an exact match or a one-line specialization of this whole item. No query is recorded as run unless it appears in the actual command log.

## Review by Q119

I read Stacks `sites-cohomology.tex` Tag 06YY (`lemma-derived-base-change`) including its proof, Tag 06YS (`lemma-K-flat-resolution`), Tag 06YN (`definition-K-flat`), Tag 0G7D (`lemma-factor-through-K-flat`), and Tag 0940 (`section-derived-limits`, the constant/limit sequence morphism and evaluation). I also read the dual resolving-class assertion in `derived.tex` Tag 06XN (`lemma-find-existence-computes`). The tensor differential is the direct-sum total convention recorded by `def-pc-tensor-complex-sheaves` from `homology.tex` Tag 012Z. The explicit sign and coherence computations are my argument, so `proof_origin.by` is `agent`. There are no new nodes whose statements need a separate source review.

For step 1 I opened `lem-weil-pbc-ringed-topoi-derived-pullback`: its statement really supplies the universal derived counit isomorphism on flat-term K-flat complexes, inverts the relevant quasi-isomorphisms, and gives natural comparisons. Its hypotheses hold because the projection in the item is supplied as a ringed-topos morphism and the sequence of a fixed small site is small in the module universe. I opened `def-coef-ringed-sequence-site` for the vertical topology and strict semilinear interpretation, and `def-pur-sheaf-tensor-product` for sheafified tensor. The level formula follows by the vertical covering condition, including the actual horizontal quotient maps.

For step 2 I opened `lem-sp-strict-coefficient-tensor-descent` and checked that it explicitly states uniqueness of normalized descent, naturality on derived roofs, and a functor into the derived category of strict systems. Its arbitrary commutative ring sheaves specialize to A and B_n, and the compatible quotient maps are A-algebra maps. `lem-coef-derived-system-evaluation-calculus`, already a statement dependency, supplies exactly that canonical strict K-flat reduction functor. `lem-pc-kflat-resolution` supplies flat-term representatives for all unbounded inputs. Thus the comparison is an identification of two descents of one functor, not an arbitrary choice between objects with equal evaluations.

For step 3 those same strict-descent statements and `lem-pur-derived-change-of-rings` give finite evaluation and canonical comparison for multiple K-flat resolutions. I wrote the two naturality equations and the three-resolution cancellation explicitly. The ordinary augmentation q tensor 1 is not asserted to be a quasi-isomorphism when P is not K-flat. Quotient maps are retained before localization.

Step 4 uses only the opened tensor and shift definitions: I calculated both coefficients of the differential, including the changed first degree p+1, and checked the inverse sign. This works for negative degrees and shifts, and each direct-sum summand is sent to a single summand, without any boundedness argument. Step 5 uses the actual K-flat definition, the unchanged kernels/images under the invertible differential sign, and the flatness definition to prove shifted K-flatness and the shifted quasi-isomorphism. These are short deductions from the cited definitions and step 4, rather than new lemmas.

Step 6 compares the same shifted resolution on both sides. I checked the degree-i maps are identity on Q^(i+r) tensor B_n, the differentials coincide, and the maps u^(i+r) tensor 1 and 1 tensor rho commute with those identities. Strict-system descent gives naturality on derived morphisms. Step 7 multiplies the explicit signs to verify zero, addition and inverse shifts; the normalized descent lemma is cited for passing these already written model equations to all derived inputs.

I tested the signs at r=0, r=1 with odd p (where the minus sign is necessary), r=-1, and consecutive shifts r and -r. Zero complexes, the empty scheme, the first quotient n=1, characteristic-two coefficient rings, and unbounded direct-sum totals introduce no exceptional case. None of the cited theorem applications requires A to B_n flat, or a complete input or normalized system. In particular a nonflat quotient is permitted, since it is the K-flat representative that computes derived scalar extension.

Against delivery-errors B1-B10: there are no new statements, hollow definitions or alleged leaves; all objects and definitions are supplied by the retained statement, sources use checked tags, TeX is single-escaped, and provenance and genuine searches are recorded. Against C1-C8 I read each cited statement, quote it literally, use no proof-only fact, and declare generic tool uses in `split_report.tool_uses`. No citation relies on a descendant of this item. Against D1-D5 the actual comparison, map formulas and sign calculations remain in this proof; no new clause-restatement node hides them. Against E1-E7 the hypotheses and objects are checked as above, and all transition and shift compatibilities are equations rather than a bare claim of transport. Every step is below 2000 characters, so no long step conceals a separate lemma.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake or build tool was run. The required server-side dry run and direct push are the remaining delivery operations.
