# Worker report: lem-pur-conormal-graded-algebra

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-conormal-graded-algebra.json`: statement, split; ten proof steps, no new nodes. Mathlib does not state all its clauses.
- `citations.json`: 40 entries after second-reading repair, one verbatim statement quotation for each retained step/node citation.
- `report.md`: this report. `searches.jsonl` was written by the required search command; `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed: this item is a child supplying the algebra used by the normal-cone definition, not the unit's key node.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item tag and the conormal/associated-graded notions. The conormal occurrence is documentation in `AlgebraicGeometry/DeformationToNormalCone.lean:47`. That module and `AlgebraicGeometry/Morphisms/RegularImmersion.lean` explicitly describe a normal-cone datum not tied to the conormal sheaf; neither states the graded-algebra construction. Its data-only API is not an attachment. No Mathlib result is claimed as a project attachment.

## WANTED

None. The shared checkout lacks the untracked Stacks and blueprint source directories. I read the already available Stacks source mirror at `/home/ubuntu/weil-launcher-nt/literature/stacks-project/`, without downloading or modifying it. The node retains the project's canonical `literature/stacks-project/` source paths and records this mirror in `proof_origin`. The chapter, unit, parent node and imported blueprint statements were read from the shared DAG records.

## Audit and corrections

The imported statement is mathematically correct. I kept every hypothesis and conclusion and added only references defining a graded sheaf algebra, quasi-coherent algebra and ordinary module stalks. No STATEMENT-DISPUTED correction was needed. The initial item had no proof: in particular it did not justify moving the ideal-power quotients from X to Z, or identify the symmetric comparison on stalks. The split now constructs those maps rather than appealing to the source's “Details omitted.”

There is no Noetherian assumption before the final coherence assertion. In particular, the existing coherent closed-immersion equivalence would have been too narrow here; I use `lem-weil-pbc-closed-immersion-pushforward-annihilated`, whose statement applies to arbitrary schemes. I use the separate fully faithful pushforward node only for the uniqueness of the pieces, rather than attributing that conclusion to a node that states just essential-image membership.

The affine sections of a sheaf direct sum are justified by the affine tilde functor's colimit clause and unit, not by assuming that arbitrary open-section functors commute with infinite sums. Stalks use the separate stalk-coproduct theorem. Algebraic localization is at an arbitrary prime, not just at one element: the power identity and the quotient/scalar comparisons are written with fractions. The symmetric base-change node states arbitrary scalar base change, so it applies to this localization even though its displayed special case mentions principal localization.

The five new search records are exactly the queries run through `msearch.py` for this item, including the second LeanFinder phrasing. LeanSearch returned HTTP 500 and is recorded as unavailable. Loogle returned no conormal declaration. LeanFinder returned closed-subscheme/ideal-sheaf constructions; I read `Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean`, including the quotient gluing and localization API. The source grep returned `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean:237`, the Proj sheafed-space construction. None states the item. Existing Mathlib leaves are cited under their existing IDs; no substitute leaves were created.

## Not duplicates

No new node was created. Whole-DAG searches used conormal, the conormal tags, associated graded, affine module/tilde, closed-immersion annihilation, symmetric algebra and direct sums. `tools/blueprint_refs.py` searches included `conormal`, `conormal algebra`, `associated module`, `symmetric algebra` and `quasi-coherent`; the ancestor command returned `def-pur-normal-bundle`. The normal-cone definition is the user of this algebra, not a theorem proving it; the blueprint's diagonal differential definition is a different statement. Existing general statements were reused throughout. The item's `same_as` remains empty, and its already precise `from.place` is retained.

## Review by N6

I read divisors.tex at definition-conormal-sheaf, equation-conormal-in-degree-n, equation-conormal-algebra-quotient and lemma-affine-conormal-sheaf (Tags 0630–0633, lines 4297–4390 in the mirror). The source first constructs the graded algebra on X, then uses annihilation to obtain the algebra on Z; this is exactly the split's route. I read Morphisms lemma-i-star-equivalence (01QY), Modules lemma-i-star-equivalence (08KS), Schemes lemma-widetilde-constructions/lemma-widetilde-pullback and the affine quasi-coherent cokernel/colimit results (01I8, 01I9, 01IC, 01ID). For the symmetric comparison I read Modules section-symmetric-exterior and lemma-local-tensor-algebra (01CF/01CG), and Algebra lemma-tensor-algebra-localization (0C6F). For coherence I read coherent.tex lemma-coherent-Noetherian (01XZ), properties.tex lemma-finite-type-module (01PB), and algebra.tex lemma-Noetherian-basic (00IK). There are no new-node statements or sources to review.

For step 1 I opened the powers definition, quasi-coherent cokernel-and-image node and affine tilde adjunction node: they give exactly the powers, affine quotient surjectivity/kernel, and reconstruction used. Step 2 uses the associated-graded ring theorem for its bilinear quotient operations and laws, the affine tensor theorem for the tensor comparison, and the tilde adjunction to realize maps of modules. The two definition nodes there describe graded operations and sheaf morphisms. The overlap check is written on affine refinements of the intersection, so no separatedness assumption is being smuggled in. The lift-change error is explicitly in the next ideal power.

Step 3 is elementary: multiply a local representative by the defining ideal and take its zero quotient class. In step 4 the annihilation node gives precisely the pullback unit isomorphism and quasi-coherence after steps 1 and 3 have established its hypotheses; the separate fully faithful node gives the counit. The affine pullback node states the tensor identification with its generator formula, and the tilde adjunction identifies the resulting sheaf. I checked the inverse m to m tensor 1, including independence of the lift of a coefficient modulo J. No coherence hypothesis is used.

Step 5 defines pullback multiplication on pure tensors, checks balancing, and extends by sheafification as the cited tensor definition permits. The coproduct theorem is on schemes and has no finiteness hypothesis. The affine tilde adjunction's clause (4) preserves all small colimits, so it applies to the countable degree diagram. Step 6 uses the affine conormal statement for quasi-coherence of i^*I, not for an unasserted algebra theorem. The pullback formula and tilde adjunction support the actual quotient-induced arrow, and its tensor inverse is proved explicitly, including the J² relation.

For step 7 the structure-stalk node is used only in its first clause, which assumes no domain condition. The tilde-stalk node gives the precise module localizations. The localization-exactness node applies to the short exact sequences of ordinary modules; the fraction and finite-product arguments establish the remaining identifications. The stalk-direct-sums statement explicitly concerns module sheaf coproducts, exactly as needed. The stalk definition justifies the local representative formula and cofinal affine neighbourhoods. I checked multiplication on homogeneous fractions, not just a module isomorphism.

For step 8 I checked the symmetric sheaf theorem's universal property and its affine comparison; the core theorem is the universal property of the exact explicitly constructed symmetric sheaf named in the item. The algebraic universal-property node also states the homogeneous commutator presentation used to check the grading. For step 9 I checked that the base-change statement is general for R to S and names its generator map. The tensor-to-fractions isomorphism is written with its inverse; together with the tilde-stalk theorem it identifies both the source stalk and the actual image of a degree-one germ.

For step 10 the Noetherian submodule theorem is applied to J^n inside the finite module R. The affine finite-type criterion states the cover-to-finite-type conclusion used; the coherence theorem applies because the quotient-ring argument first proves Z locally Noetherian. I checked that reducing coefficients modulo J is legitimate and that this proves coherence of each piece only.

I tested J=0 (only degree zero survives), J=R (Z is empty), the empty scheme, degrees zero in either factor, and R=k[epsilon]/(epsilon²), J=(epsilon). In the latter case the comparison is k[t] to k[t]/(t²), which confirms that no isomorphism assertion for the symmetric map has been introduced. Arbitrary characteristics, infinitely generated ideals and schemes without quasi-compactness or separatedness are allowed in steps 1–9. The final argument uses only a cover by Noetherian affine rings. Every cited statement was opened, and every quotation was checked as a literal substring; no proof of a cited node is being mined for an unstated conclusion. The generic off-unit tools are individually declared in `split_report.tool_uses` because the conventions unit contains no replacement for those module/algebra facts.

## Unfinished work

No mathematical step is left open in this one-level split. Existing dependencies remain their owners' work. The independent second reader must review and deliver; this worker runs only `deliver.py --no-push` and leaves the sandbox for that handoff.

## Second reading by N6

I independently read the source mirror `divisors.tex`, Tags 0630–0633 (definition-conormal-sheaf, equations conormal-in-degree-n and conormal-algebra-quotient, and lemma-affine-conormal-sheaf), plus coherent.tex Tag 01XZ and the cited affine finiteness results. The closed-immersion specialization in the item retains all hypotheses needed by those source statements; the ideal powers, quotient pieces, degree-zero and degree-one identifications, affine sections, stalk formulas, symmetric comparison map, and locally Noetherian coherence clause agree clause by clause. I checked the zero ideal, unit ideal (empty closed subscheme), empty scheme, degree zero, and the dual-number example $R=k[\epsilon]/(\epsilon^2)$ with $J=(\epsilon)$.

Step 1: checked against the powers definition, quasi-coherent cokernel/image statement, and affine tilde adjunction; the sheaf-cokernel and affine quotient argument uses exactly their hypotheses.
Step 2: checked against associated-graded multiplication and graded-sheaf/module definitions; repaired the overlap argument. Its original affine-map construction did not establish that restriction to an arbitrary affine subchart retained the product formula. The repaired step defines products by local quotient lifts, compares any two choices on affine refinements using the quotient kernels, and glues the resulting sections by the sheaf axiom.
Step 3: checked directly from the powers definition; multiplication by an ideal element lands in the next power, including degree zero, so the elementary mark is appropriate.
Step 4: checked the annihilation descent theorem, fully faithful closed pushforward, affine pullback sections, and tilde adjunction; quasi-coherence and the canonical pushforward isomorphism use the stated annihilation hypothesis.
Step 5: checked tensor balancing, graded-sheaf operations, coproduct quasi-coherence, and affine tilde colimits; no arbitrary-open section/direct-sum interchange is assumed.
Step 6: checked affine conormal sections, affine pullback, and tilde adjunction; the displayed inverse respects the $J^2$ relation and proves the degree-one identification.
Step 7: checked the structure-sheaf stalk, tilde-stalk localization, localization exactness, stalk coproducts, module-stalk definition, and associated-graded multiplication; the fraction formulas cover arbitrary primes.
Step 8: checked both symmetric-algebra universal-property statements and the explicit sheaf construction; the map is determined on degree-one generators and its homogeneous grading is justified.
Step 9: checked symmetric-algebra base change, affine tilde/stalk localization, and the explicit fraction inverse; the scalar base-change theorem is stated for arbitrary ring maps, so localization is covered.
Step 10: checked the locally Noetherian definition, Noetherian submodule finiteness, affine finite-type criterion, and coherence criterion; only the individual pieces are claimed coherent.

There are no new nodes to audit. I repaired step 2 as described above, removed its two now-unused affine tensor/adjunction citations and the unused tensor tool-use declaration, synchronized proof_deps and citations.json, and added this independent second-reading record plus an independently phrased LeanFinder search. The statement is unchanged. The search returned Ideal.Cotangent and related degree-one ring constructions. I inspected Mathlib/RingTheory/Ideal/Cotangent.lean:35–180: these are not the sheaf graded-algebra assertion, so no Mathlib leaf was gained. All 40 retained citation quotations were rechecked against the current shared node statements, and proof_deps is exactly the union of step uses.
