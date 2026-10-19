# Stage-1 report: lem-per-flat-equidimensional-catenary-descent

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-flat-equidimensional-catenary-descent.json`: statement item, now split into eight proof steps. Its hypotheses and conclusions are unchanged; local, equidimensional and the extended ideal notation are expanded, and the topological dimension definition is added to statement dependencies. Mathlib searches did not find the item itself.
- No new nodes and no new Mathlib leaves. All nine theorem dependencies are existing Mathlib leaves; the remaining proof dependencies are definition nodes.
- `citations.json`: 29 entries, copying the complete statement of each cited node verbatim for the relevant proof step.
- `searches.jsonl`: actual Q118 search results. The inherited item's search records are retained. The new records are the exact queries run through msearch.py, with no fabricated searches.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, catenary, equidimensional, and related dimension terminology found no declaration stating the item. The exact upstream master was also inspected as reference only, not evidence of a finished proof.

## WANTED

None. The complete source statement and proof, and its needed input statements, are available locally.

## What needed correction or expansion

The imported statement agrees with Stacks Tag 0AW4, `lemma-flat-under-catenary-equidimensional`, in `literature/stacks-project/more-algebra.tex`. No mathematical statement dispute was found. Its local-ring and equidimensional terminology was made explicit, without adding assumptions. The initially empty proof is replaced with the complete source argument.

I did not create nodes for the two catenarity chain calculations, for the contraction of a prime minimal over an extended ideal, or for quotient/local ring permanence: these are short arguments from the cited statements and definitions, written in the steps. In particular, catenarity of B is not silently used as a theorem about A. The localized flat equality is supplied by the existing Mathlib leaf `lem-weil-pbc-flat-height-formula` (Tag 00ON), not by a new specialization. The proof explicitly reapplies only steps 1-5 to the quotient pair before inferring catenarity of A, so it does not use the item recursively.

## Not duplicates

No new nodes. Searches across the whole DAG for catenary, equidimensional, flat-local dimension and the relevant tags located `lem-weil-pbc-flat-height-formula`, `lem-sc-flat-going-down`, the quotient-flatness leaf, and the existing spectrum and prime-chain leaves, all reused. Blueprint searches for catenary, equidimensional and flat local returned no node stating this item: the smooth-morphism definition and the supported exterior-product node returned by the broader searches are not this ring-theoretic theorem. The blueprint ancestor is `lem-per-artin-gabber-affine-curve`, with the inherited Ratliff/completion ancestry retained. No unit record needs editing since this item is not the unit's key statement.

## What remains unfinished

No proof argument remains to be supplied at this level. This is a stage-1 natural-language split only; no Lean was written or compiled.

## Review by Q118

I read the whole statement and proof of Stacks 0AW4 in more-algebra.tex, the actual flat going-down statement and proof (00HS) and the base-fibre dimension equality (00ON) in algebra.tex, and the catenary definition and its localization discussion there. I also read the current chapter and unit records and the current main-20261015 blueprint proof for the ancestor's Step 3. The item is the generic commutative-algebra descent input beneath the inherited reverse-completion route, so this split does not replace a chapter or unit argument. All theorem inputs are existing Mathlib leaves; definition citations are notions, so no new off-unit tool-use request is needed.

For step 1 I checked the full statements of `lem-weil-pbc-noetherian-local-finite-krull-dimension`, `lem-weil-pbc-spec-irreducible-components-minimal-primes`, `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`, `lem-weil-pbc-spec-topological-krull-dimension-ring`, `lem-weil-pbc-prime-contains-minimal-prime`, and the ring-dimension definition. They give respectively finite chain bounds, components indexed by minimal primes, quotient spectra as closed subspaces, the spectrum/ring dimension dictionary, and the possibility of extending a chain down to a minimal prime. Consequently the common component dimension really is dim B, rather than an unspecified smaller number.

For step 2 I checked `def-exc-excellent-ring`, which explicitly defines catenarity by bounded saturated-chain lengths, and `lem-weil-pbc-localization-dimension-chains-below-prime`, which states the height/local-dimension dictionary. Together with minimal primes and quotient prime correspondence, the written concatenation argument gives dim B_q + dim(B/q) = dim B. Every interval is bounded by dim B, and every chain has a saturated refinement, so the argument uses no hidden existence of a dimension function. This is a direct chain-counting step, not an extra lemma packaged as a new node.

For step 3 the statement of `lem-sc-flat-going-down` gives exactly a smaller prime with prescribed contraction. Minimality over pB then forces equality, proving q contracts to p. I read the complete `lem-weil-pbc-flat-height-formula` statement: its height form applies to any flat map of Noetherian rings and any prime, with no finite-type hypothesis. The height of q/pB is zero by minimality. I inspected the Mathlib source of `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` and the flat-going-down instance at the recorded locations; the existing leaf provides the precise equality used, not merely an inequality.

For step 4 the three spectrum leaves cited really identify all components of the quotient and their dimensions; the minimal-prime existence leaf supplies a minimal prime below any chain. Thus both equidimensionality and the displayed total quotient dimension follow. The local-map assumption makes pB proper, including at p=m_A, so this is never an empty-spectrum calculation.

For step 5 I checked `lem-weil-pbc-flat-module-quotient-flat`: its statement gives flatness of M/JM over R/J, so M=B gives the required quotient ring map, not just an unrelated tensor comparison. Quotients are Noetherian and local by the ideal and unit arguments written in the step. The two applications of the same flat-height leaf are at maximal ideals, giving exactly dim(B/pB)=dim(A/p)+f and dim B=dim A+f with the SAME f=dim(B/m_AB). The finite-dimension leaf ensures subtraction and cancellation are valid ordinary integer calculations.

For step 6 the chain-localization leaf gives dimension zero at each minimal prime, and the component, quotient, and spectrum-dimension leaves give the equidimensionality conclusion for A. None of these citations is only a definition of a theorem the proof needs.

For step 7 the quotient-spectrum statement identifies prime intervals; it follows directly that a quotient of B is catenary, since every inserted prime still contains the quotient ideal. I verified all hypotheses for reapplying the earlier argument to A/p -> B/pB: flatness, locality and Noetherianity from step 5, catenarity from this interval argument, and equidimensionality from step 4. The no-intermediate-prime hypothesis gives exactly the two primes in the indicated quotient-localization interval, hence dimension one by the cited chain-localization statement. There is no invocation of the final catenarity conclusion before it is proved.

For step 8 the finite-dimension leaf bounds every chain and the catenarity definition asks exactly that all saturated chains in each interval have the same length. The displayed telescoping calculation gives that length from its endpoints. No further dimension-function theorem is being used without a node.

I tested the proof on A=B a field, a nonreduced Artinian local ring, the identity on a DVR, and the flat local extension k -> k[t]_(t). In the Artinian case all minimal primes are maximal and dimensions are zero; in the extension case the closed-fibre dimension is one and cancels exactly as required. I also tested a reducible equidimensional local ring, k[x,y]_(x,y)/(xy): different minimal primes are handled separately in the chain argument, without assuming B is a domain. Identity and maximal-prime cases of every formula remain valid. No zero ring with no maximal ideal satisfies the stated unique-maximal-ideal convention.

Finally I checked delivery-errors B-E: every statement citation was opened and copied into citations.json, no source tag stands in place of a missing substantive lemma, no new node duplicates the item or an existing fact, no SGA source is used, and the source hypotheses are preserved. Every proof step is below 2000 characters; the largest is 1109. The longer elementary steps only concatenate or count prime chains or reapply the already established argument, with their hypotheses written out. Only the sandbox has been written; no git command, compiler, Lake or build tool has been run by this worker.
