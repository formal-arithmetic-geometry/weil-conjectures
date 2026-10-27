## Files written

- dag/nodes/sec-trace-formula/lem-trf-integral-monoid-free-sharpening-splitting.json: statement item, split into seven elementary steps; no whole-item Mathlib match.
- citations.json: verbatim group-completion definition for the two steps citing it.
- No new nodes and no Mathlib leaves. searches.jsonl retains the actual Q144 search results.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, sharpening, free sharpening, GrothendieckAddGroup and quotient-by-units terminology. No declaration states this item. The unrelated semicontinuity occurrences of “sharpening” do not concern monoids.

## Wanted literature

None. Read ILO Travaux de Gabber, Expose VI 3.7(a), printed p. 75 (PDF p. 81), and Expose VIII 3.1.1--3.1.2, printed p. 98 (PDF p. 104). The source states the exact log-monoid group sequence and chooses its section, then restricts it to the sharp monoid. Our item is explicitly an agent algebraic generalization. Accordingly proof_origin.by is agent: the extra generality and the details are proved directly here, rather than attributed to a theorem in ILO. No SGA source is used.

## Corrections and scope

The mathematical statement is unchanged. The imported text had doubled TeX backslashes in the decoded JSON; these were reduced to single TeX escapes. No statement dispute was found. In particular, the section preserving R does not require a positive basis, saturation, finite generation of R, or torsion-free units. The proof checks its image by the kernel and the unit orbit instead of assuming a chosen group lift already lies in R.

Read the chapter, unit, current main-20261015 ancestor proof, and the item's precise existing blueprint ancestry. This supplies an algebraic supporting fact for the sharp-chart argument, below the fixed unit route. The item is not its unit's key statement, so no unit realization fields change.

## Mathlib and duplicate searches

Seven Q144 searches were run with msearch.py: LeanSearch, two LeanFinder phrasings, two Loogle queries and two grep queries. Their exact queries, actual summaries and verdicts are in the item and searches.jsonl. The prior inherited searches remain present. Read Mathlib/Algebra/GCDMonoid/Basic.lean:1013, the GrothendieckGroup source, and LinearAlgebra/Finsupp/LSum.lean:267--270. The associates equivalence needs trivial units; the number-field hits need arithmetic hypotheses; GrothendieckAddGroup.lift_apply is just the universal map; the Finsupp splitting gives only the basis-lifting ingredient. None is the entire monoid theorem or a one-line specialization of it. The basis formula is written out, so no black-box projectivity theorem is used.

Whole-DAG keyword searches and blueprint_refs.py searches for monoid, sharpening, sharp monoid and free abelian found no duplicate stating the item. Opened the statements of lem-per-integral-monoid-unit-pushout, lem-per-divisible-unit-lattice-extension, lem-trf-fs-chart-free-factorization, lem-trf-fg-torsionfree-group-free, def-per-formal-monoid-extension-data and lem-per-fs-chart-torsion-factorization. They concern a pushout, a divisible subgroup extension, chart factorization, freeness, formal models, and torsion factorization respectively; none replaces this splitting. No new node is being proposed, so the same-tag new-node comparison requirement has no pairs.

## Review by Q144

I checked B through E of delivery-errors.md against the actual statement and all seven steps. The item assumes an injective map R to its group completion and defines the quotient relation explicitly. The only external DAG statement used in its proof is def-trf-fs-log-blowup, whose statement I opened: it defines the group completion by generators [p] and relations [pq]=[p]+[q]. citations.json quotes that sentence verbatim. Its geometric hypotheses are not invoked as a theorem about this arbitrary monoid; the algebraic definition applies to any commutative monoid.

Step 1 verifies that U is a subgroup and proves directly that B embeds in the cosets G/U; it uses only the given quotient relation. Step 2 uses the cited generators-and-relations definition: the additive map h respects the relations, so its extension detects equality in B. This proves injectivity without assuming B is already integral. Step 3 cites the same definition and collects positive and negative generators to prove surjectivity of pi. Step 4 computes the composite with the coset map on r-s, proving both kernel inclusions; it makes no unsupported exactness citation. Step 5 constructs t by the unique integer coordinates of the basis already assumed in the statement. Addition of those coordinates proves additivity and pi t=id. This is a short calculation, not an invocation of an uncited projectivity theorem. Step 6 computes r-t(i(b)) in the kernel and uses the negative of that unit to put t(i(b)) in R; the prior injectivity then proves qj=id. Step 7 checks the target of the second coordinate, additivity, and both composite identities. Every auxiliary claim is explicitly calculated in a few lines, so I kept these as elementary steps rather than introducing nodes restating the item's clauses. No step exceeds 2000 characters and the assembly text is below 3000 characters.

For edge cases I checked rank zero: B injects into the zero group, hence B=0 and R=U, with the stated maps the identity product decomposition. For arbitrary torsion units take R=N x (Z/2Z); B=N and G=Z x (Z/2Z), and any basis lift (1,a) gives t(n)=(n,na), which indeed lies in R for n>=0. For a nonsaturated example R=<2,3> x (Z/2Z), its sharpening has group completion Z and the same argument and inverse formulas work. A general group R gives B=0 and retains all torsion. At no step did I infer torsion-freeness of G from freeness of B^gp, divide inside U, or assume finite generation of R. No new false lemma, dependency cycle, off-route tool, hollow definition, or clause moved to a child is introduced.

No other reader was used, as required by the direct-delivery brief. The maintainer's independent review remains the mathematical acceptance step. Nothing remains unfinished in the split.
