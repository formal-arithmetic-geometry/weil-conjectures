## Worker report

Files written, all in the Q73 item sandbox:

- `dag/nodes/sec-trace-formula/lem-trf-monoid-algebra-domain-fraction.json`: statement, statement dependencies and creation metadata retained; seven proof steps, one proof dependency, completed blueprint place, actual additional searches, and split report.
- `dag/nodes/sec-trace-formula/lem-trf-affine-monoid-unique-sums.json`: statement; Mathlib leaf for the unique-pair property of finitely generated cancellative torsion-free commutative monoids. No proof or proof dependencies.
- `citations.json`: verbatim statement quotations for the two uses of the new leaf.
- `report.md`: this report and signed self-review.

Attachments: none. Searched `WeilConjectures/` in the read-only slopmaster2 source for the exact item/tag, monoid algebra, group algebra, torsion freeness, and the unique-sums declaration. The monomial Cech source concerns particular Laurent exponents; neither it nor the representation-theory occurrences states this whole item. No project declaration matching the new unique-sums assertion was found. No finished proof is claimed from upstream master.

WANTED: none. The PDF and the exact Mathlib declaration sources are present locally. No Stacks tag is asserted for a theorem not located in Stacks.

The item was unsplit, with no proof or Lean audit attachment. Its inherited broad normalization search missed the affine-monoid unique-sums instance. The item is not itself a Mathlib leaf: the searched domain instances do not state the embedding plus common-fraction-field assertion. The statement is mathematically correct and unchanged. In particular no sharpness, saturation, ordering, or characteristic hypothesis has been added.

The PDF's Lemma 3.2.9 does not contain the purported detailed monomial-basis argument: it uses the common dense torus and normality of the saturated realization. I read that proof, together with VIII 3.2.4 and the first paragraph of the proof of 3.2.12, which explicitly uses the embedding into the lattice group algebra and its integrality. Our supporting algebra is therefore openly recorded as an agent proof, not attributed verbatim to ILO. The explicit unique-coefficient and denominator calculations are below that existing chart argument, not a replacement of a unit-level geometric proof.

Unfinished work: none in this one-level split. The only new dependency is already a Mathlib leaf. No Lean files were written and no compiler, Lake command, or local DAG-checking script was run.

## New nodes

`lem-trf-affine-monoid-unique-sums` is the only new node. Its statement introduces an arbitrary finitely generated commutative additive monoid, cancellation, injectivity of multiplication by every positive integer, and the exact quantifiers of the unique-pair assertion. Cancellation, torsion freeness and the unique-pair property are defined in its statement; the additive monoid convention is linked to the existing `def-trf-fine-fan-blowup`, as in the item. Its primary source is the pinned Mathlib file `Algebra/AffineMonoid/UniqueSums.lean`, lines 25–27. `AffineAddMonoid.to_twoUniqueSums` and the parent `TwoUniqueSums.toUniqueSums` (generated from the multiplicative declaration at `Algebra/Group/UniqueProds/Basic.lean`, lines 270–272) supply the statement in one instance-inference line. The class field at lines 222–226 is precisely existence of one pair with uniquely represented sum, not uniqueness of every sum.

The four search kinds were actually run with msearch.py. The hits and log digests are retained in `searches.jsonl`; the new node records the exact query strings with verdicts. LeanFinder and LeanSearch returned the affine instance; Loogle also returned it and its parent; the grep names the file and line. Loogle's remote snapshot presents the torsion condition as `HasUniqueDiv`; I used the pinned source, whose explicit hypothesis is `IsAddTorsionFree`, and read that class's injectivity definition in `Algebra/Group/Defs.lean`, lines 787–792. No nonexistent hypothesis conversion is being assumed.

## Not duplicates

`lem-trf-affine-monoid-unique-sums` vs `lem-trf-fg-torsionfree-group-free`: the existing node gives a finite integer basis of a finitely generated torsion-free abelian group. The new node is about finite subsets of a cancellative monoid and the existence of a uniquely represented sum; neither statement is a one-line specialization of the other. We do not need a basis in this split.

`lem-trf-affine-monoid-unique-sums` vs `lem-trf-toric-realization-finite-type`: the existing node concerns schemes over Q, their components and torus actions, and has no finite-subset unique-sum assertion. Its search record mentions a domain instance but its statement does not provide that instance's general assertion.

`lem-trf-affine-monoid-unique-sums` vs `lem-trf-sharp-monoid-positive-grading`: that node requires a sharp submonoid of a finite-rank lattice and concludes existence of a positive integer functional. Our monoid may have units and need not be sharp; the conclusion is different.

Before creation I searched the entire DAG for the affine declaration, UniqueSums/UniqueProds, unique sums/property/condition, cancellative torsion-free monoids, monoid algebras, and group algebras. The only other group-algebra node located in this search, `lem-exc-rg-group-algebra-functorial-injective-embeddings`, concerns modules and injective resolutions and does not apply here. Whole-blueprint searches for `monoid algebra`, `unique product`, `unique sums`, `torsion-free`, and `cancellative` found no matching blueprint statement. The broader searches were also inspected. No shared Stacks tag is involved.

The new node does not restate the item or one of its ring-theoretic clauses: it contains no ring or field at all. The ring, embedding, domain, and fraction-field conclusions are proved in the item. The elementary denominator and coefficient calculations were kept as proof steps rather than promoted to nodes.

## Review by Q73

I read ILO VIII printed pp.103–104 (PDF pages 109–110), including 3.2.4, Lemma 3.2.9 with its proof, and the first proof paragraph of 3.2.12. I compared the item's hypotheses with the affine chart being used: Q is a finitely generated submonoid of a torsion-free abelian group G, and generates G as a group. A field is nonzero; no assumption on its characteristic occurs in the argument. The source's dense torus becomes the explicit monomial-denominator identities. I also opened the chapter and unit records, and the ancestor's current `blueprint_update`. The latter now uses the contracting-correspondence theorem, rather than the historical nearby-cycle branch. This item's existing historical ancestry and unit binding are retained and honestly identified as historical; no change to the current unit proof or claims about its geometric route is made.

For the new leaf I read the exact instance and its parent class in the pinned Mathlib source, not just the search descriptions. Its hypotheses are precisely finite generation, cancellativity and positive-integer multiplication injectivity. Its conclusion is existence of one uniquely represented sum for each pair of nonempty finite sets. This is exactly what steps 2 and 3 quote; `citations.json` copies its complete statement verbatim for both steps. It is statement-only, has no proof hints in its statement, no extra hidden definitions, and no dependency that could point back to the item.

Step 1 defines the formal finite-sum ring and the coefficient-preserving inclusion explicitly. The inclusion preserves products because inclusion preserves addition of exponents; coefficient recovery proves injectivity. The coefficient of e^0 proves nontriviality. These are definition calculations, not an uncited embedding theorem.

Step 2 checks every hypothesis of the new leaf at Q: addition is commutative and cancellative inside G; nx=ny implies n(x-y)=0 in G and then x=y; finite generation is an item hypothesis. It cites the non-elementary unique-sums theorem rather than silently assuming an order on G. Step 3 cites the same assertion on exactly the two nonempty finite supports. Expanding the product gives one nonzero coefficient because the relevant sum has one contributing ordered pair. This two-line finite-sum calculation is elementary once that cited assertion is supplied. No separate domain lemma is hidden in it.

Step 4 proves Q-Q=G by checking subgroup closure and then using the generation hypothesis. It does not assume that Q contains any negatives. The inverse of e^b is explicitly e^(-b), so the monomial quotient is justified without prior fraction-field identifications.

Step 5 replaces the vague phrase 'clear denominators' by b=sum b_g, and checks each shifted exponent as a_g+sum_(t!=g)b_t. Everything is in Q. The empty support is handled by b=0. Step 6 reduces a putative zero product in k[G] to one in k[Q], using the units just exhibited and the inclusion's injectivity. It invokes only the already established conclusion of step 3, not a stronger uncited torsion-free-group-ring theorem.

Step 7 spells out the induced map between fields using the elementary cross-multiplication definition of fractions. Its injectivity uses step 1. Its surjectivity formula is F/H=(e^d f)/(e^b h), where f=e^bF and h=e^dH; I checked both exponents and the nonzero denominator. Thus this proves equality of the full fraction fields, not just a quotient assertion for monomials. The construction agrees with the given inclusion.

I tested the zero-rank case Q=G={0} (both rings and fields are k), Q=N in G=Z (polynomial and Laurent polynomial rings), Q=<2,3> in G=Z (the nonsaturated cusp monoid), and Q=G=Z (units allowed). For the new leaf, the singleton monoid and pairs of singleton subsets satisfy the quantifiers, and cancellation and torsion freeness are genuinely needed: in a finite nontrivial abelian group, taking both sets to be the whole group violates unique representation. There is no false extension to torsion groups. All steps are shorter than 2000 characters. Every non-elementary fact used is the statement of the cited leaf; the remaining operations are displayed finite-sum, subgroup, or fraction calculations. No statement dispute or source error requiring a mathematical correction was found. The correction made during this review was to avoid presenting ILO's terse torus argument as a detailed monomial proof and to retain the explicit coefficient/denominator work in the item.

The first server dry run requested a definition-node citation in the new leaf. I repaired its `stmt_deps` and statement by explicitly reusing `def-trf-fine-fan-blowup` for precisely its opening additive monoid convention. That citation does not assert that M is a fan, sharp, or saturated; all actual monoid hypotheses remain written in the leaf. I checked that this definition has no dependency path to the item, and refreshed the two verbatim quotes.
