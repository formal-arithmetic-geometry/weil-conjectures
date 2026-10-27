# Stage-1 delivery: lem-sfb-split-integral-radical-cover (Q74)

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-integral-radical-cover.json: existing statement, unchanged; split in eight steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-split-root-datum.json: statement-only, unsplit; Mathlib has combinatorial RootDatum but no geometric group-scheme root datum or fibre criterion.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-root-datum-isogenies.json: statement-only, unsplit; Mathlib has root-pairing homomorphisms but no integral reductive-group realization/isogeny theorem.
- citations.json: one verbatim statement quote for every node used by every step (18 entries).

Two new nodes, zero new Mathlib leaves. No Lean, compiler, Lake or repository writes.

## Attachments

None. Searched the project WeilConjectures and Sheaf source for the item tag and split-integral/radical-cover notions. No declaration states the item. The field-only central-cover DAG nodes do not supply an integral attachment. Mathlib RootDatum, RootPairing.Hom and RootPairingCat are combinatorial, not reductive group schemes; read Defs.lean:82-119, RootPairingCat.lean:42-66 and Hom.lean:62-95. The logged semantic searches returning those declarations are no-match searches for the geometric statements, not evidence that Mathlib lacks root data.

## WANTED

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, local copy as literature/conrad-reductive-group-schemes.pdf; Example 5.1.7, Proposition 5.1.6, Theorem 6.1.16, Example 6.1.9, Exercise 6.5.2 and Appendix B.1, for the item and the two new nodes. Read the named places online. This file was already WANTED by the input node; I did not download or write literature. The assembly is explicitly marked agent-written. No prohibited source is cited or used.

## Findings and corrections

The item is true as stated. No statement dispute or change was needed. Its empty proof did not justify passing from field covers to integral covers. The proof now constructs the central torus from the torsion-free quotient of the centre character group, then obtains the semisimple quotient from the existing relative quotient theorem and field radical theorem. It constructs the cover using the full weight lattice and realizes the root-compatible finite-index lattice inclusion integrally. The fppf quotient meaning of the second sequence is verified by local lifts and the scheme-theoretic kernel, rather than assumed from surjectivity on field points.

The imported blueprint.from.node is null; tools/blueprint_refs.py ancestor reports None for this chain. I retained this existing provenance, its via chain and from.place. The two new nodes inherit that exact ancestor result and prepend the item to via. Read the current latest blueprint unit and direct-image proof at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. They contain the inherited direct-image route but no separate integral root-datum or cover node. Whole-blueprint searches for radical, integral root, root datum and central isogeny found no equivalent blueprint statement. No unit/chapter record is changed: this item is not its key statement.

One off-unit generic tool is lem-trf-fppf-covering-base-change (already a Mathlib leaf), used solely for the base-change axiom of fppf coverings when checking the quotient after arbitrary scalar extension. It is declared in split_report.tool_uses for transparency; it does not replace the unit's argument.

## Not duplicates

lem-sfb-integral-split-root-datum vs lem-sfb-local-split-root-data-weyl-lifts: the existing theorem assumes a Noetherian local base and supplies root groups and Weyl representatives; it neither applies globally over Z nor gives semisimplicity/simple-connectedness lattice criteria. The new theorem is over Z and its scalar extensions, with fibre lattice criteria and no Weyl representatives.
lem-sfb-integral-split-root-datum vs lem-sfb-reductive-borel-pair-structure: the latter is over an algebraically closed field; it does not supply a common integral datum or the simply-connectedness criterion for every integral geometric fibre.
lem-sfb-integral-split-root-datum vs lem-sfb-simply-connected-character-lattice: the existing field-only statement starts with a simply connected semisimple group and deduces its weight lattice. The new statement also gives the converse and the common integral root datum; it is needed to certify the constructed integral group.
lem-sfb-integral-split-root-datum vs lem-sfb-relative-reductive-centre-weight-kernel: the existing relative theorem assumes constant root-weight support for its explicit formula and supplies the centre, not that constant root datum or the semisimple/simply-connected criteria. It is cited, not recreated.
lem-sfb-integral-root-datum-isogenies vs lem-sfb-root-datum-realization: the existing realization is over an algebraically closed field only, not over Z, and does not assert the integral central isogeny.
lem-sfb-integral-root-datum-isogenies vs lem-sfb-root-datum-isogeny-realization: the existing isogeny theorem is over an algebraically closed field (allowing noncentral Frobenius exponents); the new statement concerns integral exponent-one maps, finite flat kernels over Z, and arbitrary ring base change. The field theorem cannot supply such a map or its finite local freeness over Z.
lem-sfb-integral-root-datum-isogenies vs lem-sfb-reductive-etale-integral-models: the latter produces etale-local identifications with some integral model; it neither realizes a prescribed root datum nor a prescribed character map, and gives no cover of the specified semisimple integral quotient.
lem-sfb-integral-root-datum-isogenies vs lem-sfb-chevalley-integral-root-model: the existing theorem starts with a simply connected field group and constructs an integral model with a Chevalley basis and coordinates. It does not map that model onto a specified integral group with a prescribed lattice map. The new theorem is the general geometric realization theorem, not the item's simply connected cover clause.
lem-sfb-integral-root-datum-isogenies vs lem-sfb-semisimple-multiplicative-universal-cover: the latter is a field-only universal cover, not integral root datum realization. The new node is independent of semisimplicity or the weight-lattice choice, which the item's steps must construct.
lem-sfb-integral-split-root-datum vs lem-sfb-split-integral-radical-cover: the new input identifies integral root data and characterizes fibre properties; it constructs neither the torus quotient nor a cover.
lem-sfb-integral-root-datum-isogenies vs lem-sfb-split-integral-radical-cover: the new input realizes arbitrary root data and lattice maps. It does not construct the item's radical, semisimple quotient, enlarged weight lattice or identify why that realization is simply connected. Steps 2-5 make those arguments.

No Stacks tag duplicates occur for the new nodes: the relative reductive-group results do not have Stacks tags. Existing same-place candidates were found by searching source fields for 5.1.6, 5.1.7, 6.1.16, and the concepts above. No new elementary lattice lemma or centre/quotient node was created.

## Review by Q74

I read delivery-errors B-E whole, the stage-1 brief, the three-level route rule, GOAL, the chapter/unit records and the latest blueprint direct-image proof. For the item I read Conrad Example 5.1.7 (centre and weight lattice), the statement and reduction of Theorem 6.1.16, Example 6.1.9 (centrality exactly at root exponents one), Definition 3.3.9 (finite flat surjection, which is stronger than mere field-point isogeny), and Exercise 6.5.2(i). For the first new node I read Definition 5.1.1, Example 5.1.4 (why Spec Z admits a split triple), Proposition 5.1.6, Example 5.1.7 and the opening of Exercise 6.5.2. For the second I read Theorem 6.1.16, Example 6.1.9 and the centre/torus kernel discussion in Corollary 3.3.6 and Appendix B.1. These are genuine general structural inputs; they are not the item's two existence clauses with new names.

Step 1 uses the new integral datum to furnish the constant-support hypothesis of the existing relative centre statement. I opened that centre node and verified it explicitly concludes the scheme-theoretic formula D(M/ZPhi) and arbitrary base change, not just an equality on geometric points. Z is Noetherian and nonzero, and the given torus is fibrewise maximal, so the hypotheses apply.

Step 2 uses the finitely generated abelian-group structure theorem for finiteness of torsion and freeness of the quotient. I opened its actual invariant-factor statement, which gives these facts. The relative diagonalizable duality node explicitly treats arbitrary nonzero base rings, closed immersions from character surjections and their kernels. The largest-subtorus assertion is proved here in two lines: a character map into a free group kills torsion, so factors through the torsion-free quotient. No general largest-subtorus lemma is hidden in a new node.

Step 3 uses the relative central-multiplicative quotient exactly as stated: represented reductive quotient, fppf torsor, maximal-torus image, and arbitrary base change. The subgroup is the closed central split torus just constructed, so it is multiplicative type. The diagonalizable quotient gives U/T=D(N); the existing subgroup-of-finite-free-lattice leaf gives freeness of N. The field radical node is applied only over algebraically closed residue fields, never over Z. I read Milne Corollary 17.62(b)-(d), printed pp.372-373, in the local PDF (extracts in this sandbox), confirming that the largest central torus is the radical and the quotient is semisimple. This avoids mistaking a field theorem for an integral statement.

Step 4 uses the new integral datum for Q and the existing root-datum-lattice-embedding theorem. I checked that its j is an inclusion into P plus the central complement and has finite cokernel. Semisimplicity gives full rational root span here, so its complement is zero and j is exactly X into P. Thus the finite-index claim is supplied by that theorem, not inferred from an unproved rank comparison.

Step 5 writes out the root-datum check on P: the pairing is integral, each reflection subtracts an integer multiple of a root in X, and the rational reflection group and reduced root set have not changed. The existence clause of the new integral realization theorem gives S. The root-span and full-weight-lattice clauses of the first new node then give semisimplicity and fibrewise simple connectedness. The proof does not assume the converse of the existing field-only simply-connected-character-lattice node.

Step 6 checks both root and coroot compatibilities for X into P before using the new integral isogeny theorem. Its statement supplies finiteness, faithful flatness, finite presentation, centrality and the exact diagonalizable kernel. Finite local freeness over Z is then immediate from the explicit group-algebra basis indexed by the finite group P/X, using the ring-diagonalizable definition. This remains true at primes dividing the index.

Step 7 cites the arbitrary-base-change clauses of both relative structural results, not their proofs. The only additional theorem is the cited fppf-covering base-change leaf. I read Stacks Tag 021O, topologies.tex lemma-fppf(3), matching its statement. After the pulled-back cover gives a lift, the equality of two cosets is checked by the explicit element s1 inverse times s2 in the scheme kernel. This establishes the second quotient as a sheaf, without requiring surjectivity on B-points. Step 8 uses the base-change/geometric-fibre clause of the first new node; freeness of B[P/X] uses the same basis. The empty base is treated separately because the new datum theorem discusses nonzero rings.

I tested all new statements with root rank zero, pure tori, simply connected and adjoint rank-one groups. For H=Gm, L=0, C=M, T=H, Q=S=1. For H=SL2, C=0 and P=X, so the new map is the identity. For H=PGL2, X is the root lattice, P/X=Z/2, and the cover kernel is mu2 over Z; it is not reduced in characteristic 2 but is finite free of rank 2. This checks the potentially dangerous bad-characteristic case against the exact wording of the new isogeny input. Product root systems and zero lattices cause no exception. No statement uses the connected component of the centre in place of its largest torus.

I inspected each cited node statement, checked the graph does not already depend back on this item through these inputs, and generated the citation quotes directly from the statements read. Both new nodes have no proof, no proof dependencies and no proof sketch in their statements. Each introduces all its objects and has definition dependencies or inline definitions. Logged searches include LeanFinder, LeanSearch, Loogle and grep with second semantic phrasings. Actual hits were read; none is a geometric group-scheme match, and no unavailable service was described as a no-match. Every proof step is below 1000 characters, so no long step hides an extracted lemma. I corrected the cover-source reference to Tag 021O after reading the actual cited node and source.

## Unfinished work

No gap in the item's assembly remains. The two new integral structural theorem nodes are deliberately statement-only obligations for later stage-1 workers. No claim of a completed Lean proof is made.
