# Q32 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-bialgebra-top-degree-exterior.json`: item split into five steps; existing statement retained exactly; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-borel-graded-bialgebra-monomial-basis.json`: one new statement-only prerequisite; no Mathlib match. This is the general structure theorem, with no equality or top-degree assumption.
- `citations.json`: verbatim statement quotations for every step citation.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the exact blueprint tag, bialgebra/graded Hopf notions, and exterior criterion. The ordinary Hopf-algebra files concern coordinate-ring quotients, Frobenius and Cartier; none states this signed graded algebra theorem. The independent primitive-product node proves nonvanishing only, not generation or characteristic-two square-zero.

## WANTED

WANTED: A. Borel, Sur la cohomologie des espaces fibres principaux et des espaces homogenes de groupes de Lie compacts, Annals of Mathematics 57 (1953), the connected graded commutative Hopf-algebra structure theorem, for lem-sfb-borel-graded-bialgebra-monomial-basis. Milne's obtained notes explicitly quote the needed theorem, and that quotation is the source of the new statement; Borel's original proof has not been read and no proof is assigned to the new node.

## Findings

The item is correct with its explicit coassociative signed algebra-map and counit hypotheses. Milne I Lemma 12.2, printed p.55 (read with pdftotext, including the preceding formula (3)), is the source for the item and the new prerequisite. Milne's first proof sentence invokes Borel rather than proving it. The new node makes precise the homogeneous generators with only anticommutativity and pure-power nilpotence relations used there. All those generators are positive-degree and have finite heights because the algebra is connected and finite-dimensional. No source statement or project target was changed. No Stacks tag is claimed for Borel's theorem; Stacks algebra.tex Tag 00DM, label section-tensor-algebra, was read for the exterior construction and basis used at the end.

Read the chapter/unit records and the latest blueprint unit and direct-images proof. The inherited ancestor command reports blueprint.from.node=None; retained that inherited root and the full via chain, adding this item to the new child's via. Whole-DAG concept searches and blueprint_refs searches Hopf, exterior, truncated polynomial, Borel 1953, and monomial basis found no structure theorem to reuse. The new prerequisite belongs below the existing coherent exterior base-change chain; there is no change of chapter or unit route. No unit realization fields are due because this auxiliary item is not the unit statement.

Mathlib searches ran exclusively through msearch.py and are recorded literally in searches.jsonl and the nodes. Both Borel/monogenic and bounded-H1 phrasings were tried. Read Mathlib/RingTheory/GradedAlgebra/FiniteType.lean:32 and :45: homogeneous finite generation provides neither independence nor pure-power relations. Ordinary Hopf tensor products do not solve the signed graded theorem. Exterior-algebra hits concern the already defined exterior algebra, not the comparison with H. Loogle Bialgebra/GradedAlgebra and HopfAlgebra/Basis returned no hits; restricted greps gave only unrelated etale monogenic results or none. Existing exterior leaves were reused rather than created again.

## Not duplicates

lem-sfb-borel-graded-bialgebra-monomial-basis vs lem-sfb-bounded-bialgebra-top-degree-exterior: same Milne source but different assertions; the new node supplies a general truncated-monomial basis without a top-degree equality, whereas the item uses the equality to force exactly degree-one square-zero generators and a canonical exterior isomorphism.
lem-sfb-borel-graded-bialgebra-monomial-basis vs lem-sfb-graded-primitive-product: primitive-product only says independent primitive degree-one elements have nonzero product, with no perfectness or commutativity required; it gives neither a basis for the whole algebra nor nilpotent homogeneous generators.
lem-sfb-borel-graded-bialgebra-monomial-basis vs lem-sfb-coherent-group-bialgebra: the latter constructs geometric coherent-cohomology bialgebra data; it gives no algebraic generator decomposition.
lem-sfb-borel-graded-bialgebra-monomial-basis vs lem-sfb-abelian-coherent-exterior-base-change: the latter is a relative geometric theorem, including arbitrary base change and local freeness, not a general algebra structure theorem.

## Unfinished

None for this one-level split. The new structure theorem remains statement-only for its own future worker.

## Review by Q32

I read delivery-errors B through E whole and checked the actual node statements and source, not merely their titles. For the item and the new Borel node I read Milne I Lemma 12.2 p.55 and its proof. I checked the new node has no hidden equality hypothesis: it applies as well to exterior generators in higher odd degrees and truncated polynomial generators of larger height. Those examples explain why it is a real structural input rather than a renamed clause of this item. In characteristic 2, k[t]/(t^4) with t primitive of degree 1 is allowed by the new node but fails the item's bound g=1; this distinguishes the assertions. Products of such factors are covered. In characteristic zero only exterior factors can remain finite-dimensional; the new weaker formulation does not incorrectly demand characteristic-p polynomial factors there.

Step 1 quotes exactly the new node's basis and pure-power conclusions. I verified perfectness, finite dimension, H0=k with nonzero unit, signed graded commutativity, degree-preserving coassociative unital algebra coproduct and both counit identities are all present in the item and repeated in the prerequisite. No ungraded tensor multiplication, cocommutativity, or antipode assumption is silently imported.

Step 2 quotes the same node's homogeneous basis. Looking degree by degree in a homogeneous basis proves that exactly g generators have degree 1. The maximal allowed monomial has degree D=sum (N_j-1)d_j and is nonzero, hence D<=g. Every term is positive, and the g degree-one generators already contribute g; thus no higher generators exist and every height is two. This is explicit arithmetic, not a separate lemma. It also handles g=0 and r=0, with the empty basis monomial 1.

Step 3 has no black-box input: I expanded the square of an arbitrary linear combination and paired its mixed terms. Cancellation uses xy+yx=0 rather than division by two. Thus the square-zero clause holds also in characteristic two; graded commutativity alone would not have sufficed there.

For Step 4 I opened lem-trf-exterior-power-universal-property and read its full statement; it supplies precisely the unique extension of each alternating multilinear product map. To verify alternation for repeated, nonadjacent entries, move one entry across its neighbors with the graded sign and then use its square-zero. Degree zero is the stipulated scalar unit map. This existing Mathlib leaf is a general tool, not a different geometric route.

For Step 5 I opened lem-weil-pbc-exterior-power-free-basis and def-weil-pbc-exterior-algebra. The former supplies the increasing-wedge basis over every commutative ring, hence over k, including degrees 0 and >g; its hypothesis of a free module is furnished by the explicit basis of H1. I also read Stacks algebra.tex Tag 00DM at the exterior quotient and free-basis paragraphs, and Mathlib ExteriorPower/Basic.lean:206-236 for the universal property leaf. The latter definition supplies concatenation and the spanning wedges, so multiplication compatibility follows on these spanning generators. Sending corresponding bases to bases gives bijectivity without an uncited rank theorem. This proves the canonical product map, not just an abstract algebra isomorphism.

All citation quotes in citations.json are copied verbatim from the statements actually used. No new node is elementary or a clause of the item; the sole new node is exactly the non-elementary Borel input that Milne quotes. Every proof step is below 2000 characters, all uses are in proof_deps, and the proof does not cite a source as a substitute for a lemma. The source/definition cross-check led me to reuse the existing universal-property and free-basis leaves instead of adding redundant nodes. I retained the statement, citations, existing Mathlib searches, inherited blueprint references and metadata. No Lean, compiler, repository write, SGA source, or agent delegation was used.
