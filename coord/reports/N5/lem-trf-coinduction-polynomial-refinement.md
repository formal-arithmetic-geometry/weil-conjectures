# Worker report: lem-trf-coinduction-polynomial-refinement

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coinduction-polynomial-refinement.json`: item, split into six proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-cartier-quotient-derived-dual.json`: one new statement-only node, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node citation.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, coinduction, derived coinduction, Cartier duality and polynomial/RHom terminology found no declaration stating both functor isomorphisms. Existing representation coinduction and sheaf-coinduction results have different categories. The existing Koszul immersion and self-Ext/Tor files likewise do not state this item. No Lean was written or compiled.

## Literature

No WANTED documents. I read `literature/stacks-project/dualizing.tex`, Tag 0BZH (`lemma-compute-for-effective-Cartier-algebraic`), including its proof, and Tag 0BZJ (`lemma-well-defined`), including both paragraphs of its proof. For composition and the action I read `lemma-right-adjoint`, Tag 0C0F (`lemma-composition-right-adjoints`), and Tag 0A71 (`lemma-RHom-ext`). The new node isolates the object computation in the proof of 0BZH, not its whole tensor-functor conclusion. I checked the labels against `literature/stacks-project/tags/tags` and also consulted the official 0BZH and 0BZJ pages.

I read the chapter and unit records, the item's ancestry and the current main-20261015 local-term-locality proof. This item is an algebraic auxiliary below the polynomial-duality construction, not the unit's key statement. Its existing ancestor/via chain is retained; the new node adds the item to that chain. No unit or chapter record is changed.

## Corrections and scope

The item had no proof and no Lean attachment. Its statement is correct as written; no STATEMENT-DISPUTED repair is needed. Although 0BZJ is presented for finite-type Noetherian maps, its evaluation-variable argument uses neither hypothesis: 0BZH itself and the coinduction adjunction work for arbitrary commutative rings and unbounded complexes. The proof below verifies precisely those weaker input requirements, without changing the item. I corrected an initially mistyped source tag for composition to 0C0F after checking the tag index.

The previous five Mathlib searches stored in the live item were read and retained. They returned complex shifts, ordinary polynomials, and group homological algebra, not the action-preserving derived comparison. For the new node I ran LeanFinder, LeanSearch, Loogle and grep with the mandated msearch command and read the returned hits. A second semantic formulation also found no derived coinduction dual. All newly recorded query texts come from `searches.jsonl`; ordinary cotangent and Picard-module lemmas are not exact matches for an isomorphism in D(B).

## Not duplicates

lem-trf-cartier-quotient-derived-dual vs def-trf-derived-coinduction: the definition constructs coinduction and its quotient action; it does not compute C_B(S) for an invertible kernel.

lem-trf-cartier-quotient-derived-dual vs lem-trf-algebraic-shriek-derived-hom-adjunction: that statement gives a currying isomorphism and double-dual evaluation compatibility, not the Cartier-quotient dual object.

lem-trf-cartier-quotient-derived-dual vs lem-trf-coinduction-shift-scalar-model: that statement gives Hom shift signs and scalar-action compatibility for the still unspecified object V; it does not identify V with a dual conormal line.

lem-trf-cartier-quotient-derived-dual vs lem-trf-coinduction-tensor-comparison-model: that statement constructs the tensor-to-coinduction map and its representatives, expressly without asserting invertibility; it does not compute D_B for an invertible ideal quotient.

lem-trf-cartier-quotient-derived-dual vs lem-trf-coinduction-total-hom-model: that statement gives chain-level currying, K-injectivity preservation and scalar restriction, not the Cartier dual-object calculation.

lem-trf-cartier-quotient-derived-dual vs lem-trf-derived-coinduction-adjunction: that statement establishes the adjunction and conservative scalar restriction, not an identification of C_B(S) with the inverse conormal line. The split cites this existing adjunction separately.

lem-trf-cartier-quotient-derived-dual vs lem-trf-coinduction-polynomial-refinement: the new statement computes one derived-dual object for an arbitrary invertible kernel ideal; the item proves natural functor comparisons for evaluation polynomials by perfect evaluation, composition and induction.

lem-trf-cartier-quotient-derived-dual vs lem-trf-lci-koszul-duality-determinant-comparison: that node concerns scheme embeddings into affine space, top differential twists, and determinant-normalized chart comparisons. It does not state the ordinary-module quotient dual for arbitrary commutative S and an invertible ideal, including non-Noetherian rings. Moreover its dependency chain reaches the item, so it cannot be used as an input here.

lem-trf-cartier-quotient-derived-dual vs lem-trf-algebraic-shriek-calculus: that node constructs polynomial shriek models for finite-type Noetherian ring maps and already depends on the item; it does not supply this invertible-kernel object computation.

lem-trf-cartier-quotient-derived-dual vs lem-trf-relative-duality-polynomial-chart: that node concerns a relative dualizing pair for a flat locally finitely presented scheme morphism with locally Noetherian base, and its normalized polynomial charts. It is above the algebraic comparison and does not state the new arbitrary-ring derived-dual assertion.

lem-trf-cartier-quotient-derived-dual vs lem-trf-perfect-algebra-coinduction-tensor: that existing node gives the natural tensor formula with D_B=C_B(S), but does not identify D_B with the dual conormal line. The split reuses it and isolates only the missing computation.

The whole-DAG tag and concept searches and `blueprint_refs.py search` for coinduction, 0BZH, Cartier, derived dual and invertible ideal found no blueprint assertion stating the new lemma. The returned Cartier nodes concern blowups, torsion sheaves, or schemes, not this module derived object. No duplicate blueprint node is listed in same_as.

## Review by N5

I checked the node files against delivery-errors B--E with the cited statements open. The new node introduces S, I, B and N, defines the invertible-module hypothesis inline as finite projectivity and local rank one, and specifies the coinduction action through its existing definition node. It has a statement only and no proof or proof dependencies. Its mathematical source is the derived-dual calculation in 0BZH, which is a substantive input, smaller than either functor comparison. The other ingredients already exist and are cited instead of recreated.

For step 1, the definition of a perfect ring complex says exactly that a bounded finite projective complex represents the object. I wrote the difference-of-powers identity giving the evaluation kernel and the coefficient argument giving injectivity. These furnish the two-term free resolution over every coefficient ring, including rings with zero divisors. This algebra is elementary, so it did not become a new node.

For step 2, the new Cartier statement gives an isomorphism in D(T), retaining the T-action; I checked that the ideal (y-g) is free by step 1 and hence meets its projectivity and rank-one hypotheses. Evaluation on its chosen generator trivializes the conormal dual. The statement of perfect-algebra-coinduction-tensor expressly gives a natural comparison in D(T), for every unbounded input, once T is perfect over S. This is exactly the perfection proved in step 1. The second-factor tensor-functor statement supplies functoriality under an isomorphism of the second factor. The elementary signed total-tensor identification is written explicitly; it gives [-1], not [+1]. No isomorphism has been lifted merely from an underlying S-object.

For step 3, derived-coinduction-adjunction states the unbounded right adjunction to scalar restriction, with no ring-map finiteness assumption. Right-adjoint-composition states the comparison of a composite's right adjoint with the composite right adjoints. Those are precisely the statements used. The remaining shift and identity identifications are written directly on Hom into a shifted K-injective; they preserve the quotient action. They are not attributed to the adjunction node as extra clauses of its statement.

For step 4, the induction is for all objects of D(Q_i), so it can be applied to the derived extension produced at the successor. Both base and successor are explicit. K-flat-extension-of-scalars states that arbitrary ring extension preserves ordinary-module K-flatness; second-factor tensor-functor states the computation on K-flat representatives and the canonical comparisons for different representatives. These statements justify computing the nested tensors, and I wrote mutually inverse balanced cochain maps. Neither node is being cited as an unproved tensor-associativity slogan. The result is natural because the displayed maps commute with representative maps and the cited construction is independent of resolution.

For step 5, the same two cited statements apply to R→Q and Q→P. A K-flat R-representative remains K-flat over Q after extension; the balanced maps then compute the iterated tensor. No K-flatness after forgetting along a nonflat map is assumed. In particular P need not be flat over R. Step 6 is the explicit assembly of the already proved natural comparisons and their shift cancellation, in D(A). It adds no external result.

I tested m=0 (identity maps), m=1 over Z and over Z/4 (the free two-term resolution and cohomology in degree 1), arbitrary zero divisors in P, the zero ring, I=S in the new node (zero quotient), and P=R/(a) for a nonflat structural map. The proof never divides by a leading coefficient, never supposes ψ surjective, and never truncates an unbounded input. The ordered generator choices are retained, and no choice-independent orientation is claimed.

I read every citation statement and recorded it verbatim in citations.json, including its hypotheses, so none takes a fact solely from another node's proof. Every step is below 2000 characters. The only new node is a genuine derived-object input, not an elementary calculation or a copied clause of the item. The proof uses no SGA source. The two off-unit K-flat/tensor inputs are declared as generic tools in split_report.tool_uses; the adjoint-composition input is already a Mathlib leaf. All other statement inputs are in the item's unit.

## Unfinished work

Only the new derived-dual node remains unsplit, as required for a one-level split. The item's two functor assertions are fully assembled. The first dry run stopped at the duplicate-report gate: six other nodes share the auxiliary Tag 0A71. I read all six statements; none identifies the Cartier derived dual, and their pairwise differences are recorded above. The full dry run is repeated after this report repair.
