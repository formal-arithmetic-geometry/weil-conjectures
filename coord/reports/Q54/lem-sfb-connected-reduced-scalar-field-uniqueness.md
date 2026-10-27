# Q54 stage-1 report

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-connected-reduced-scalar-field-uniqueness.json`: item, statement retained, split into eight steps; no project Lean attachment or Mathlib match found.
- `lem-sfb-reduced-integral-polynomial-generalized-inverse.json`: statement, unsplit; no Mathlib match found for the reduced-algebra polynomial generalized inverse.
- `lem-sfb-relatively-closed-constants-units-fg.json`: statement, unsplit; Stacks 04L7(1), no Mathlib match found.
- `lem-sfb-subfield-units-quotient-finite.json`: statement, unsplit; the ring-theoretic unit-quotient argument of Stacks 04MK, no Mathlib match found.
- `lem-sfb-integral-element-tower-descent.json`: statement, Mathlib leaf; `isIntegral_trans`, `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:479–480`, with the source read at 470–500.

`citations.json` contains one verbatim statement quotation per cited node per proof step. `searches.jsonl` retains the actual launcher search log; the node search records use those exact tool/query pairs. No Lean was written or compiled. This continues the existing sandbox and reuses its searches.

## Attachments

None. Searching the live read clone's `lean/WeilConjectures/` for the item id, blueprint tag and scalar-field/integral-closure notions found no declaration stating the item. The unrelated unique-base-field preimages in matrix-cocycle descent do not state scheme scalar-field uniqueness. Mathlib's domain inverse results do not apply to a connected reduced scheme's possibly non-domain global ring.

## WANTED

None. The sources used are present under `literature/stacks-project/`.

## What was wrong or incomplete

The imported item was statement-only, with no completed proof to attach. Its statement is correct and unchanged. I added the integral-closure definition to its statement dependencies, supplied the argument for both the field and equality assertions, and recorded every non-elementary input as a cited statement. In particular, I did not create a node for either clause of the item.

I read the current blueprint under `literature/blueprint/latest/`, including the chapter/unit and the direct-images proof paragraph (3). The inherited creation chain serves that paragraph through the alteration/moduli/groupoid chain and the Stacks 06FF stabilizer-dimension argument. `tools/blueprint_refs.py ancestor lem-sfb-connected-reduced-scalar-field-uniqueness` returns null on the existing ancestry. I retained that value rather than inventing a blueprint ancestor, preserved the detailed inherited place/via, and added each new input's exact role in that place. Whole-DAG and whole-blueprint keyword/tag searches found no existing statement of any of the three new non-Mathlib inputs. The other 04MK scalar-algebraicity node depends on this item, so using it here would be circular.

The unit route remains the Stacks scalar-field argument. The two off-unit non-leaf tools are declared in `split_report.tool_uses`: the connectedness/idempotent criterion and the Noetherian-space connected-component theorem. Neither substitutes a different six-functor route.

## Source error

In the first paragraph of the proof of Stacks 04MK (`varieties.tex`, `proposition-unique-base-field`), the conclusion after proving a monic equation is printed as “f in k_1”. It must be “f in k_1'”, the integral closure. For example, take X = Spec Q(sqrt(2)) over Q and f = sqrt(2): a monic equation does not put f in Q. This is a proof-text typo, not a false item statement. Step 8 uses the integral closure correctly.

I also expanded the final quasi-compact argument into the two inclusions of the relatively integrally closed fields. The source's final equality with the intersection is true after these inclusions; no correction to that equality is necessary. I did not depend on any assertion that an intersection of affine opens is affine, nor on decomposing overlaps into finitely many components.

## New input arguments and search assessment

These arguments are recorded here for subsequent workers; the new unsplit files themselves contain statements only.

For `lem-sfb-reduced-integral-polynomial-generalized-inverse`, I read 04MI (`lemma-integral-closure-ground-field`) and the finite-algebra calculations in algebra.tex, 00J6 (`lemma-finite-dimensional-algebra`) and 00JA (`lemma-product-local`). This is a polynomial refinement of their reduced integral-algebra input, not a literal quotation of 04MI. Given a monic annihilator p of x, factor p(T)=T^m r(T) with r(0) nonzero. If m=0 then r(x)=0. If m>0, (x r(x))^m=0, so reducedness gives x r(x)=0. Since T and r are coprime, the Euclidean algorithm gives u(T)T+v(T)r(T)=1. Evaluating and multiplying by x yields x^2 u(x)=x. The zero algebra is immediate. This isolates the real commutative-algebra input (factorization and polynomial Bezout) rather than moving the connected-scheme field conclusion into a node. The algebra can be disconnected and have zero divisors. Searches with two natural-language phrasings, Loogle, and the integral-closure/generalized-inverse/absolutely-flat source patterns found only domain inverse theorems and radical-minimal-polynomial facts, not this statement. In particular `IsIntegral.isUnit` cannot replace it for a reduced ring with zero divisors.

For `lem-sfb-relatively-closed-constants-units-fg`, I read all the hypotheses and alternative (1) of 04L7 (`proposition-units-general`) in varieties.tex. The node retains local finite type, connectedness, reducedness, finitely many irreducible components, and the relative integral-closedness assumption. It asserts only that alternative, with the unit quotient defined inline. Rosenlicht/global-units searches with a second phrasing found number-field Dirichlet results and unrelated globally finite section results; none state this theorem for arbitrary reduced schemes.

For `lem-sfb-subfield-units-quotient-finite`, I read the middle quasi-compact paragraph of 04MK, from the intersection k_12 through its Laurent-polynomial surjection and Zariski's lemma. For general A and its subfields K,L, the kernel of L^* to A^*/K^* is exactly (K intersect L)^*. Its quotient is a subgroup of a finitely generated abelian group and is therefore finitely generated. Choose representatives alpha_i in L^*. Every nonzero element of L is a scalar from the intersection times a Laurent monomial in the alpha_i; zero is also in the generated algebra. Thus L is a finitely generated algebra over the intersection field, and Zariski's lemma makes the extension finite. This statement removes all scheme hypotheses and does not assert equality or relative closedness of K and L. Semantic searches with both phrasings and the subfield/finite-dimensional searches found only intermediate-field results that assume finiteness in advance, not a result deriving it from the unit quotient.

For `lem-sfb-integral-element-tower-descent`, I read algebra.tex 00GN (`lemma-integral-transitive`) and the exact Mathlib elementwise transitivity theorem. The latter assumes an integral intermediate algebra and integrality of this one element of the top ring. It does not require the entire top ring to be integral. Set its intermediate algebra A to the node's S. All scalar maps in the node form exactly its scalar tower. `isIntegral_trans` is the exact match; grep gave its declaration at line 479. The natural-language and Loogle hits agree.

Every recorded Mathlib query was actually run with msearch.py and its results read; no unavailable service has been counted as a negative result. Queries were reused after resumption because none of these statement/search questions changed. The second phrasing was used before each no-match conclusion.

## Review by Q54

I checked the files against delivery-errors B–E with the source statements open. The item follows 04MI for its field clause and 04MK for comparing the two constants fields. It requires nonempty connected reduced X and two locally finite type structures; it adds no irreducibility, separatedness, properness, perfection, or finite-extension assumption. Each new statement introduces all its own objects, cites or defines its notions, uses single-escaped TeX, and has no hidden proof in its statement. The three unsplit inputs have empty proofs/dependency lists; the fourth is the exact Mathlib leaf described above.

Step 1 uses the scheme definition for the nonzero stalk at a point, the field definition for injectivity, the reduced-scheme definition's explicit assertion that all section rings are reduced, and `lem-pc-scheme-connected-iff-idempotents` for the global ring's only idempotents. That last statement requires a nonempty scheme, which this item has. I did not infer that the global ring is a domain.

Step 2 uses the integral-closure definition's subring assertion and the new generalized-inverse statement. The polynomial inverse stays in that subring, its product with c is an idempotent, and the existing connectedness criterion makes it 1 once c is nonzero. The displayed multiplication checks that this really gives an inverse. No finite-type condition is silently used for the field clause.

Step 3 uses the single-element tower leaf, not the stronger whole-top-algebra transitivity statement: A need not be integral over C_i. The integral-closure definition then gives relative closedness. I opened `lem-weil-pbc-morphism-into-affine-scheme`; it actually states the ring-map/morphism bijection needed here, not merely full faithfulness of affine spectra. The local finite-type definition provides the affine charts, and the same finite generators still work over the larger field because k_i factors through C_i. Compatibility of this structure with the original map follows from that bijection.

Step 4 uses `lem-weil-pbc-finite-type-over-noetherian` for a finite-type morphism to the spectrum of a field, after checking the target is Noetherian. The field has two ideals; its spectrum is a quasi-compact affine chart by `lem-weil-pbc-affine-scheme-qcqs` and is locally Noetherian by `pqf-def-locnoeth`. The finite-type definition combines local finite type with the now-assumed quasi-compactness of X. `lem-weil-pbc-noetherian-finitely-many-components` gives exactly the finite irreducible-component hypothesis of the units node. Step 3 provides both local finite type over C_i and relative closedness, so all the units-node hypotheses hold for each C_i. The subfield-quotient node then gives finite extensions of their intersection inside the same nonzero ring A. Finite-dimensionality gives a monic annihilator by linear dependence of powers; relative closedness supplies each inclusion. None of the cited statements is used only through its proof.

Step 5 uses affine quasi-compactness, finite-type-over-Noetherian, and `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` to give a Noetherian topological chart. I opened the latter: it says the minimal-closed-set condition, equivalent to the descending chain definition used in the component theorem. `lem-sfb-noetherian-connected-components-open` says the components are open, and `lem-sfb-noetherian-space-compact-subsets` says all subsets of that Noetherian chart are quasi-compact. Thus the components are legitimate nonempty connected quasi-compact open subschemes covering X. Reducedness restricts because their stalks are the original reduced stalks. I added an explicit citation of `lem-weil-pbc-lft-affine-pairs`: its statement quantifies over every affine pair, so restricting the source to an open preserves that condition. This repairs the earlier implicit appeal to source locality. The quasi-compact argument already proved now applies to both field structures on each component.

Step 6 uses the integral-closure definition to restrict a monic equation and choose one equation over k_2 on a starting open. The field definition gives injectivity into the sections of any nonempty overlap, because that section ring is nonzero at one of its stalks. Polynomial evaluation commutes with restriction by ring-map identities. Step 7 uses the connected-scheme definition's absence of a nontrivial clopen partition: the union of successful indices is disjoint from the union of unsuccessful ones, by the displayed injectivity. The polynomial values lie in the local common fields because their coefficient field is contained there. These are elementary steps, written out, with no new lemma for a cover or for overlap propagation. Step 8 uses precisely the uniqueness clause of the structure sheaf in the scheme definition to globalize that same monic equation, then uses the integral-closure definition for the two inclusions. It does not attempt to glue unrelated polynomials of unbounded degree.

I tested the new algebra input on B=0, x=0, a field, and B=k times k with x=(1,0). The latter has the generalized inverse y=(1,0), and illustrates why the algebra lemma must allow zero divisors; the scheme connectedness is applied later. For the units input, X=Spec k has trivial quotient, and X=G_m has its expected finitely generated quotient; the node does not assert that units are finitely generated without dividing by constants. For the subfield input, K=L gives degree one and a zero-dimensional unit quotient, and A may be a product of fields; only common identity and nontriviality are needed for the kernel calculation. In A=k(t), K=k, L=k(t), the conclusion would fail without the unit-quotient assumption, which indeed fails there. For the tower leaf I checked that zero rings and noninjective structural maps are permitted, and that no integrality of the entire top algebra is needed. Inseparable finite field extensions are allowed everywhere.

For the item itself, disconnected X=Spec(k times k) would make the closure k times k fail to be a field, and the connected nonreduced scheme Spec(k[epsilon]/epsilon^2) would have a nonfield integral closure; both excluded hypotheses are essential. Dropping local finite type allows X=Spec k(t), with its k and k(t) structures, whose closures differ; the k-structure is not locally of finite type. The general-X proof uses no global quasi-compactness. There are no proof steps over 2000 characters, and no lemma is hidden in an overlong step. The largest step is the explicit construction of the open cover, with its inputs individually cited.

I compared every use with the cited node's statement, then copied those statements into citations.json without alteration. The elementary field-map, idempotent, polynomial and sheaf-uniqueness calculations remain steps. No new node is the item, either clause, or a special case of an already available statement. I explicitly rejected the downstream scalar-algebraicity node to avoid a cycle. The repairs during this review were the explicit open-restriction citation, explicit Noetherian target check, and correction of the source-text missing prime; the item's statement did not change.

## Not duplicates

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one: the existing node assumes an algebraically closed base, a finite reduced algebra and no nontrivial idempotents to conclude dimension one; the new node allows any field and any reduced ambient algebra, with zero divisors and idempotents, and constructs a polynomial generalized inverse of one integral element.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-sfb-finite-maximal-support-localization: the existing node decomposes a finite module with finite maximal support into localizations; it does not construct a polynomial in a given integral element satisfying x^2 y=x.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-sfb-connected-reduced-scalar-field-uniqueness: the new node is a reduced-ring polynomial identity, with no connected scheme and no comparison of fields; it does not restate either item clause.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-local-tensor-quotient-power-bound: the existing node is a uniform bound on powers of maximal ideals for a localized finite algebra; the new node is a polynomial generalized inverse in an arbitrary reduced algebra, with no localization or power-bound conclusion.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-product-of-localizations-at-maximal: the existing node assumes finitely many maximal ideals and locally nilpotent Jacobson radical of its whole ring and gives a product decomposition; the new ambient ring need not be Artinian or have finitely many maximal ideals, and the conclusion supplies y in k[x], not merely a decomposition.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-finite-dim-algebra-artinian: finite-dimensional implies Artinian does not state a polynomial generalized inverse of one integral element in an arbitrary reduced ambient algebra; obtaining that inverse needs the additional reduced/polynomial argument.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-dimension-zero-local-strictly-henselian: the existing node concerns strict henselianity of a zero-dimensional local ring with separably closed residue field, not a polynomial generalized inverse; the new node has no local or residue-field hypotheses.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-completion-localized-algebra-finite-quotients: the existing node splits finite quotients of completed localized finite algebras, while the new node concerns a polynomial identity in one integral element, with neither completion nor localization.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-local-dimension-zero-henselian: the existing node is the henselianity of a zero-dimensional local ring; the new node does not assume locality and has no henselian conclusion.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-local-tensor-quotient-base-ideal-detection: the existing node detects tensor-sum vanishing from local base-ideal memberships; no such tensor sum or base ideal occurs in the new polynomial identity.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-weil-pbc-local-tensor-quotient-detection: the existing node detects tensor-sum vanishing from uniform local quotient exponents; it does not assert the reduced-algebra polynomial identity and imposes different local finite-algebra data.

lem-sfb-reduced-integral-polynomial-generalized-inverse vs lem-cbc-spine-inner-anodyne: the existing node concerns simplicial spines and inner anodyne maps, so the shared 00JA source token is a citation-token collision and has no mathematical relationship to the commutative-algebra statement.

lem-sfb-subfield-units-quotient-finite vs lem-sfb-space-two-field-scalar-algebraicity: the existing node compares residue-field scalar images on an algebraic space with two locally finite type structures and depends on this item; the new node instead assumes a finitely generated ambient unit quotient in a general ring and concludes finite degree over an intersection, independently of schemes or residue fields.

lem-sfb-subfield-units-quotient-finite vs lem-sfb-connected-reduced-scalar-field-uniqueness: the new node gives a finite-degree consequence of a unit-quotient assumption in a general ring; it asserts neither equality of integral closures nor that a closure is a field, and leaves the scheme, unit-theorem and relative-closedness assembly in the item.

lem-sfb-integral-element-tower-descent vs lem-real-henselian-residue-galois-action: the existing node constructs a residue Galois action for a henselian local ring and integral closure in an algebraic closure; the new node is elementwise integrality descent for an arbitrary commutative ring tower with no henselian or Galois data.

lem-sfb-integral-element-tower-descent vs lem-weil-pbc-integral-transitive: the existing node assumes the entire upper algebra is integral over the middle algebra; here the ambient global section ring need not be integral, only one selected element is. The new node records the exact elementwise Mathlib declaration isIntegral_trans, rather than applying the whole-algebra statement under an unavailable hypothesis.

## What remains

The three new non-Mathlib inputs are intentionally statement-only for later stage-1 work. There is no unfinished argument in the item's assembly proof. Server dry-run and delivery results follow below when available.
