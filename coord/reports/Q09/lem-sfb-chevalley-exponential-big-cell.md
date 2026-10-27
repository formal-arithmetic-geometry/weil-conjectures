# Q09 stage-1 report: lem-sfb-chevalley-exponential-big-cell

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-exponential-big-cell.json`: split; statement unchanged; seven proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-unipotent-polynomial-coordinates.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-opposite-rational-collection.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-block-gauss-scheme-chart.json`: new statement-only general matrix lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-generic-matrix-locus-subgroup-closure.json`: new statement-only general closure lemma, unsplit; no Mathlib match.
- `citations.json`: verbatim statement extracts for each proof-step citation.

The sandbox initially contained dispatcher brief files only, with no item, report, or search log. The item was copied from the current read-only mirror. No repository or launcher file was written; no git, Lean compiler, Lake or build command was run. No agents were started.

## Attachments

None. Searches for the item tag, Chevalley, big-cell, and root exponential notions under the live `lean/WeilConjectures/` and `lean/Sheaf/` did not find a declaration stating the item. The Chevalley hits under WeilConjectures concern constructible images, valuations or Beck–Chevalley maps. The project has no completed declaration for this pre-reductivity construction.

## Literature wanted

WANTED: R. Steinberg, Lectures on Chevalley Groups (1967), the root-subgroup collection and unique unipotent-coordinate arguments, for lem-sfb-chevalley-unipotent-polynomial-coordinates and lem-sfb-chevalley-opposite-rational-collection. Milne §23h Notes, p.511, names these lectures as the basic reference. No copy is listed in literature/LIST.md. Nothing was downloaded. The split and its supporting new statements are explicitly agent-written rather than attributed to an unread proof.

## What required repair in the imported material

The item has an empty proof and calls itself an agent-stated strengthening of Milne. I retained its statement, including its explicitly corrected condition Delta subset R, and supplied the missing argument rather than citing the parent's reductivity result. The parent lem-sfb-chevalley-root-exponential-group uses this item's tangent conclusion to prove maximality of T before applying the rank-one reductivity theorem; citing that parent, or the reductive Borel/root-product theorems, would be circular. None is used.

Milne's p.510 sentence defining the torus by independent scalars on weight spaces does not supply the exact weight-character torus required here. I used Spec F[P] and proved its closed matrix embedding by the explicit character-algebra surjection. Likewise I make no use of Milne's claim that the Lie algebra is the reduction of the chosen integral Lie form. The item already excludes that identification. There is no new statement dispute and no statement weakening.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor returned None. I retained that value and the inherited chain verbatim and prepended this item to the new nodes' via chains. I read the latest main-20261024 direct-images proof (3), which now phrases the alteration work through the open direct-image theorem; this descendant still carries the inherited Chevalley-construction prerequisite. No chapter or unit route was changed, and the item is not a unit key node. No realization fields were written.

## Argument and smaller inputs

Write C for A^N times T times A^N. The one-sign lemma supplies actual closed subgroup schemes U_minus and U_plus and their prescribed polynomial coordinates; it does not mention K or an opposite product. The matrix Gauss chart identifies C with a closed subscheme of a principal open of GL, so C is a locally closed matrix locus. Its coordinate algebra is polynomial/Laurent polynomial and stays a domain after any field extension.

The opposite-collection input is strictly a localized matrix identity p_plus(b) p_minus(a) = p_minus(A) h p_plus(B) with a denominator d satisfying d(0)=1. It gives neither a generated group nor openness nor a tangent description. Its domain is essential: in the standard SL2 module, the factors are A=a/(1+ab), h=diag(1+ab,(1+ab)^(-1)), B=b/(1+ab). A global polynomial refactorization would be false at ab=-1.

The assembly explicitly computes a generic product and a generic inverse in C. I initially wrote the scheme-image Hopf-ideal calculation inline, then extracted its reusable general claim into the fourth unsplit node instead of hiding a generic closure theorem in an elementary step. For that input, let B be the ambient group coordinate ring and I=ker(B -> A). The two generic laws show that the pullbacks of f in I vanish on nonempty opens of C^2 and C. Geometric integrality makes those rings domains, so the functions vanish globally. The injection B/I -> A tensors injectively with itself over the field (choose linear retractions). Thus the coproduct and antipode preserve the quotient B/I, and evaluation at the specified identity kills I. Group identities descend from the ambient Hopf algebra. This proves precisely the closure claim without assuming that C is already a group. The item then proves that the resulting subgroup is K by the two inclusions from its generators and scheme-image minimality.

For the block chart, the inverse is obtained inductively from [A B; C D] = [1 0; C A^(-1) 1] diag(A,D-C A^(-1) B) [1 A^(-1)B;0 1]. At each stage the next block determinant is a unit because the successive leading minors are units. This works over arbitrary test algebras. The formulas are regular after inverting the product of those minors, and uniqueness follows successively from the first block and its Schur complement. Conjugating every block by a block diagonal matrix conjugates all these formulas. This many-block scheme isomorphism is not just the single two-block identity.

For the unipotent and opposite-collection nodes, the intended later proofs are the integral root-string collection argument, with the rank-one SL2 formula for opposite roots. In the one-sign case the height filtration orders the correction terms; uniqueness must be proved as a matrix-scheme claim on all test algebras, not merely as a bijection of F-points. In the opposite case one must track the localized denominators and show that they are 1 at zero. These are the non-elementary tasks explicitly left in the two statement-only nodes; their statements carry no proof sketch. They do not use the present item or its parent as a dependency.

## Searches and Mathlib verdicts

All new searches were executed using the required unmodified batch2/msearch.py with Q09 and this item, and their actual records are in searches.jsonl. Each new node records two different LeanFinder phrasings, LeanSearch, Loogle and a source grep. No unavailable response was recorded as absence. The pre-existing item search records were preserved and relevant newly run searches appended.

I read the returned signatures. GeckConstruction supplies matrix Lie-algebra identities, not arbitrary-characteristic algebraic-group coordinates. RootPairing results are root combinatorics. Analytic exponential lemmas require normed-algebra hypotheses and do not express integral divided powers. Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec, read in Transvection.lean around lines 673-691, allows arbitrary transvections over a field and supplies no prescribed-root or scheme chart. Matrix.fromBlocks_eq_of_invertible₁₁, read in SchurComplement.lean lines 48-58, is the useful two-block identity but does not supply the many-block scheme isomorphism or its unique natural inverse in one line. Closure hits concern existing abstract/topological subgroups or generic IsIntegral/immersion instances, not a locus with only generic laws. The four new nodes therefore remain unsplit, with zero new Mathlib leaves.

## Not duplicates

lem-sfb-chevalley-unipotent-polynomial-coordinates vs lem-sfb-borel-root-product-coordinates: the existing result assumes a reductive ambient group, a maximal torus and a Borel; the new result constructs closed one-sign subgroups directly on an admissible lattice before reductivity is known. The existing proof cannot be used here to establish its own hypotheses.

lem-sfb-chevalley-unipotent-polynomial-coordinates vs lem-sfb-unipotent-root-intersection-products: the existing result concerns intersections of Borel radicals in an already reductive group; the new result has no Borel or reductive hypothesis and is a matrix-construction input.

lem-sfb-chevalley-opposite-rational-collection vs lem-sfb-root-monomial-kernel-coordinates: the existing result assumes reductive source and target groups and then compares root-coordinate homomorphisms; the new result asserts only a localized opposite-product matrix identity before a reductive group has been constructed.

lem-sfb-block-gauss-scheme-chart vs lem-sfb-transverse-subgroup-product-open: the existing theorem requires a known Lie-algebra direct sum inside a smooth ambient group. The new one is a block-matrix scheme isomorphism with an explicit principal-open target and works over arbitrary field algebras, without any group smoothness or tangent hypothesis.

lem-sfb-generic-matrix-locus-subgroup-closure vs lem-wf-zariski-closure-subgroup: the old result concerns an actual abstract subgroup over Q_l-bar; the new one starts with a geometrically integral scheme locus having only generic laws and proves the scheme-image subgroup assertion over an arbitrary field.

lem-sfb-generic-matrix-locus-subgroup-closure vs lem-sfb-perfect-field-groupoid-image-closure: the latter starts with a morphism of existing groupoids and assumes a perfect field; the new one has no source group/groupoid, starts with generic partial laws on a matrix locus and uses geometric integrality rather than perfection.

No new node restates a clause of the item: in particular none states that the displayed map is open in K. DAG and whole-blueprint searches were run for Chevalley, root product, unipotent product, Gauss decomposition, triangular, refactorization, generic multiplication, generically and group closure. The candidate existing statements above were opened, not dismissed by their titles. No Stacks tag was added to a new node's source; hence there are no same-Stacks-tag pairs requiring an additional comparison.

## Review by Q09

I read Milne iAG §23h equation (152), equation (153), Theorem 23.72 and its proof and Corollary 23.73 on printed pp.509-511 for the item and the two integral-exponential inputs. Milne explicitly omits the details, so I did not attribute the new coordinate/refactorization assertions to a proved sentence there. For the general block input I read the actual Mathlib two-block identity and the transvection theorem identified by the searches; the many-block chart is recorded as an agent lemma. For the fourth input I read Milne Lemma 1.40 and Theorem 1.45, pp.18-19, for the closure stability method and gave the exact coordinate proof above for the stronger generic-law formulation. For the open-in-image input I read the existing node and Stacks morphisms.tex lemma-quasi-compact-immersion, Tag 01RG: the quasi-compact alternative is exactly the hypothesis supplied by step 3. No SGA route is used.

For step 1 I opened lem-sfb-chevalley-admissible-representation. Its statement supplies both the Chevalley bracket and the weight/decomposition/divided-power conditions used in the coefficient calculation; the quote includes these clauses. There is no appeal to its proof or to reductivity.

For step 2 I re-read the entire new one-sign statement. It gives closed immersions, subgroup structures and the block unitriangular property, precisely what the step needs. The choice of a separating positive functional is a finite hyperplane avoidance argument over Q, not over the possibly positive-characteristic field. The scalar weight torus's closed embedding is written out by a surjective coordinate map, including the negative characters obtained from inverse block determinants; I corrected the initial overly terse assertion of that surjectivity by writing the rank of each weight block explicitly.

For step 3 the new Gauss statement supplies the scheme isomorphism onto a principal open on all test algebras. The closed factors' coordinate surjections give a closed immersion of their product. I initially cited the freeness conclusion of lem-sfb-root-datum-lattice-embedding, but its complete statement starts with a separate lattice M. To avoid an unstated instantiation I replaced that proof citation with the existing Mathlib leaf lem-trf-fg-torsionfree-group-free, whose entire statement I read: every finitely generated torsion-free abelian group has a finite integral basis. Here the given finite weight set Omega generates P, and P is torsion-free because it sits in a rational vector space. These verify every hypothesis directly. The root-system convention remains an unchanged statement dependency. Quasi-compactness holds because C is affine of finite type over F and the target is affine (or because the Gauss chart is affine and its restricted image is closed).

For step 4 the one-sign statement gives the subgroup operations and the opposite-collection statement gives actual regular maps on an open with d(0)=1. The product and inverse formulas are written, including the two torus conjugations; I checked their multiplication order by direct cancellation. Each domain contains the identity, so it is nonempty even in characteristics two and three, and is dense in the integral source. Nothing asserts that the locus is globally closed under multiplication.

For step 5 the new generic closure statement asks for an affine geometrically integral finite-type source, an immersion, an identity lift and generic regular laws. Steps 3 and 4 supply all four. Its conclusion is exactly that H is a closed subgroup; the two inclusions H=K are then established in this proof, not taken from the new node. I opened def-nagata-scheme-theoretic-image: its definition explicitly makes the image the smallest closed subscheme through which the morphism factors; this is precisely the minimality used in H subset K. Since all schemes in this step are affine, the kernel on coordinate rings gives that image.

For step 6 lemma-nagata-immersion-open-in-scheme-image really states openness of the canonical factor for a quasi-compact immersion, with no reductivity hypothesis. It is already a Mathlib leaf and therefore an allowed generic tool without an off-unit route exception, as is the finite torsion-free group basis theorem used in step 3. The image has already been identified with K. The conjugation identities come from step 1 on arbitrary test algebras, rather than from pointwise detection on F-points.

For step 7 I checked the dual-number multiplication: every first-order coordinate contributes its displayed matrix, mixed products vanish, and the torus term is its usual tangent vector. Since the chart is an open immersion, this linear map is an isomorphism, so no separate characteristic-dependent assertion of nonvanishing of a reduced Lie-form root vector is used. Character distinctness is distinctness in the lattice P, not distinctness of their differentials.

Small cases checked: empty root system and V=0; zero-dimensional W (GL(0)=1 in the generic matrix lemmas); one weight block and no roots; rank-one SL2 in arbitrary characteristic, including F_2-bar; SL2 with two copies of its standard module, which confirms that the middle torus consists of the actual linked weight scalars; SL3 with the two possible height-one orderings, whose difference is absorbed in the height-two coordinate. The block chart includes s=0 and s=1 and allows nonreduced test algebras; the opposite-collection identity includes a unit condition rather than incorrectly saying a field element is merely nonzero over a general algebra. The generic closure statement excludes the zero ring and uses geometric integrality so that the product source is integral as required. Its identity-lift assumption prevents a translate of a subgroup from being misidentified with a subgroup.

I checked delivery-errors B through E against the actual files: new nodes are self-contained statements with empty proofs and proof dependencies, their notions are introduced or cited, their blueprint fields are filled, and all logged searches are real. The only imported statement modification was no modification. Every non-elementary assembly input is a cited node whose statement I opened; citations.json has a literal extract for every use. No parent/dependent result is cited, so the split introduces no backward edge. The four smaller lemmas are neither the item nor its individual global clauses. Every proof step is below 2000 characters, and the reusable closure subclaim was extracted rather than hidden. This review is my signature as author; the maintainer's review is independent.

## Unfinished work

No part of this item's stage-1 split is left unwritten. The four new lemmas are deliberately unsplit and join the queue, as required by a one-level split. No Lean statement or proof was attempted.

## Validation

The initial complete delivery dry run passed at 5ad537a00bc. The final citation audit then replaced the lattice-freeness citation as explained above; the required dry run is repeated for that concrete correction before push.
