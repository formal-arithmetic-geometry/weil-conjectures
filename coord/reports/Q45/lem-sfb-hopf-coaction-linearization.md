# Q45 stage-1 delivery: lem-sfb-hopf-coaction-linearization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-hopf-coaction-linearization.json`: the existing statement, unchanged mathematically and textually, now split into twelve explicit steps. Its statement dependencies now include scalar extension and the multiplication on algebra tensor products, which the original statement already uses.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-coordinate-hopf.json`: statement, Mathlib leaf. The affine-group coordinate-ring instance at `Mathlib/AlgebraicGeometry/Group/Affine.lean:337` gives its Hopf structure; the recorded coalgebra, bialgebra, antipode and finite-sum consequences give each displayed clause. There are no new unsplit nodes.
- `citations.json`: one entry for every use in every proof step, copied verbatim from the statement used.
- `searches.jsonl`: original search-command records; `write_split.py` is the sandbox-only construction script. All project files outside this sandbox were read only. No git command, Lean edit, compiler, Lake or local DAG-validation tool was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, coactions/comodules and the relevant semilinear terminology find no declaration covering this item. The GroupScheme/GeneralLinear representation file mentions subcomodules, but does not state this dictionary. The new prerequisite is a Mathlib declaration, not an attachment of a project proof.

## WANTED

None. All mathematical sources used were available in the read clone.

## Corrections and scope

The original item has a correct statement. Its proof was empty. The proof now distinguishes the preliminary universal-property bijection for arbitrary maps from the subsequent proof of invertibility. It computes the ring of composable arrows, fixes the order of the two group coordinates, and verifies both inverse composites. In particular, the antipode expression is checked to be L-linear over the twisted E-action; it is not accepted merely because it is written on pure tensors.

The source is Stacks `groupoids.tex`, Tag 03LF, label `definition-equivariant-module`, lines 2244 onward. It gives the identity and cocycle diagrams; it does not state the displayed finite-sum inverse. The inverse and tensor calculations are therefore explicitly agent-written, with `proof_origin.by = agent`. I also read Tag 022S, label `definition-group-scheme`, including the group laws immediately preceding it; `algebra.tex` Tag 00CX, label `lemma-tensor-product`; and `schemes.tex` Tag 01I4, label `lemma-fibre-product-affine-schemes`. No SGA source is used.

The latest blueprint was read through `literature/blueprint/latest`, currently `main-20261023-1620`, in particular the unit section and the direct-image proof (3). This item is an auxiliary of the already chosen quotient-stack/invariant-algebra branch, not the unit's key statement. No unit or chapter record is changed. `tools/blueprint_refs.py ancestor` returns `None` for this imported-created ancestry; the null ancestor and full existing via chain are retained, and the new leaf has the item prepended to that chain. Whole-blueprint searches for `coaction`, `semilinear coaction`, `Hopf`, `coordinate ring`, `antipode`, and `affine group` found no equivalent blueprint theorem. The existing special coordinate descriptions for general linear groups and tori are not the general theorem for arbitrary affine group schemes.

## Not duplicates

lem-sfb-affine-group-coordinate-hopf vs det-d-geometry: the existing imported node discusses affine varieties and matrix algebraic groups cut out by Hopf ideals; it does not supply the coordinate Hopf identities for every affine group scheme over every field, without finite-type assumptions.

lem-sfb-affine-group-coordinate-hopf vs sk-d-geometry: the existing node defines explicit general-linear coordinate maps in its algebraically closed characteristic-zero setting and Hopf-ideal quotients; the new leaf is the generic affine-group coordinate construction, including both antipode identities, with no such restrictions.

lem-sfb-affine-group-coordinate-hopf vs lem-wf-hopf-augmentation-height: the existing lemma assumes a finite-type commutative Hopf algebra with its identities already supplied and concludes an augmentation-ideal height equality. It neither constructs the coordinate Hopf structure nor gives that conclusion for arbitrary affine groups.

lem-sfb-affine-group-coordinate-hopf vs lem-sfb-hopf-coaction-linearization: the leaf states only facts about C=k[H]. It has no E, no M, no semilinear coaction, and no linearization. The item's twelve steps prove the correspondence, inverse, morphism and tensor assertions themselves. It is not a clause of the item moved out to a new node.

The exact Stacks tag 022S was searched throughout the DAG before creating the leaf; no existing source carrying that tag was found. The tag 03LF belongs to the item and is not the new leaf's source. The two existing Mathlib tensor leaves and the module-base-change universal-property leaf are reused, rather than recreated.

## Review by Q45

I checked B--E of `coord/delivery-errors.md` against the actual node statements and the sources just listed. The new node introduces k, H, C and each structure map explicitly, expands the Hopf axioms instead of using a tag as a definition, has no proof sketch or deferred proof, and names the exact Mathlib declaration, file and verified line. Its searches are the actual msearch.py calls retained in searches.jsonl. The first semantic coordinate-ring search returned mainly generic group-like and monoid-algebra results; Loogle's `HopfAlgebra, AlgebraicGeometry.Scheme` and the grep identified the exact coordinate instance, whose construction I read. Searches for the whole item returned abstract-group free linearization, which is different. The second phrasing confirmed that distinction. I did not turn these unrelated hits into matches or record any unavailable service as a negative mathematical result.

Step 1 takes the full coordinate Hopf identities from the new leaf and the tensor multiplication from the existing algebra-tensor pushout leaf. I read `Affine.lean:337-343` and its fully faithful Spec transport, the cogroup/Hopf equivalence in `CommHopfAlgCat.lean:199-219`, the inherited coalgebra and bialgebra axioms, `HopfAlgebra/Basic.lean:71-108`, and `HopfAlgebra/Convolution.lean:80`. Thus the operations are dual to the given group operations, and no cocommutativity, smoothness or finite type is implicit. This theorem is used as a Mathlib leaf; no project definition is being cited for an unstated affine-equivalence theorem.

Step 2 uses the statement of `lem-weil-pbc-module-base-change-universal-property`, which really gives the map-out bijection and the inverse formula, with R=E, S=L, and N=M tensor_k C carrying E through rho_E. I checked the change of tensor order and gave both maps identifying the target extension. The two cited definition leaves give the scalar action, balanced tensor relations and pure-tensor generators. Semilinearity over E implies k-linearity because rho_E is a k-algebra map. These are all the lemma's hypotheses.

Step 3 uses only tensor relations to compute identity pullback, with both composites E -> L -> E equal to the identity by the assumed counit of rho_E. Step 4 uses the actual affine fibre-product statement, not its proof, for L_a tensor_E L_b. It writes the forward and inverse ring formulas and the balancing relation, then the three coordinate maps. The commutative-algebra tensor leaf supplies multiplication and its universal property. This justifies the affine ring of composable arrows without assuming an unrecorded base-change theorem.

Step 5 uses the given coassociativity of rho_E to identify the source scalar action. The two displayed composite formulas come from substituting the three coordinate maps into d(m tensor l)=theta(m)l; generation of scalar extensions is in the cited tensor definition. Their equality is exactly coassociativity of theta, in both directions. The order is first h, then g, in agreement with the item's composition hg; no commutativity of H was used.

Step 6 derives its auxiliary coefficient identity in three displayed equalities from the assumed algebra-coaction axioms and the cited Hopf cancellation. It is an elementary calculation, not a new lemma node. Step 7 defines the candidate inverse as a composite of linear tensor maps before testing L-linearity. Its E-linearity calculation uses the balance em tensor_s l = m tensor_s rho_E(e)l, multiplicativity of S from the leaf, and precisely step 6. Its C-linearity is direct. The algebra-tensor leaf gives generation by products from E and C. Step 8 writes both inverse composites and uses the two different Hopf cancellations in their original order. No injectivity or flatness of an uncited tensor functor is assumed.

Step 9 compares a module map on m tensor 1, using the actual functorial scalar-extension formula and tensor generators stated by the cited leaves. Step 10 writes the two scalar-extension identifications for E and computes the unit datum. Step 11 writes both directions of the tensor comparison and checks the E- and L-balancing relations, then evaluates the tensor datum. Step 12 separately verifies the tensor-coaction balancing, semilinearity, counit and coassociativity, using exactly the multiplicativity supplied by the Hopf leaf. These are explicit calculations from previously stated maps, not an appeal to a hidden tensor-descent theorem. None of the twelve steps exceeds 2000 characters.

I tested the conventions on the trivial group (C=k, theta=id, both linearizations and inverse reduce to identities), the zero module, and E=0 (all modules involved vanish). For H=G_m and a weight-n vector, theta(v)=v tensor t^n and the inverse uses t^(-n), giving both inverse composites. With E=k[z,z^(-1)] and rho_E(z)=z tensor t, step 6 gives (z tensor t)(1 tensor t^(-1))=z tensor 1, testing the twisted balance rather than only the case E=k. For the nonreduced group alpha_p in characteristic p, Delta(t)=t tensor 1+1 tensor t and S(t)=-t make both antipode sums zero for t, as required by epsilon(t)=0; with rho_E(z)=z tensor 1+1 tensor t the coefficient identity is (z tensor 1+1 tensor t)-(1 tensor t)=z tensor 1. The proof uses commutativity of C, which every affine scheme coordinate ring has, but never swaps the two coproduct legs, so it also covers noncommutative group laws. Arbitrary direct sums of copies of E test that no bounded dimension or finite-generation condition is hidden: every individual tensor expression remains a finite sum.

Citations in citations.json were copied from each actual cited statement. All proof uses are collected in proof_deps. The only new edge beyond existing scalar/tensor tools is to a Mathlib leaf whose dependencies are pre-existing notions, so it introduces no cycle. There are no off-route statement tools requiring a new tool-use exception. The original statement, source, ancestry, created record and all maintainer-owned fields were preserved.

## Unfinished work

No mathematical clause remains unproved in the natural-language split. Stage 2 and Lean proof work remain outside this task. The required server dry run and push are the delivery steps; their final result is reported by deliver.py.
