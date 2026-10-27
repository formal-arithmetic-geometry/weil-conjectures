# Stage-1 delivery: lem-sfb-pseudoabelian-proper-algclosed

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pseudoabelian-proper-algclosed.json: statement unchanged; six-step dimension-induction proof, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-general-group-centre-zero-dimension-affine.json: statement-only; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-rosenlicht-connected-almost-complement.json: statement-only; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-rosenlicht-nonproper-affine-subgroup.json: statement-only; no Mathlib match.
- citations.json: verbatim statements for every citation of every proof step.

Three new nodes, zero Mathlib leaves. No Lean written or compiled. All writes are in the assigned sandbox. searches.jsonl records the actual msearch.py invocations. milne.txt is a local extraction for reading, and write_split.py is a sandbox-only JSON assembly script.

## Attachments

None. Searched the project source WeilConjectures/ for the item id, pseudo-abelian, Barsotti, Chevalley, Rosenlicht, almost-complement, centre and center. Matrix-group centre statements concern already affine groups; none proves the item or the new nodes. The blueprint tag is absent.

## WANTED

None for this split. The item follows the local Milne Algebraic Groups (2017) PDF. Milne's Proposition 8.25 explicitly delegates its rational-action proof details to other literature; those details belong to the new unsplit dichotomy node, not to this item's assembly. No SGA is cited or used.

## What changed or was wrong

The imported item had no proof. Its statement is correct and unchanged. The proof follows Milne Theorem 8.26, printed p.154, with three clarifications: take the reduced identity component of the centre, use a connected smooth almost-complement, and prove normality by fpqc lifting rather than by a statement only about k-points. The zero-dimensional-centre case uses the actual pseudo-abelian hypothesis to make an affine G trivial, so it does not assume the additional condition O(G)=k appearing in Milne's prose.

The ancestor command returns None, matching the reviewed parent and the inherited null from.node. I retain that provenance rather than invent a blueprint ancestor. The latest blueprint chapter and unit were read; this is an intermediate algebraic-group input of the already reviewed Chevalley decomposition, not the unit key node. Whole latest-blueprint searches for pseudo-abelian, Rosenlicht and almost-complement found no counterpart. Blueprint reference searches for centre affine and complete group returned unrelated nodes, which were checked against the proposed assertions. Unit realized fields are not changed.

## Not duplicates

- lem-sfb-general-group-centre-zero-dimension-affine vs lem-sfb-affine-group-centre-base-change: the existing node assumes G affine, so cannot prove that a possibly non-affine G is affine when its centre is zero-dimensional. The new node does not assert the existing field-extension clause.
- lem-sfb-general-group-centre-zero-dimension-affine vs lem-sfb-conjugation-finite-jet-kernel: the existing jet statement assumes G affine and uses its global coordinate algebra. The new node supplies the general-group centre input and the affineness implication required here.
- lem-sfb-rosenlicht-connected-almost-complement vs lem-sfb-abelian-inclusion-multiple-retraction: the existing retraction statement assumes the ambient group is itself an abelian variety; here the ambient G may be nonproper and noncommutative.
- lem-sfb-rosenlicht-connected-almost-complement vs lem-sfb-group-hom-dimension-kernel-image: the existing dimension statement assumes affine source and target, and constructs no almost-complement to an abelian subvariety.
- lem-sfb-rosenlicht-nonproper-affine-subgroup vs lem-sfb-barsotti-chevalley-decomposition: Chevalley is the parent using this item and cannot be cited back. The new dichotomy gives a subgroup that need not be normal, rather than the normal affine kernel with abelian quotient.
- lem-sfb-rosenlicht-nonproper-affine-subgroup vs lem-sfb-pseudoabelian-proper-algclosed: the dichotomy gives only an affine subgroup, with no normality. The proof has to apply it inside the centre, construct a lower-dimensional almost-complement, transfer normality, and perform induction. It does not restate the item.

No new node has a Stacks-tag collision: their central algebraic-group assertions are Milne's, and their source places explicitly say no Stacks tag states those theorems. Existing Stacks inputs are reused as nodes, not recreated.

## Review by Q44

I read Milne Definition 8.3 and Proposition 8.1 (p.149), Proposition 1.92 and the definition following it (pp.33–34), Corollary 8.10 and Corollary 8.11 (pp.150–151), Theorem 8.24 and Proposition 8.25 (pp.153–154), and the complete proof of Theorem 8.26 (p.154). I also read the local Stacks statements underlying the existing identity-component input (0B7R), reduction over a perfect field (047R), fpqc coverings (022B), and proper scheme-theoretic image (0AH6). I checked each cited node's actual statement, not its proof or title; citations.json contains those statements verbatim.

For the new centre node, Milne 1.92 represents the centre for a possibly non-affine group. The component and reduction discussion gives dim (Z^0)_red = dim Z. Corollary 8.10 identifies the finite-jet kernel with the possibly nonreduced centre, and Proposition 8.1 gives affineness when that centre is zero-dimensional and hence finite. This statement does not assume that the centre is smooth, which would fail for SL_p in characteristic p. The affine-only existing centre and jet nodes cannot substitute for it.

For the new almost-complement node, Theorem 8.24 gives smooth N over the perfect field k. Replacing N by N^0 gives a connected closed normal subgroup. The restricted product still has finite kernel and has image of full dimension, hence is surjective onto connected G; Milne 1.68–1.71 gives faithful flatness, and Proposition 5.23 gives dim G = dim A + dim N. These are properties of the same product homomorphism, not a claim that the product map is an isomorphism or separable. The source permits a nonreduced finite kernel, and so does the node. The source argument and this connected refinement are recorded here for the next worker; the node itself remains statement-only.

For the dichotomy node, Proposition 8.25 gives a positive-dimensional affine subgroup, not a normal one. Over k its reduced identity component is a smooth connected affine closed subgroup with the same positive dimension by Milne 1.35 and 1.39. This refinement does not introduce a normality conclusion. I did not use equivariant compactification Theorem 8.44 to prove it; Milne warns that doing so would be circular.

Step 1 uses only the dimension clause of affine-normal-subgroup-products, the general centre node, and the complete conclusion of locally-algebraic-group-identity-component. The first applies to any separated finite-type group, not just affine groups. The last applies to Z even if it is nonsmooth or disconnected. I wrote composition of closed inclusions as composition of quotient ring maps, so it needs no extra invented node. Strong induction is simultaneous over all such k-groups, not an invocation of the item as a DAG edge.

Step 2 uses the zero-centre-dimension implication and finite-proper. The identity subgroup G is eligible under all stated hypotheses once affineness is known, so G is trivial by the original hypothesis itself. An isomorphism is finite directly on coordinate rings. This provides the d=0 case and any later case with dim A=0.

Step 3 applies the dichotomy to A, whose smoothness, connectedness, finite type and separatedness were established in step 1. Every subgroup of the central A is normal in G on all algebra-valued points, so the original hypothesis really applies to U. Its positive dimension contradicts triviality. The abelian-variety definition used then requires only properness, smoothness and connectedness; it does not supply a hidden commutativity theorem.

Step 4 applies the almost-complement node with exactly its central abelian-subvariety hypotheses. Its formula gives strict dimension decrease because dim A>0. N has every hypothesis of the induction claim except the no-affine-normal-subgroup property, which is proved in step 5. No induction on a disconnected or nonsmooth almost-complement is attempted.

Step 5 checks normality for an arbitrary B-point g, not only g in G(k). The faithfully flat finite-presentation product map gives an fpqc covering, and covering-axioms supplies its pullbacks. There g=an, and centrality makes gsg^{-1}=nsn^{-1}. Normality of S in N now places this point in S. Its local lifts agree because the subgroup inclusion is a monomorphism, and representable fpqc descent glues them. The same descent uniqueness verifies their image is the original conjugate. This proves that S is normal in G, so the original hypothesis makes it trivial, and strong induction applies to N.

Step 6 first uses the exact proper-base-change and proper-composition statements to make A×N proper. The proper-image node assumes a proper source and a separated locally finite-type target, both satisfied here. Its conclusion is properness of the scheme-theoretic image, not merely closedness of the image. I corrected an initial draft's inappropriate pullback-ideal shortcut: factoring through a closed subscheme alone does not make the module pullback of its ideal zero. The final proof instead cites smooth-geometrically-reduced for G and uses surjectivity: the image ideal is contained in all prime ideals on every affine open, hence in the zero nilradical of the reduced ring. This makes the image equal G scheme-theoretically.

Small cases checked: G=1 (dimension-zero branch); G=G_a and G=G_m (excluded by their own nontrivial affine normal subgroup); G an abelian variety (A=G and N can be trivial); A×H with H affine (the almost-complement exposes H and forces it trivial under the hypothesis); finite central group schemes such as μ_p in SL_p (no smoothness of Z assumed); and a purely inseparable isogeny of abelian varieties (finite product kernel need not be reduced). The empty scheme is excluded by the group identity. The statement makes no commutativity assumption, and the proof never adds one for G.

Against delivery-errors B–E: each new node has a self-contained statement, notion citations and empty proof/dependency fields, actual semantic/Loogle/grep searches with two wordings, and precise Milne provenance. No new node duplicates the item, one of its clauses, or an elementary assembly step. The DAG and blueprint were searched for each input, including existing affine-only versions. Each non-elementary step cites the statement it needs, and the few-line calculations, closed-inclusion compositions and nilradical argument are written explicitly. The dependency direction is downward; no Chevalley, equivariant-completion or item-self edge is introduced. Every step is below 2000 characters. Off-unit scheme facts are declared as generic tool uses in split_report, without modifying maintainer-owned tool_uses.

## Unfinished

No unfinished assembly argument. The three new statement-only inputs remain unsplit for subsequent stage-1 work, as required. Validation and direct-delivery results follow below.

## Validation

The required deliver.py --no-push completed with exit 0 and printed OK at 048fd4db1f2: server preflight passed, including check_dag.py and review_split.py. The item statement is unchanged, all six steps are below 1000 characters, and every cited node has its verbatim statement in citations.json. The direct-delivery brief authorizes delivery after this worker's review; no second worker was started.
