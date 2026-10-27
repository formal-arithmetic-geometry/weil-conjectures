# Worker report — Q102

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-group-monomorphism-closed-immersion.json`: item, split; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-trivial-kernel-homogeneous-quotient.json`: new statement-only prerequisite; unsplit, no Mathlib match.
- `citations.json`: exact statement quotations for each use in the four proof steps.

One new node, zero Mathlib leaves. No Lean files were written, and no compiler or build was run. Only this sandbox was written. The existing searches.jsonl was read and preserved; the initial item searches were reused and supplemented. No previous item copy or report existed in this sandbox.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint id and by group/monomorphism/closed-immersion and homogeneous-quotient terminology. No declaration states the item or the new prerequisite. Mathlib's `IsClosedImmersion.iff_isFinite_and_mono`, `Morphisms/Finite.lean:124–125`, requires finiteness of the morphism, not just finite type of the groups over a field. It is not a leaf for this item. `Scheme.LocalRepresentability.isRepresentable`, `Sites/Representability.lean:210`, requires a relatively representable open atlas and local surjectivity; it does not provide the quotient from the group hypotheses. Abstract group quotient and PreGaloisCategory search hits have different objects.

## WANTED

None. The source PDF and Stacks sources are present.

## What needed repair

The live item has no proof. Its statement is correct as written, and was retained verbatim. Its source explicitly specifies the first proof of Milne Theorem 5.34, so I retained that proof, rather than the alternative Zariski-main sketch. That alternative even includes the dubious ambient dense-open claim of Proposition 5.37; none of that sketch is used.

The existing homogeneous quotient node assumes a **closed** subgroup. Applying it to u before proving u closed would be circular. Milne Theorem 5.28 instead starts with a homomorphism with trivial kernel; its representability conclusion is the independent prerequisite needed here. The new node retains only the action, distinguished point and coset-fibre property needed for the argument. It does not assert the item's conclusion, or put the proof into a new node. It has no proof or proof dependencies. Quotient representability is not an elementary fact.

The item's inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` prints `None`. The new node follows that existing lineage, prepending the item to `via` and naming the precise Milne sentence in `from.place`; I did not invent an imported blueprint id or edit maintainer-owned lineage. Searches over the whole DAG and `blueprint_refs.py search` for homogeneous, quotient, coset, trivial kernel and monomorphism found no exact imported blueprint counterpart. The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` was read, along with its unit. The inherited alteration/Picard subroute is more detailed than that current proof's paragraph (3); this delivery keeps the item's specified local route and enclosing direct-image clause.

## Not duplicates

lem-sfb-trivial-kernel-homogeneous-quotient vs lem-sfb-algebraic-group-homogeneous-quotient: the existing node assumes a closed immersion j and supplies quotient flatness and local lifts; the new prerequisite assumes only trivial scheme-theoretic kernel, and supplies homogeneous representability and coset fibres before closedness is proved. The stronger input would be circular for this item. Both cite Milne 5.28, so this difference is essential.

lem-sfb-trivial-kernel-homogeneous-quotient vs lem-sfb-homogeneous-orbit-quotient-geometry: the existing result assumes an algebraically closed field, smooth connected affine ambient group and a closed subgroup; the new statement allows arbitrary fields and separated finite-type non-smooth non-affine groups with only a trivial-kernel homomorphism.

lem-sfb-trivial-kernel-homogeneous-quotient vs lem-sfb-smooth-commutative-subgroup-quotient: the existing result concerns a closed inclusion of smooth commutative geometrically integral groups and a group quotient; neither commutativity nor normality nor smoothness is assumed in the new homogeneous-space theorem.

lem-sfb-trivial-kernel-homogeneous-quotient vs lem-sfb-algebraic-group-homomorphism-factorization: the factorization theorem is the parent using this very item and cannot be used here; it produces an image group and a closed immersion, whereas the new result constructs a homogeneous scheme for a trivial-kernel map and supplies no closed-immersion conclusion.

## Review by Q102

I read Milne, Algebraic Groups (2017), Definition 5.20 and Proposition 5.24, printed pp.104–105; Theorem 5.28, p.105; Proposition 5.31 and the first proof of Theorem 5.34, pp.106–107. For the new node I also read the statement and beginning of the proof of Appendix B Theorem B.37, p.605, which expressly takes a monomorphism defined there by trivial kernel. Its statement, not the closed-subgroup special case following 5.28, supports the new node. Milne's definition gives the coset condition on affine tests; the scheme-test formulation follows by covering T with affines: local H-lifts are unique because the kernel is trivial (a quotient of two lifts lies in that kernel), hence agree on intersections and glue. It adds no unproved extra quotient properties. All group schemes in the application are of finite type over k; the hypothesis on u is on all algebras, including nonreduced ones. No SGA source is used.

Step 1 uses `def-sc-group-scheme`, whose statement defines the scheme-theoretic kernel fibre product, and `def-pc-fibre-product`, whose statement gives existence and the full test-object universal property. I opened both. The affine-local equality argument upgrades the given injectivity to every test scheme. The kernel's inclusion equals its identity-valued map, so the identity section and structure map are inverse by that universal property. This is an explicit elementary argument, not an invocation of an uncited representability theorem.

Step 2 uses the new trivial-kernel quotient node. Its statement introduces exactly H,G,i,X, the action and point, and explicitly gives the equality of coset fibres on every test scheme. With H=A,G=B,i=u all its hypotheses hold by the item and step 1. Setting the first group element equal to the identity gives exactly the fibre-over-o statement used later. No flatness, local lift or normal quotient claim is taken from this node.

Step 3 uses the opened `def-pc-fibre-product` universal property. Given a compatible pair of maps, step 2 gives a preimage and step 1 gives its uniqueness. Thus this square itself has the pullback universal property. There is no use of a mere topological fibre identification, no hidden isomorphism comparison lemma, and no new node is needed for this two-line universal-property check.

Step 4 uses `def-weil-affine-spectrum`, which states the affine ring/morphism correspondence and that Spec k has one point; `def-weil-closed-immersion`, which explicitly states the affine criterion with surjective ring maps; and `lem-weil-pbc-closed-immersion-base-change`, whose entire statement is precisely the projection assertion needed. I opened all three. I read Stacks morphisms.tex Tag 01QO (`lemma-closed-immersion`) and schemes.tex Tag 01JY (`lemma-base-change-immersion`), to which Tag 01QR refers. The proof explicitly checks both affine inverse-image cases, including the empty case Spec 0; the nonempty affine map fixes k and is surjective. Pulling it back along q proves closedness of u by step 3, without a separatedness hypothesis on the quotient. An isomorphic model of a cartesian square gives the same affine criterion, so there is no extra geometric permanence fact hidden in this identification.

For small cases I checked H trivial (the quotient is G with o the identity), i an isomorphism (the quotient is Spec k), nonnormal subgroups (the quotient needs only be a scheme with action, not a group), and infinitesimal subgroups such as mu_p in G_m. No reducedness or smoothness is used. Frobenius on G_a in characteristic p fails the all-algebras injectivity hypothesis when evaluated on k[epsilon]/epsilon^p, so is correctly excluded, even though field-valued injectivity alone would miss its kernel. These checks also show why replacing all test algebras by field-valued points would be wrong.

I checked delivery-errors B–E: every new object and hypothesis is introduced; definition dependencies are cited; TeX is single-escaped in decoded text; searches are actual logged calls with two semantic phrasings and inspected hits; the new node is statement-only and neither elementary nor a clause of the item; all cited node statements were opened, and citations.json quotes them verbatim. No step exceeds 2000 characters. The proof does not use the parent factorization or a closed-subgroup quotient, so it introduces no such cycle. The item statement and its statement dependencies are unchanged.

## Unfinished work

No unfinished work on this one-level split. The new quotient theorem is intentionally statement-only for a later stage-1 worker.

The first dry run passed. During final reading I corrected the allocation of the already-run semantic quotient searches into the new node (both phrasings are now recorded there), and corrected the representability theorem line number to 210. No mathematical statement or proof changed.
