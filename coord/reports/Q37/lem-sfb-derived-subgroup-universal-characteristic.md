# Q37: lem-sfb-derived-subgroup-universal-characteristic

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-derived-subgroup-universal-characteristic.json: statement, split; no Mathlib match. Four proof steps, nine step/node citation entries, zero new nodes, zero new Mathlib leaves.
- citations.json: exact excerpts from the statements of all nine step/node citations.
- report.md: this report. searches.jsonl was produced by the authorized msearch command.

## Attachments

No project declaration states the complete item. Searched WeilConjectures for the blueprint tag, derived subgroup/derivedSubgroup, commutator, characteristic and group-scheme terminology. GeneralLinear/ClosedSubgroup.lean:456–545 constructs a derived ideal and proves its minimality for embedded groups; it does not state invariance after arbitrary algebra extension and is not an attachment of this item.

TensorProduct.eq_zero_of_forall_rTensor_eq_zero belongs to lem-sfb-vector-space-tensor-family-zero-detection (existing node), WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basis.lean:32. Read its entire sorry-free proof at lines 32–48. The existing DAG node already records this declaration; no edit to that node is delivered.

## WANTED

None. Milne Algebraic Groups (2017) and the Stacks source needed here are present locally.

## Corrections and route

The mathematical statement is retained with every original hypothesis and with arbitrary commutative base algebras, including nonreduced and infinitely generated algebras. The imported statement contained doubled literal TeX backslashes; these have been reduced to single TeX escapes. This is a rendering correction, not a statement dispute.

Milne Corollary 6.19(e), printed pp.129–130, proves characteristic invariance via its faithfully flat point description in (c). I read that proof and Proposition 6.18. Instead of creating a new node for (c), the split uses the existing coordinate-ring generated-subgroup theorem (Milne 2.46, printed pp.54–55) and existing vector-space tensor-family zero detection. It proves the same scheme-theoretic assertion by a kernel computation. This is a choice below the unit level, and adds no new assumption or replacement of the constructibility unit's route.

The inherited blueprint ancestor is null, confirmed by blueprint_refs.py ancestor. Its detailed inherited from.place is retained. Read latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). Searches across the blueprint for derived subgroup, commutator and characteristic subgroup found no node stating this item. The five commutator hits concern monodromy, product reducedness and Lie algebra terminology; none asserts arbitrary-algebra characteristic invariance. No chapter or unit file is changed.

The existing affine-spectrum and affine-fibre-product statements are used as generic tools, declared in split_report.tool_uses. Finite-type composition/base-change is an existing Mathlib leaf. No SGA source is used.

## Mathlib searches

Ran msearch for this item with LeanFinder, Loogle, grep restricted to AlgebraicGeometry, and LeanSearch; ran a second LeanFinder phrasing explicitly mentioning a nonreduced commutative base ring. Read every output and reused the command's JSON log as the record of exact queries. All services answered successfully. Semantic searches found instCharacteristicCommutator, Subgroup.commutator_characteristic and derivedSeries_characteristic for abstract groups, and the second phrasing found formally unramified base-change properties and geometrically reduced rings. None identifies this subgroup scheme after arbitrary algebra extension. Read GroupTheory/Commutator/Basic.lean:315 and 380–405, GroupTheory/Solvable.lean:68–71, and AlgebraicGeometry/Group/Abelian.lean:40–65: these are abstract-group characteristic subgroups or proper group scheme commutativity, not the item. Existing inherited searches are preserved and fresh searches appended; no search is invented or recorded as unavailable when it succeeded.

## Not duplicates

No new nodes are created. For clarity about the item: lem-sfb-smooth-connected-derived-subgroup only constructs the derived subgroup over an algebraically closed field and identifies field-valued points; lem-sfb-smooth-connected-relative-commutator constructs a relative subgroup but does not assert automorphism invariance after arbitrary algebra extension. lem-sfb-derived-commutator-word-arbitrary-field constructs the item’s D(H), gives a dominant word and field-extension compatibility, but does not cover automorphisms over arbitrary base algebras. The generated-subgroup construction and tensor-family zero-detection nodes are cited, not duplicated.

## Review by Q37

I read Milne 2.46–2.48 (printed pp.54–55), 6.18–6.20 (printed pp.129–130), the complete statement of each cited node, and the project tensor-family theorem. The sources give the coordinate construction and the commutator identity; the additional arbitrary-algebra kernel argument is explicitly marked agent-written.

Step 1 uses affine fibre products to make X=H×H affine, finite-type composition/base-change (Stacks Tags 01T3, lemma-composition-finite-type, and 01T4, lemma-base-change-finite-type, read in morphisms.tex:2711–2750) to check finite type of X, and the pointed-map generated-subgroup statement for C=P/intersection ker(w_n*). Its hypotheses are checked: H is affine finite type, (e,e) is a rational point, c(e,e)=e, and swapping the two arguments gives the inverse of a commutator over every algebra. The existing arbitrary-field derived-word statement identifies its D(H) by the same smallest-closed-subgroup property, without taking anything from that node's proof. Joint zero detection is then the definition of the displayed intersection. No smoothness or connectedness conclusion is smuggled in from a definition.

Step 2 uses the affine fibre-product statement for coordinate base change. Functoriality is checked on pure tensors, and the tensor-product definition says pure tensors generate, allowing the explicit lift of finite sums proving q_A surjective. The existing zero-detection theorem has exactly the family hypothesis proved in step 1 and applies with M=C and N=A: every k-algebra is a k-vector space, with no finite-dimensionality assumption. This avoids exchanging an infinite intersection with tensor product. The quoted statement includes arbitrary index sets and infinite-dimensional spaces, so it really covers every A here.

Step 3 is the written group-word identity on the universal tuple over B_n,A. The affine-spectrum node actually states the correspondence between affine morphisms and ring maps, which justifies passing to pullbacks and constructing the restriction. For z in ker(q_A), the equality f_n,A q_A u*=U_n* f_n,A q_A makes every f_n,A kill q_Au*(z); step 2 then kills that element itself. Well-definedness of the descended algebra map is checked using this kernel inclusion and the surjectivity already proved. There is no inference from topological containment to scheme factorization and no passage merely to field-valued points.

Step 4 repeats the established argument for u inverse, cancels the surjective coordinate map, and checks the group operations via injection on points over every A-algebra. It therefore obtains a group-scheme automorphism of the specified subgroup, and equality as closed subgroup schemes, rather than only invariance of a set of points. The affine-spectrum citation says what cancellation of the corresponding ring maps needs. The elementary marking is limited to these explicit identities and the descended-map construction; the non-elementary construction and tensor theorem occur in steps 1–2 with citations.

I tested H=1, H commutative (including Ga and tori), imperfect and finite fields, and A=k[epsilon]/(epsilon^2), a polynomial algebra with infinitely many generators, and A=0. In the first cases D=1 and the restriction fixes the identity. Nilpotents of A are preserved throughout the coordinate computation, and no property of A other than being a vector space over k is used. For A=0 every tensor coordinate algebra is zero and all the identities hold on the empty base changes. No assumption that u descends to k is used; it is only an A-algebra automorphism on P_A. This addresses the key distinction from invariance under k-automorphisms.

I checked B–E: no new statement-only nodes or uncited helper lemmas are hidden, every cited statement is used with its actual hypotheses, no clause is shifted into a renamed node, all nine citation quotes are verbatim, and all four steps are below 2000 characters. No mathematical statement needed correction. The only correction was inherited TeX escaping.

## Unfinished work

None in the split. Delivery validation and push are performed by the prescribed deliver.py commands; no Lean file is written or compiled.
