# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cartesian-envelope-cocartesian-criterion.json`: statement, split in eight steps; Mathlib verdict no match. The statement, statement dependencies and inherited provenance are unchanged. Appended five actual searches from this sandbox, retaining the inherited searches.
- `citations.json`: an entry for every node used in every step, with verbatim statement text. The full envelope/straightening statements are included because their different clauses supply the different steps; the conventions quotes are the right-pinched mapping-space convention in step 1 and the homotopy-fiber construction in the path-pullback steps.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No unit record changes: this created foundation is not the unit's key statement. `write_split.py` is retained sandbox scratch, not a delivery file.

## Attachments

None. Searched the entire read-only `WeilConjectures/` tree for the item's blueprint tag/name and cartesian-envelope/cocartesian terminology, and the category-theory subtree for the ordinary terminology. There is no matching project declaration giving these infinity-categorical clauses. No upstream master sorry is treated as a finished proof.

## Wanted sources

WANTED: Chu--Haugseng, *Free algebras through Day convolution*, arXiv:2006.08269v2, Proposition 6.7(ii), Corollary 6.8 and Example 3.2, for lem-coef-cartesian-envelope-cocartesian-criterion. Read the online PDF, printed pp. 5 and 14-15; not present in the literature archive. No download or shared-file write was made. The source is not a Stacks result; no Stacks tag states this infinity-categorical proposition.

## What was wrong or missing

The item was an unsplit statement with no proof, not an already completed attempt. Its hypotheses and all its clauses agree with the cited source's cartesian special case. The general-pattern proof of Proposition 6.7 invokes a criterion for a functor between cocartesian fibrations; this delivery does not introduce that criterion as another node or transfer the whole item into it. Instead it verifies the mapping-space square directly from the already existing envelope formula. The proof is marked `proof_origin.by = agent` because this direct proof expands the cartesian special case rather than reproducing the source's general-pattern argument.

The phrase “cocartesian fibration” is read in the intrinsic convention explicitly provided by the item's existing statement dependency `lem-coef-cocartesian-straightening`. This convention includes equivalence to a simplicial representative after replacement over the base. We do not infer that the particular simplicial product-diagram functor is an inner fibration just from its universal mapping squares. This is a convention already stated in that dependency, not a change or weakening of the item.

The retained ancestor is `prop-coef-integral-exceptional-adjoint`, proof paragraph 2, the finite-coefficient mapping-complex adjunction before the derived limit. I read that proof in the current main-20261015 blueprint and the chapter and unit records. This item supplies the specific cartesian-envelope foundation for the existing coherent Day-model descendant, without changing the ancestor's integral adjunction route. No SGA source is used. No existing node was edited except the item copy.

## Search results and duplicate check

Read all five entries in the sandbox's `searches.jsonl`. Loogle queried `CategoryTheory.Functor.IsFibered`; LeanSearch queried the cocartesian block criterion; LeanFinder used two distinct phrasings, one about induced product-preserving fibrations and one about finite tuples and product-then-transport lifts. The prescribed grep searched cocartesian terminology and cartesian envelopes in `CategoryTheory`. All services answered successfully. Hits concern ordinary fibered categories or ordinary cartesian monoidal categories. Read `FiberedCategory/Cocartesian.lean:48-77` and `Monoidal/Cartesian/Basic.lean:937-969`: their types use ordinary categories and hom sets; they do not give this quasicategorical envelope theorem as an exact match or one-line specialization. No match was recorded as unavailable, and no unrun query was added.

Searched the whole DAG for cartesian envelopes, cocartesian mapping criteria and the source identifier; opened the existing envelope, straightening, mapping criterion, product-diagram recognition, pointwise transport, and related statements before selecting dependencies. Whole-blueprint searches for `cartesian envelope`, `cocartesian`, and `finite-product` produced no equivalent imported blueprint statement. The first two had zero results; the last gave ordinary sheaf coefficient constructions. The ancestor command confirms the existing blueprint ancestry. The current item remains `same_as: []`. No new nodes were needed, so there are no new/existing pairs to distinguish.

## Review by N0

I checked the entire B-E checklist with the item, cited statements and source open. The source's Corollary 6.8 has exactly finite products in E and B, preservation of those products, and binary stability of cocartesian edges. Proposition 6.7(ii) gives the lift as monoidal transport followed by fiberwise cocartesian transport, which is precisely block product followed by p-transport here. Example 3.2 gives the ordered interval blocks. The eight steps establish the extra “if and only if” assertion as well, instead of citing the corollary for something it does not explicitly state. There are no new statements to check for B1-B8, and neither a clause of the item nor an elementary product fact was made a new node.

Step 1 uses `lem-coef-cartesian-operadic-envelope` for the induced coherent functor, the displayed mapping-space formula and its substitution law. I checked all three occur in its statement. It uses `lem-coef-cocartesian-straightening` for the intrinsic definition and the comparison with a replacement, both explicitly stated there. The right-pinched mapping convention in `def-cbc-enhanced-diagrams-cones` makes the decomposition by discrete pointed maps direct: the entire initial face is constant, so there is one final arrow label in every simplex. The product comparison applies because p preserves every finite product, including the empty one.

Step 2 is elementary induction from the item's binary hypothesis. Its nullary case is the identity of the terminal object, whose mapping square has horizontal identities, using exactly the intrinsic criterion quoted from straightening. This checks the possible missing nullary hypothesis rather than adding one. The convention does not claim arbitrary arrows out of a terminal object are cocartesian.

Step 3 uses the same straightening square for each finite product of the u_j. The envelope node's composition statement identifies precomposition on each beta summand with those products; it is not being cited merely as a definition of an envelope. The product of path pullbacks is their coordinatewise path pullback, by the explicit path-space construction in the convention node. The comparison is the product of the comparison equivalences. The regrouping uses disjoint inverse images of distinct non-basepoints, so it introduces no diagonal or repeated input and uses no distributivity hypothesis on E or B.

Step 4 uses that same path-pullback construction and the envelope decomposition to assemble the beta summands. I checked the subtle case where beta -> beta alpha is not injective: beta remains part of the lower-left map data in the path pullback, so different beta labels are not identified. Paths cannot cross discrete labels. The resulting total square is exactly the square required by straightening, for every test tuple. This establishes sufficiency, rather than asserting a comparison without its argument.

Step 5 tests necessity with a one-term target and the inert projection selecting j. The envelope statement gives precisely Map(f_j,z) and Map(x_j,z) on those two labels; no inaccessible proof construction of a cited node is used. Restricting the total comparison to these discrete summands recovers the intrinsic square for u_j for every z. Thus the cited straightening statement applies with all its hypotheses. For s=0 necessity is empty and sufficiency already handled it.

Step 6 applies the assumed lifting property of p to the actual object x_j and the base arrow obtained using p's product-preservation equivalence. The straightening statement explicitly includes the lifting property; the envelope statement explicitly realizes tuples of block maps as the relevant mapping space. This gives the stated target tuple and lift, with the base identification retained. It uses no unsupported strictification or extra inner-fibration assertion. The already constructed coherent functor supplies its higher simplices; a binary argument is not used to assert a new coherent functor.

Step 7 is an elementary computation of the ordered-block functor, including identities, composition, empty intervals and discarded indices. The union for a composite has endpoints a(b(k-1)) and a(b(k)); inputs outside the retained ranges are discarded in both composites. This agrees with Example 3.2, and needs no separate lemma node.

Step 8 uses straightening's explicitly stated base-change compatibility and identification of transports. The comparison E_F = E^times x_(B^times) B_F is the direct description of the two pullback data, not an additional descent theorem. The envelope mapping formula over an ordinal label and the same discrete-label path calculation prove the criterion in this pullback. In particular necessity still has the singleton test, using the opposite map [1] -> [s] selecting j-1,j. This avoids assuming that a generic functor reflects cocartesian arrows.

I tested r=0, s=0, t=0; a constant ordinal map; an empty alpha-block; a beta that discards one or all outputs; the identity fibration; and E -> * for a finite-product category. In the last case p-cocartesian means equivalence, and the criterion becomes exactly the envelope node's equivalence-of-blocks criterion. When s=0, all arrows to the empty tuple are cocartesian; when r=0 and s>0 the blocks start at 1_E and still require the specified p-cocartesian transport. No nonemptiness, presentability, colimit, or product-preservation-by-transport hypothesis was used. No statement dispute was found. Each proof step is below 2000 characters; the coordinatewise product and discrete-label calculations are routine arguments written explicitly, not hidden general lemmas. All uses occur in proof_deps, and every use has a literal statement quote in citations.json. No cycles, duplicate nodes or off-unit statement tools are introduced; the only off-unit dependency is a definition/convention node.

## Unfinished work and validation

Mathematical split complete. Server `check_dag` reported no finding introduced by the sandbox or on its nodes, and `review_split` reported PASS with 0 new nodes. The required `deliver.py N0 lem-coef-cartesian-envelope-cocartesian-criterion --no-push` printed OK (not pushed), with preflight passed and a durable stage-1 dry-run receipt saved. A final repeat follows this validation-note update and the more specific step-1 quotation. No push was made. The accepted sandbox is for a fresh second reader to deliver.
