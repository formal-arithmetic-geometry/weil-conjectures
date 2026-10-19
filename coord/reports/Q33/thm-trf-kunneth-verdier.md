# thm-trf-kunneth-verdier — Q33 stage-1 split

## Files written

- `dag/nodes/sec-six-functors/thm-trf-kunneth-verdier.json`: existing statement, split into four steps; eight actually logged Mathlib searches, no match.
- `citations.json`: nine verbatim statement excerpts covering every step/use pair.
- `report.md`: this report.

## New nodes

None. There are zero new nodes and zero Mathlib leaves. The proof uses the existing external-Hom and exceptional-Kunneth propositions; the input checks and inverse calculation are elementary steps, not new lemmas.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, Kunneth/Verdier names and the comparison maps. `AlgebraicGeometry.Etale.hasKunnethComparisons`, `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Comparisons.lean:163`, has `sorry` at line 166. Furthermore, its current interface gives `Nonempty` isomorphisms rather than invertibility of the specified canonical morphism. It cannot attach this node. The pro-etale definition `AlgebraicGeometry.ProEtale.GeometricOperations.kunnethVerdier`, `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Defs.lean:1048`, takes a geometric-operations package whose field `isIso_kunnethVerdierMap` (line 825) already supplies the needed conclusion; it is not an unconditional proof under this item's hypotheses. Neither the upstream master nor its sorry declarations were used as finished-proof evidence.

## WANTED

None. The blueprint statement, proof, comparison-map definition and both comparison propositions are present in the current snapshot.

## Corrections and scope

The statement is unchanged, with the finite-field/coefficient datum inherited through `def-trf-dualizing-complex`. The original single paragraph skipped the reason that the dualizing complex is a valid input to external Hom. Step 1 now checks it: the coefficient unit has amplitude zero, and the assumed exceptional adjoint has source and target the constructible finite-Tor subcategories. This uses the explicit functor type in `def-trf-admissibility`, not a general assertion that any dualizing complex is tensor-dualizable. The identity exceptional adjunction is elementary.

The old proof loosely attributed the identification `M ⊠ omega_Y = p_X^! M` to a definition. The actual isomorphism now comes from the statement of `prop-trf-exceptional-kunneth`, with `def-trf-dualizing-complex` used only for `omega_Y = Ra_Y^! A_s`. The final step identifies the *specified morphism*, not merely its source and target, through `def-sf-kv-maps` (iv) and writes its inverse explicitly.

The current source is `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/thm-trf-kunneth-verdier.md` and its `.proof.md`; the current statement and the old imported statement agree. The proof origin and each step now point at the current proof file. No SGA source or purity route was introduced. No statement dispute was found.

The item is the kappa component of unit `sk-thm-sf-kunneth-verdier`, whose key node is the separate node with the unit's own id; this delivery does not claim to complete that unit or edit its realization fields. It realizes exactly that unit's third proof paragraph. The existing alpha and beta propositions stay in that same unit. The other cited nodes are definitions, so no off-route theorem/tool citation is needed.

## Not duplicates

No new node pairs to justify. Whole-DAG and whole-blueprint searches used `tools/blueprint_refs.py ancestor thm-trf-kunneth-verdier` and searches for `external Hom`, `exceptional Künneth`, `Künneth–Verdier`, `kappa`, and `dualizing complex`, together with full-DAG text/statement searches. The broader `sk-thm-sf-kunneth-verdier` asserts alpha, beta and kappa together, and its kappa clause is the unit-level version of this item; it is not the same complete statement, so `blueprint.same_as` is empty. `def-sf-kv-maps` and `sk-def-sf-kv-maps` construct the maps and explicitly defer invertibility to theorems; they do not prove this assertion. The two existing comparison propositions are reused rather than re-created.

## Mathlib search review

All eight records come from `msearch.py` and their exact tool/query texts and actual hits are retained in `mathlib_searches` and `searches.jsonl`. Both semantic services were available. Two formulations were tried with LeanFinder and two with LeanSearch, plus Loogle and two grep searches (the second in `AlgebraicGeometry`). LeanFinder first returned rigid-category tensor/Hom equivalences and then ordinary structure-sheaf module adjunctions and condensed projectivity; their displayed types do not concern the constructible exceptional inverse image. Loogle returned closed/cartesian monoidal comparison lemmas and Day reflection, which do not imply geometric exceptional Kunneth. LeanSearch returned external products of functors, Kan extensions and basic etale sites rather than this assertion. Both targeted source greps had zero hits. No result was promoted to a Mathlib leaf.

## Review by Q33

I read delivery-errors B through E whole, the three-level rule, the chapter and unit records, and the current main-20261015 item statement and proof. I also read the current source statements of `prop-trf-external-hom`, `prop-trf-exceptional-kunneth`, and `def-trf-dualizing-complex`, and opened the complete DAG statements of all five nodes cited by the split. For the comparison definition and admissibility I read the `blueprint_update` as well as the stored statement; the clauses used agree. No new node has a source or statement left to review.

Step 1 uses the displayed type `Rf^!:D^b_ctf(Y,A) -> D^b_ctf(X,A)` of `def-trf-admissibility` and the displayed construction of omega in `def-trf-dualizing-complex`. The latter alone does not assert preservation, so the former is cited explicitly. The coefficient unit is the free rank-one module in degree zero; constructibility and amplitude zero follow directly. These checks supply precisely the missing fourth input to beta, without adding a hypothesis on Y or changing coefficient categories.

Step 2 takes the actual beta isomorphism, with all four inputs in ctf, from the *statement* of `prop-trf-external-hom`. X and Y are separated and finite type as required. The dualizing definition identifies the second internal Hom with D_Y N. The two unit identifications and the choice of the pairs are explicitly in `def-sf-kv-maps` (iv), which was checked against the cited formula; the step does not ask a fully-faithfulness statement or definition for an invertibility theorem.

Step 3 takes the actual canonical alpha isomorphism from the *statement* of `prop-trf-exceptional-kunneth`, specialized to id_X and a_Y with inputs M and A_s. The identity case has the identity adjunction; a_Y and p_X have the exceptional adjoints stipulated by the item. Their source and target schemes are separated finite type over the same fixed field. The product target X times s is X and the second exceptional input is omega_Y by its definition. Definition (iv) specifies exactly this alpha for the comparison used here. This repairs the original paragraph's misleading attribution of the isomorphism to the dualizing definition alone.

Step 4 uses the exact composite in `def-sf-kv-maps` (iv). Applying the internal-Hom functor to a and its inverse preserves the two inverse identities. Composing with b and its inverse then checks both identities directly. This is an elementary functor-and-inverse calculation, with no uncited geometric theorem concealed in it.

For B, no new nodes need standalone definitions, tags or leaf line checks; JSON uses single TeX escapes after decoding and preserves the imported metadata. For C, every non-elementary assertion is one of the two cited comparison statements; every use has a verbatim citation entry, and no proof-internal construction of a cited node is used. For D, the item's steps perform the beta/alpha specializations and inverse calculation themselves; nothing was moved into a replacement node, and no induction or new dependency cycle is introduced. For E, I checked the finite-Tor input hypotheses, base field and same coefficient ring, the product projection orientation, and the canonical-map identity. If M or N is zero both source and target are zero and the argument still applies. If Y=s the construction reduces to the unit and tensor/Hom comparison, with no exceptional dimension shift; if either scheme is empty the same zero-object calculation applies. No smoothness, properness, regularity or tensor-dualizability of omega_Y is being tacitly assumed.

## Unfinished work

No part of this one-level split remains unfinished. The existing comparison propositions remain separate DAG tasks. The sandbox is for the second reader; nothing is pushed by this worker.

## Dry-run repair

The first dry run rejected the step-1 admissibility quote solely because its displayed functor type was fewer than 40 characters. I extended that verbatim excerpt to include “has a specified right adjoint”; the node, proof and dependencies needed no mathematical change.


## Earlier second reading (a previous round; superseded)

I independently read `coord/delivery-errors.md` B–E, `GOAL.md`, `coord/dag-sync.md`, the stage-1 contract, the chapter and unit records, and the current `main-20261015` blueprint statement and proof. The item has no Stacks-tag source: its source is the blueprint's `sec-six-functors/sk-thm-sf-kunneth-verdier/thm-trf-kunneth-verdier.md` and `.proof.md`. I compared the actual statements of all five cited nodes, including the current `blueprint_update` for admissibility and the map definition, rather than treating their proof bodies as available facts.

- Item statement: matches both snapshot statements verbatim after removing front matter; the common base is the fixed geometric finite field through `def-trf-dualizing-complex`, the ring is the same finite coefficient stage, both schemes are separated finite type, the structure map and product projection have the stipulated constructible exceptional adjoints, and the conclusion concerns the specified canonical map. PASS; no statement dispute.
- Step 1: checked against the displayed adjoint type in `def-trf-admissibility`, the formula for omega in `def-trf-dualizing-complex`, and the definitions `def-weil-finite-tor-amplitude` and `def-weil-finite-torsion-constructibility`. The constant coefficient sheaf is finite locally constant, and tensoring its degree-zero rank-one free complex with a degree-zero sheaf gives that sheaf in degree zero. Thus its amplitude is [0,0], and the assumed adjoint places omega in ctf. The identity adjunction supplies the identity exceptional inverse image. PASS; elementary input checks, without a claim that arbitrary dualizing complexes are tensor-dualizable.
- Step 2: checked the four-input beta statement of `prop-trf-external-hom` and its source `prop-trf-external-hom.md`, the dualizing formula, and `def-sf-kv-maps` (iii)–(iv) with its current source. The choices are exactly (A_X,M) and (N,omega_Y); step 1 supplies both additional ctf inputs, and X,Y meet the separated finite-type hypotheses. The definition supplies the two unit identifications and identifies this beta with the first arrow of kappa. PASS; extended the citation quote to include those exact unit identifications and input pairs.
- Step 3: checked the canonical alpha statement of `prop-trf-exceptional-kunneth` and its source `prop-trf-exceptional-kunneth.md`, the dualizing formula, and `def-sf-kv-maps` (ii),(iv). Its inputs are id_X:X→X and a_Y:Y→s, with coefficients M and A_s; their product is p_X:X×_sY→X×_ss≅X. The identity, a_Y and p_X have precisely the exceptional adjoints needed; the target coefficient becomes M and the second source coefficient becomes omega_Y. PASS; this supplies the canonical alpha, not merely some isomorphism between its endpoints.
- Step 4: checked against `def-sf-kv-maps` (iv) and the two preceding isomorphisms. For H=RHom(p_Y^*N,-), functoriality gives H(a^{-1})H(a)=1 and H(a)H(a^{-1})=1. Therefore (b^{-1}H(a^{-1}))(H(a)b)=1 and (H(a)b)(b^{-1}H(a^{-1}))=1, with both expressions well typed. PASS; the entire remaining calculation is elementary and proves invertibility of the specified composite.
- New nodes: none, as confirmed by the sandbox file list. No new definition, duplicate, restatement, elementary lemma or purported Mathlib leaf needs B1–B8 repair. Both non-elementary results are existing nodes of this unit, and the other citations are existing definitions. PASS; no off-route theorem is introduced.

Small cases: M=0 or N=0 makes the relevant internal Hom or exceptional image zero and both maps remain isomorphisms; an empty X or Y gives the same zero calculation. For Y=s, a_Y is the identity and omega_Y=A_s, so alpha specializes to the unit identification. For X=Y=s and n=1 the statement specializes to the ordinary finite-dimensional tensor/Hom formula over the residue field. At n>1 the proof still requires finite Tor amplitude explicitly and does not infer it from constructibility. The coefficient convention has n≥1, so n=0 is not a missing case. No properness, smoothness, regularity, algebraic closedness of coefficients, or stronger ambient-adjoint datum was added.

I also reopened `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Comparisons.lean`: `hasKunnethComparisons` at lines 163–166 ends in `sorry` and the kappa field at lines 135–147 asserts only `Nonempty` of an isomorphism. The ProEtale `kunnethVerdier` at lines 1048–1059 obtains invertibility from the package field `isIso_kunnethVerdierMap` at line 825. Neither is an unconditional finished proof of this canonical-map statement, so no attachment is warranted. No compiler was run.

Changes made: extended the step-2 `def-sf-kv-maps` quote in `citations.json` through the unit-identification paragraph, because the original quote showed the composite but omitted those identifications used in that step; ran an independent LeanFinder query phrased in terms of internal Hom preserving isomorphisms and the product formula, recorded its actual eight hits in `searches.jsonl` and `mathlib_searches`, and rejected them after reading their displayed types (light condensed internal Hom, sheaf pullback units, and general monoidal categories, not this geometric comparison); appended this second reading. The statement, four proof steps, dependencies and first worker's review are retained. All nine citation quotes were checked as verbatim substrings, and their step/node pairs cover every proof use. There are still zero new nodes and zero Mathlib leaves.

Validation: the first second-reader dry run was rejected because its commit was no longer on the server current base; the resulting diff included `coord/blueprint-index.tsv`, `coord/queue.md`, and `coord/queue.tsv`, none present in this sandbox. Re-running the required delivery tool rebuilt from the refreshed base and printed `OK (not pushed) deliver/Q33/thm-trf-kunneth-verdier at 904a5d65bf: preflight passed`. No validator was run directly on this machine.

## Repair of returned delivery

The landing return identified one stale citation: `def-trf-admissibility` had
changed after the reviewed delivery. I rebased the validation against the
current DAG copy at `dag/nodes/sec-smooth-purity/def-trf-admissibility.json`,
read its complete revised statement, and replaced the step-1 quote with the
verbatim finite-level adjunction clause (including the two restricted functor
types, unit and counit, triangle identities, exchange isomorphisms, and the
specified constructible-functor qualification). The step still uses only the
fact that admissibility supplies `Rf^! : D^b_ctf(s,A) -> D^b_ctf(Y,A)`; the
revised statement says this explicitly. I rechecked every other citation
against the current DAG statements; the other eight excerpts remain verbatim and support the same uses. In particular, the dualizing definition is now an expanded, reviewed definition with an ambient-valued contravariant Verdier-dual functor; the split uses only its formula for omega and D_Y, and never asserts that D_Y preserves ctf.


## Review by Q33 — returned-citation repair

The returned head is `e2d451d154`; I used the retained split and report from
that delivery as the starting point and compared its item with the current
shared DAG. The item's statement and imported route metadata agree; the
reviewed split is still absent from main, whose item remains imported.
The change that caused the return is visible directly in the failed old
quote: the old wording “has a specified right adjoint” is no longer in the
current admissibility statement. I read the full revised statement and its
current main-20261015 source in `sec-six-functors-basics/sk-def-sf-admissible/`.
It now explicitly names the restrictions of both specified constructible
functors, their adjunction and triangle identities, the precise conjugate
base-change map, and signed uniform bounds. Only the restriction's source
and target are needed here; no base-change or uniform-bound claim is used
by this split.

For step 1 I rewrote the actual proof text, as well as its quote: the unit
is constructible because it is locally constant with finite stalk A, and
its derived tensor with every degree-zero sheaf is that sheaf, proving
Tor amplitude [0,0]. Applying the explicitly restricted constructible
Ra_Y^! to A_s gives omega_Y in ctf. The current dualizing definition's
formula identifies the value, and does not itself supply a preservation
theorem. This is exactly the same finite-stage A_{E,n} category on both
sides. No unrestricted ambient exceptional adjunction is inferred. The
identity exceptional inverse image and identity adjunction still give
the remaining identity-factor specialization.

I reopened the complete current statements of the other four cited nodes
and their main-20261015 sources. Step 2 still takes the evaluation-defined
beta isomorphism from prop-trf-external-hom with (A_X,M) and (N,omega_Y),
all four inputs now checked by step 1. Step 3 still takes canonical alpha
from prop-trf-exceptional-kunneth with id_X and a_Y; its product is p_X,
so the orientation and exceptional inputs agree with the statement.
The updated dualizing definition is used only for its displayed omega and
D_Y formula. In steps 2–4, def-sf-kv-maps (iv) still specifies the same
unit identifications and exactly H(alpha) composed with beta. Step 4's
inverse is b^{-1} composed with H(a^{-1}); applying functoriality and the
two inverse identities verifies both composites. None of these uses needs
a proof-internal assertion from a cited node.

The whole B–E review remains satisfied: no new node, Mathlib leaf, source
tag, off-route theorem or dependency is added; the argument stays in the
unit's kappa paragraph. The input checks are elementary and the two
non-elementary assertions remain the existing alpha and beta propositions.
I checked again M=0, N=0, an empty factor, and Y=s; the argument retains
its zero-object and unit specializations. At n>1 it uses the finite-Tor
restriction explicitly rather than deriving it from constructibility.
The statement and hypotheses are unchanged, and no source dispute arises.
All nine step/use pairs now have current verbatim excerpts of at least
40 characters. The required delivery tool rebuilds this repaired split on
the current origin/newtargets-dag; only a dry run is authorized for this
worker, leaving final delivery to the fresh second reader.

## Earlier second reading by Q33 — before product-map return

- Item statement: checked against `main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/thm-trf-kunneth-verdier.md`; all scheme, coefficient, admissibility, projection, and comparison-map hypotheses agree; PASS.
- Step 1: checked against the current statements of `def-trf-admissibility` and `def-trf-dualizing-complex`; the restricted exceptional functor puts `\omega_Y` in the finite-Tor constructible category, and the unit inputs have degree-zero finite Tor amplitude; PASS.
- Step 2: checked against `prop-trf-external-hom`, `def-trf-dualizing-complex`, and clause (iv) of `def-sf-kv-maps`; the four inputs, pair specialization, unit identifications, and first `\kappa` arrow are exactly supported; PASS.
- Step 3: checked against `prop-trf-exceptional-kunneth`, `def-trf-dualizing-complex`, and clause (iv) of `def-sf-kv-maps`; the identity and structure morphism specialize to `p_X`, with the required admissibility and `\omega_Y`; PASS.
- Step 4: checked against clause (iv) of `def-sf-kv-maps`; functoriality sends the displayed inverse pair to identities, so the explicitly specified composite is invertible; PASS.
- New nodes: none; the existing external-Hom and exceptional-Kunneth propositions are reused, so B1–B7 and Mathlib-leaf checks are vacuous.
- Edge cases: zero objects, an empty factor, `Y=s`, and the unit/field specialization retain the claimed isomorphism; no extra smoothness, properness, or coefficient hypothesis is used.
- Changes made: added this required second-reader section and retained the worker's expanded four-step proof, current admissibility citation, nine verbatim citation entries, and eight recorded no-match searches; no mathematical or node-file change was needed.


## Repair of product-map landing return (2026-10-17)

The present return names `def-sf-kv-maps`, rather than the admissibility
return repaired in the preceding round. I retained that round's node,
proof, report, citations and all eight logged searches. Comparing the
retained item with the current shared DAG shows that the item statement,
statement dependencies and imported route metadata agree; the current item
is still imported. The authorized delivery tool rebases the sandbox's split
fields onto current `origin/newtargets-dag` in its temporary worktree.

I compared every retained citation with the current statement it names.
The six excerpts from admissibility, the dualizing definition, external
Hom and exceptional Kunneth still occur verbatim. All three excerpts from
`def-sf-kv-maps` fail: the revised definition now writes derived pullback
explicitly, uses canonical unit isomorphisms, expands the geometric
operation and finite-Tor domains, and explains the identity/structure-map
specialization. I replaced those three excerpts with current verbatim
text. The step-2 excerpt also includes the finite-stage identification,
so it supports the new coefficient clarification as well as beta's inputs.

The node itself is repaired, not merely rebased: step 2 now explicitly
restricts the multi-stage map definition to Lambda=A=A_{E,n}, identifies
its Verdier dual with D_Y through the identical RHom formula, interprets
p_Y^* as derived pullback, and uses unit isomorphisms instead of literal
equalities. Step 3 uses the canonical target-base identification
X times_k s isomorphic to X and the exact specialization stated in current
clause (iv). Step 4 applies internal Hom with the displayed derived
pullback. The statement and its finite-coefficient scope are preserved.

## Review by Q33 — product-map citation repair

I reopened the complete current DAG statements of all five cited nodes,
and read the main-20261015 statement and proof of this item, the unit's
kappa paragraph, the current snapshot sources for both comparison
propositions and the dualizing definition, and the current map-definition
and admissibility source texts (including their stored blueprint updates).
The revised DAG definition of the maps is a more explicit construction
than its snapshot text: clauses (ii), (iii), (iv) still specify respectively
the adjoint-of-counits alpha, transpose-of-evaluations beta, and the same
kappa composite. Its wider coefficient list is specialized to its stated
finite stage; neither integral nor field operations are substituted for A.
No new node or new source is introduced.

Step 1 still uses exactly the restricted exceptional-adjoint functor type
in `def-trf-admissibility` and the omega formula in
`def-trf-dualizing-complex`. The rank-one constant coefficient sheaf is
constructible and its tensor with a degree-zero sheaf is that sheaf, so
it has amplitude [0,0]. Thus omega_Y is a valid fourth input. The updated
map definition independently agrees on this unit and finite-stage datum.
The dualizing definition is used for its formula, not an unproved claim
that its contravariant functor preserves the small category.

Step 2 cites `prop-trf-external-hom` for precisely its evaluation-defined
beta isomorphism with the four ctf inputs (A_X,M,N,omega_Y).
`def-trf-dualizing-complex` identifies D_YN; current `def-sf-kv-maps` (iv)
identifies the two pairs, unit isomorphisms and first arrow. Its finite
coefficient paragraph expressly identifies the geometric adjunctions with
the finite-stage datum, so this step does not change categories. The
notation Lp_Y^* agrees with the derived p_Y^* of the item.

Step 3 cites `prop-trf-exceptional-kunneth` for the canonical alpha, with
id_X and a_Y and coefficient inputs M and A_s. The identity adjunction
handles id_X; a_Y and p_X have the datum assumed by the item. All schemes
are separated finite type over the same k; the target base is
X times_k s, canonically X. The dualizing formula identifies a_Y^!A_s.
Current clause (iv) explicitly states all four substitutions and the
product morphism p_X, and clause (ii) fixes the geometric counits used.
Consequently this is the actual second comparison in kappa.

Step 4 cites the current displayed kappa composite and applies the
functor H=RHom_A(Lp_Y^*N,-) to alpha and its inverse. The inverse is
b^{-1} composed with H(alpha^{-1}); both composite identities follow by
functoriality and cancellation. No geometric lemma is concealed here.

I rechecked delivery-errors B--E against these statements: no new node,
duplicate, Mathlib leaf, off-route theorem or source tag is added; the
proof carries the specializations and inverse calculation rather than
moving its conclusion into a child. Every cited non-elementary fact is
an actual comparison-isomorphism statement, and all nine step/use pairs
have verbatim supporting text. I tested zero M, zero N, an empty factor,
Y=s, and X=Y=s at n=1; the maps retain their zero/unit cases. At n>1 the
finite-Tor hypothesis is still explicitly used, not inferred from
constructibility. No new statement dispute is needed. Searches were
read from searches.jsonl and retained without repetition because neither
the item statement nor the search question changed. I also reopened the
Lean comparison declarations: the etale package remains sorried, and the
pro-etale isomorphism still takes its invertibility from a package field,
so neither is an attachment under this item's hypotheses.

The earlier second readings above describe earlier delivery heads; this
worker's repaired sandbox is to receive a fresh independent second
reading after the required dry run. Nothing is pushed by this worker.


## Second reading by Q33

This is the fresh independent reading of the product-map return repair, after the worker's final section above. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 contract, the current chapter/unit records, the main-20261015 item statement and proof, and the current complete statements of all five cited DAG nodes. The source of this item is the blueprint, not a Stacks tag; there are no new Stacks-sourced nodes to check. The current map and admissibility definitions were compared both with their snapshot sources and with their stored blueprint updates. The current expanded definitions retain the specific finite-stage adjunctions and the same alpha/beta/kappa constructions.

- Item statement: checked hypothesis by hypothesis against main-20261015 `sec-six-functors/sk-thm-sf-kunneth-verdier/thm-trf-kunneth-verdier.md`; the sandbox statement also equals the current shared DAG statement. Same finite-field datum, A=A_{E,n}, separated finite-type factors, constructible finite-Tor inputs, exceptional adjoints for a_Y and p_X, and specified canonical comparison. PASS; no statement dispute.
- Step 1: checked against the actual restricted functor type in current `def-trf-admissibility`, the omega formula in `def-trf-dualizing-complex`, and the definitions `def-weil-finite-tor-amplitude` and `def-weil-finite-torsion-constructibility`. A single constant finite sheaf is constructible, and the degree-zero coefficient unit tensors to the input sheaf, giving amplitude [0,0]; the specified restricted functor sends A_s to omega_Y in ctf. The identity adjunction handles id_X. PASS; elementary checks, with no ambient adjoint or tensor-dualizability assertion.
- Step 2: checked against the complete statement and current snapshot source of `prop-trf-external-hom`, the dualizing formula, and current `def-sf-kv-maps` (iii)–(iv) and its finite-stage identification paragraph. The four inputs are exactly (A_X,M,N,omega_Y), all in ctf; beta is the evaluation-defined map. The two canonical unit isomorphisms give precisely the first arrow b of kappa, with derived pullback Lp_Y^*. PASS; no use of a cited proof's internal constructions.
- Step 3: checked against the complete statement and current snapshot source of `prop-trf-exceptional-kunneth`, the dualizing formula, and current map definition (ii),(iv). Substituting (id_X,a_Y,M,A_s) gives alpha with source M external-tensor omega_Y; the product target X times_k s is canonically X and the product morphism is p_X. All exceptional adjoints and separated finite-type hypotheses are supplied. PASS; it is the canonical second comparison in kappa, not an arbitrary isomorphism of endpoints.
- Step 4: checked against the actual kappa composite in current `def-sf-kv-maps` (iv). For H=RHom_A(Lp_Y^*N,-), functoriality gives H(a^{-1})H(a)=1 and H(a)H(a^{-1})=1. Thus b^{-1}H(a^{-1}) is a two-sided inverse of H(a)b. PASS; elementary inverse calculation, with the argument explicitly present in the step.
- New nodes: none, confirmed by the sandbox node-file list. PASS; no elementary child, duplicate, clause restatement, missing definition node, source-tag mismatch or Mathlib leaf requires removal or repair. Alpha and beta are existing propositions in this unit; the broader unit theorem includes all three comparisons and is not substituted for this item's proof.

I checked M=0, N=0, an empty factor, Y=s, and X=Y=s. They give zero-object or unit specializations, and at n=1 the point case is the usual finite-dimensional tensor/Hom identity. The convention n>=1 excludes n=0; at n>1 finite Tor amplitude is still required and never inferred from constructibility. No smoothness, properness, regularity or larger coefficient category has been introduced. All nine citation quotes are current verbatim substrings of at least 40 characters and their step/node pairs cover exactly every `uses` entry. No SGA source or off-route theorem is introduced.

I independently searched the read-only slopmaster2 source by the theorem name and Kunneth-Verdier vocabulary and reopened `Etale/Derived/Kunneth/Comparisons.lean:135–166` and `ProEtale/TraceFormula/Defs.lean:815–842,1048–1059`. The former's existence-only comparison package ends in sorry; the latter's isomorphism consumes the package's explicit invertibility field. Neither proves this canonical-map statement unconditionally, so no attachment is made. No compiler or Lake command was run.

Changes made: appended this fresh second-reading section while retaining all first-worker and earlier-round sections; ran a new LeanFinder query phrased in terms of projection exceptional inverse image and internal-Hom product duality, and added its actual eight hits and no-match verdict to the item's mathlib_searches (the search tool appended searches.jsonl). The displayed hits concern exponentiable morphism triangle identities, light condensed internal projectivity, and structure-sheaf module pullback. No hit supplies the geometric constructible exceptional comparison. The current worker's mathematical proof, dependencies and all nine correct citation excerpts are retained. There are zero new nodes and zero Mathlib leaves.

The required server dry run follows this completed reading; validators are invoked only through deliver.py.
