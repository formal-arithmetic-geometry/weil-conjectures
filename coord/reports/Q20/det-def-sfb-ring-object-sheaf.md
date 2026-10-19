# Worker report: det-def-sfb-ring-object-sheaf

## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-ring-object-sheaf.json`: statement, split into seven steps; no full Mathlib match.
- `citations.json`: every proof citation with a literal quotation from the cited statement.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The existing leaf `def-weil-pbc-sheafification` is reused.

## Attachments

None. I searched the specified slopmaster2 project by the exact item id, the blueprint tag, ring/sheaf/monoid terminology and the unit's named declarations. `WeilConjectures/CategoryTheory/Sites/MonObj.lean` supplies `CategoryTheory.Sheaf.monObjOfPresheaf` (line 52), `μ_comp_map_mul` (line 59), `ε_comp_map_one` (line 85), tensor/unit hom extensionality and a morphism criterion. These are useful partial constructions, but no declaration found states every clause for the underlying abelian sheaf of an arbitrary sheaf of rings, including the counit uniqueness and commutative clause. Thus I do not claim ATTACH. The exact tag and the unit's listed sheafCompose/ring-object declaration names were absent from the specified project tree. I did not treat upstream master sorry declarations as finished proofs.

## Wanted literature

None. All proof sources used are present.

## Audit and corrections

The statement is unchanged. I read the current `main-20261015` statement, its separate `.proof.md`, the ring-object unit `_section.md`, and the proetale-coefficients chapter `_section.md`. This item realizes clause 3 of that unit and is not the key definition node. The imported item has no `lean_audit` field and no chapter/unit fields. There is also no `dag/chapters/sec-proetale-coefficients.json` or matching ring-object unit record in this shared snapshot. I used the corresponding blueprint section files directly; no maintainer-owned metadata or unit realization was changed. This missing record is reported for maintenance, not repaired by the worker.

The imported proof compressed several arguments into “transport” and “naturality”. It also wrote the sheafification multiplication as `a(μ_p)` without displaying its strong monoidal comparison. The replacement retains the same route and spells out that comparison, cancels it against the tensor of the counit inverse, and only then obtains the concrete extension formula. The proof never assumes that the inclusion of abelian sheaves is strong monoidal. Forgetting ring operations is handled by the identical matching families, rather than introducing a general preservation-of-limits lemma.

The whole-DAG and blueprint searches for “ring object”, “sheafification”, “counit” and “sheaves of rings” found the existing presheaf, monoid, tensor and sheafification nodes. The unit `sk-def-sfb-ring-object` includes the existence/morphism clause, but already depends on this item; it was deliberately not cited back, avoiding a cycle. The existing `lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction`, `lem-weil-pbc-sheaf-ring-objects-bijective` and `...-surjective` concern internal commutative ring objects for the cartesian tensor on sheaves of sets, not the tensor over the integers on abelian sheaves. No replacement or duplicate was created.

All Mathlib queries were executed through `msearch.py` and are recorded verbatim in the item and `searches.jsonl`. Two semantic phrasings were tried. The `CategoryTheory.Sheaf, MonObj` Loogle query rejected the unqualified identifier; I recorded that and ran the qualified `CategoryTheory.MonObj.ofIso` query. The initial grep restricted to `CategoryTheory/Monoidal/Mon` returned no hits; the corrected `CategoryTheory/Monoidal` query located `Mon.lean:112,232`, which I read. I also read `Sites/Monoidal.lean:164–202`, the cartesian tensor candidate's hypotheses, and the sheaf-module definitions located in `ModuleCat/Sheaf.lean`. General monoidal sheafification, cartesian tensors and module-category constructions are partial machinery, not a full match. Isomorphism transport is the explicit elementary calculation in step 4, not a new node.

## Unfinished work

No mathematical part of the one-level split is left unfinished. Existing cited items remain separate DAG work. The required check is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q20 det-def-sfb-ring-object-sheaf --no-push`; the final READY response is issued only after that command prints OK for this sandbox. No delivery is pushed by this worker.

## Review by Q20

I reviewed the item against `det-def-sfb-ring-object-sheaf.md` and both paragraphs of `det-def-sfb-ring-object-sheaf.proof.md` in the current blueprint. I also read Stacks `sites.tex`, Tag 00YR (`section-sheaves-algebraic-structures`), especially (alpha), (epsilon) and the ring-as-sextuple description, and Tag 00WH (`proposition-sheafification-adjoint`). These support the general sheafification convention and the matching-family argument. The Stacks section's historical mention of SGA is not used: no SGA source or theorem enters this split. There are no new-node sources to audit.

Step 1 has no black-box lemma: ring sections and additive sections have identical matching families and gluing; the additive equalities follow by restricting the sum, zero or negative and applying uniqueness. Thus it is an elementary argument, including empty coverings.

Step 2 cites the actual statement of `def-weil-pbc-sheafification`, which explicitly says every map to a sheaf factors uniquely. I checked that its values include abelian groups. The inverse of the counit is proved using that uniqueness and fullness of the inclusion; no full-faithful-adjunction theorem is hidden. The naturality identity follows from the same universal map.

Step 3 cites both clauses of `det-def-sfb-ring-object-presheaf`: they explicitly supply the presheaf multiplication/unit, the monoid structure on `aP`, its displayed strong-monoidal comparison, commutativity and functoriality. Its site and tensor hypotheses are exactly those already stipulated by the item. No hypothesis that the rings are commutative is added here.

Step 4 uses the equations in `det-def-sfb-ring-object-monoid`, not a supposed transport theorem in that definition. The argument expands associativity into the two conjugated expressions with the same map `Q`; tensor functoriality and associator naturality are part of the monoidal structure. It likewise writes both unitor identities, both counit/inverse morphism identities, and cancellation proving uniqueness. Every ring-object axiom has been checked. These computations make a separate transport node unnecessary.

Step 5 also cites clause 3 of `det-def-sfb-sheaf-tensor-local-iso`, which explicitly states that sheafifying the tensor of universal unit maps gives an isomorphism. I read that full statement and checked that its sites and value categories are those inherited here; its dependency path does not return to this item. This citation was added on self-review to make invertibility of this specific comparison explicit. Step 5 uses the statement of `det-def-sfb-sheaf-tensor-structure`, which defines the tensor as the sheafification of the objectwise tensor, defines morphism tensors by sheafifying them, and specifies the strong monoidal comparison built from the universal unit maps. That is exactly the comparison used here. I checked the types of `a(t_P tensor t_P)` and its inverse: their endpoints are `S tensor S=a(P tensor_p P)` and `aP tensor aP`. Since `i(q)=t_P`, the cancellation is valid. Only after that cancellation is the transported multiplication identified with `e a(μ_p)`. The sheafification node supplies uniqueness of extension for both this multiplication and the map from the constant integer presheaf; the constant sheaf is its sheafification, not an assertion that the constant presheaf was already a sheaf.

Step 6 uses the commutativity equation defined in the monoid node and the already established commutativity of `aP` from step 3. Naturality of the symmetry gives the displayed equation, with no uncited commutative transport theorem.

Step 7 cites the presheaf node for the two presheaf morphism equations, the tensor node for the tensor of morphisms, the sheafification node for uniqueness, and the monoid node for the meaning of a ring-object morphism. I checked both product maps have source `a(P tensor_p P)` and the same target sheaf, so uniqueness applies; their restrictions agree because the map is a ring map on every section. The unit maps likewise have source `a(Z_p)`. This proves functoriality directly and does not require a monoidal-counit theorem absent from those statements.

I checked B–E against the actual files: no new node to contain an unsupported proof sketch or duplicate clause, all five citation targets exist and are unmerged, all their statements are quoted verbatim, and no cited node depends on this item. The general sheafification leaf is a tool already allowed by the route; the tensor and monoid notions are definitions, and the local-isomorphism fact is in the tensor unit cited by the ring-object unit; the non-elementary constructions are provided by the presheaf node in the same blueprint unit and the existing unit-induced tensor-comparison isomorphism in the tensor unit it cites. No off-unit theorem route is substituted.

The small cases are the terminal site with trivial topology (where `a`, the counit and comparison are identities and all maps reduce to the usual ring maps), the zero ring, empty covering sieves (whose sheaf value must have one element, giving the zero ring/additive group), and noncommutative section rings such as a constant sheaf with matrix-ring coefficients. The construction and the morphism argument apply in the last case; only step 6 uses commutativity. No finiteness, nonzero-ring, enough-points or geometric hypothesis is used. The correction made during this review was to display and type-check the strong monoidal comparison instead of treating `a(μ_p)` as already having source `aP tensor aP`.

## Not duplicates

No new nodes were created.

## Second reading by Q20

I reread the item statement against the blueprint node and its proof, and checked the
site, sheaf, abelian-presheaf, tensor, unit, commutativity, and morphism hypotheses
against the cited presheaf and tensor statements.  The statement agrees clause by
clause; the zero ring, terminal site, empty covering, and noncommutative matrix-ring
examples leave all claimed clauses well typed (commutativity is asserted only under
the stated sectionwise hypothesis).

Step 1 was checked against Stacks Tag 00YR (section-sheaves-algebraic-structures,
assertion (alpha)) and the ring-as-sextuple discussion: identical matching families
give additive gluing, including zero and empty covers.  Verdict: elementary and
complete.

Step 2 was checked against the full statement of def-weil-pbc-sheafification and
Stacks Tag 00WH: the two counit inverse equations use the universal extension
property, and the displayed naturality equation has the correct presheaf and sheaf
types.  Verdict: elementary and complete.

Step 3 was checked against both clauses of det-def-sfb-ring-object-presheaf: it
supplies the objectwise maps, strong-monoidal comparison, commutativity, and
functoriality used here.  Verdict: dependency says exactly what the step uses.

Step 4 was checked against all three clauses of det-def-sfb-ring-object-monoid.  I
expanded associativity, both unit equations, the two inverse morphism equations, and
the cancellation uniqueness argument; no transport assertion is being assumed.
Verdict: elementary calculation.

Step 5 was checked against det-def-sfb-sheaf-tensor-structure, its local-isomorphism
clause det-def-sfb-sheaf-tensor-local-iso (clause 3), and the sheafification universal
property.  The comparison is explicitly typed as the inverse of the sheafified
tensor of counit units, so its cancellation with q tensor q is valid before the
concrete extension formula is asserted.  Verdict: complete.

Step 6 was checked against the commutative-ring-object clause of
det-def-sfb-ring-object-monoid and the commutativity clause of the presheaf node;
naturality of the symmetry gives the displayed conjugation.  Verdict: complete with
the correct sectionwise commutativity hypothesis.

Step 7 was checked against the presheaf morphism equations, tensor-on-morphisms and
sheafification uniqueness, and the ring-object morphism definition.  Both product
maps have source a(P tensor_p P), and both unit maps have source a(Z_p), so the
unique-extension comparison is applicable.  Verdict: complete.

There were no new nodes to audit under B1--B7.  I confirmed the existing citation
nodes occur in the DAG, quoted statements are verbatim in citations.json, all
non-elementary facts are cited, and the dependency graph has no citation back to
this item.  No files or statements required repair in this second reading.
