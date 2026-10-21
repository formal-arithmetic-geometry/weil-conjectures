# Q19 stage-1 delivery

## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-tate-root-projection-reduction.json`: existing statement, now split into nine proof steps; no Mathlib match.
- `citations.json`: 33 citations, each quoting the cited statement verbatim.
- `searches.jsonl`: actual msearch results for the item.

There are **0 new nodes and 0 new Mathlib leaves**. The helper `write_split.py` is sandbox-only and is not a project delivery file.

## Attachments

None. I searched the current `lean/WeilConjectures/` for the exact blueprint tag and root/Tate/projection terms. `AlgebraicGeometry.Scheme.ProEt.rootsOfUnityTower` in `WeilConjectures/AlgebraicGeometry/Sites/ProEtaleRootsOfUnity.lean:271` constructs the tower; it does not prove the item. The finite Kummer comparison declarations concern etale finite twists, not the prescribed pro-etale inverse-limit twist with all these coherence clauses. They are not attachments for this item.

## Wanted literature

None. All sources used are available in the read-only repository.

## Audit findings and corrections

The original node had a statement but no proof. I preserved its statement and all statement dependencies. In particular I did not impose flatness on the ramified quotient, replace the finite twist, or assume the exponent is divisible by the ramification index.

The original source field cited completion-flat, Tag 093M. That theorem concerns completion of constant coefficient rings; it alone does not establish the root projection or its normalized coherence. I supplied a direct local-lift argument from existing Kummer transition epimorphisms and the full-site weakly contractible covers, and changed the source field accordingly. The proof origin is explicitly `agent`. The actual literature inputs are Stacks Tag 0990 (`proetale-lemma-proetale-enough-w-contractible`), Tag 090K (`sites-lemma-w-contractible`), the Kummer section 03PK and its root-lifting argument, the general-site epi criteria, and ordinary sheaf tensor calculus 03EK/03EL. No SGA source is used.

I read the current main-20261015 vector-bundle purity proof paragraph 1, the chapter record, and the full sk-prop-an statement and proof. This is a coefficient calculation under the vector-bundle integration, not a replacement for any step of the model-purity unit. Since the item is not the key node, I did not alter the unit realization fields.

## Not duplicates

No new nodes. The existing `lem-pur-twist-root-local-models` supplies unnormalized local models and scalar reduction isomorphisms. Its proof contains compatible-root choices, but its statement does not give the precise projection identities required here; I did not cite its proof as a theorem. The root transition lemma, the general-site epi criteria and the weakly contractible covering theorem are used directly instead. Whole-DAG key-term searches and `blueprint_refs.py search` for roots and root projection found no blueprint node stating this entire comparison with its pullback equations. The item retains `same_as: []` and its existing nearest ancestor, `thm-amb-vector-bundle-purity`.

## Mathlib searches

I ran msearch leansearch, loogle, grep and two distinct leanfinder phrasings for the item. All services answered. The returned results concern ring roots and cyclotomic characters, module tilde constructions and generic sheaf pullback/sheafification, rather than the item. In particular the cyclotomic-character projection formula describes automorphisms of a ring with enough roots, not a root-sheaf inverse-limit comparison. The AlgebraicGeometry grep for TateModule, rootsOfUnityTower and root projection returned zero hits. Queries, actual result summaries and verdicts have been appended without altering inherited search records. No searches were invented or inferred from another worker's log.

## Review by Q19

I checked delivery-errors B through E against the statements, sources and all nine steps. There are no new statements requiring their own sources, definitions, duplicate exclusions or Mathlib leaf line checks (B1-B9); the item is self-contained and retains its notion-defining dependencies. The actual search log supports the appended searches (B7), the blueprint reference is precise (B9), and no exact project attachment was found (B10). The proof does not move clauses into new nodes (D1-D2), does not rely solely on definition nodes for a hidden theorem (D3), and writes the recursive choices with their base and inductive step explicitly (D4-D5).

**Step 1.** I read `def-coefficient-twists-detailed`, the root sheaf definition, the sectionwise inverse-limit definition and the sheaf tensor definition. They give exactly the two iterated ordinary tensors forming the prescribed twist, the root coordinates and the sheafification construction. The explicit maps multiplying the middle coefficient and inserting its unit respect the balancing relations. This is an elementary tensor reassociation, not a new lemma. The coordinatewise exponent action uses the constant Z_l ring; it does not identify that constant sheaf with its completion.

**Step 2.** I opened all five cited nodes. `lem-pur-twist-root-transitions` supplies every consecutive power map at positive root level (take its natural-number index to be s-1 for s >= 1). It is an abelian epimorphism, so I explicitly used the general-site abelian epi criterion followed by the general-site set criterion. I did not use their etale-only variants. The weakly contractible covering node promises affine covers of every object, weakly contractible for the full original pro-etale site, and explicitly makes set epimorphisms surjective on sections. Those are the precise hypotheses needed to choose every later root on one fixed covering member. Stacks 0990 and 090K were read in the source. The tuple is initialized at level r, its lower coordinates are defined by powers, and its upper coordinates are chosen recursively. No smoothness, finite type, quasi-compactness of T, or commutation of stalks with limits is needed.

**Step 3.** The two definitions cited compute the limit on sections and identify its transition with raising to ell. I checked the shifted tuple: x_(s+r) has order dividing ell^s because its ell^s power is x_r = 1. Its ell^r power is x_s. This proves the exact kernel claim on every object in two coordinate calculations. It is elementary, so I did not create a kernel lemma node.

**Step 4.** The cited tensor-section calculus explicitly gives bilinearity, restriction compatibility and determination of maps by pure tensors. The torsion constant-module theorem states both existence/uniqueness of the Z/ell^r-module structure and linearity of every additive sheaf map between sheaves killed by ell^r. I applied it on a slice with the local coefficient section fixed, so it really supplies the balancing over local sections of the constant finite ring. The target is killed by ell^r because A is. The difference between two lifts is ell^r y by step 3, so its tensor vanishes using ell^r a = 0, not flatness. This independence glues the local pairing, and checking the two composites on pure tensors proves both inverse identities. The argument contains the actual inverse rather than assuming right exactness preserves an unspecified sequence.

**Step 5.** The root definition supplies the exact exponent map. I evaluated both transition composites on a general pure tensor and used the tuple equation, then exhibited the inverse transition as theta_r composed with theta_r' inverse. This also verifies the identity and three-level composition equations and checks the change in finite coefficient ring rather than silently treating all tensors as over one ring.

**Step 6.** I opened `lem-pur-roots-of-unity-inverse-image-iso` and used only its clauses 1 and 2: transition compatibility and semilinearity. It does not assert isomorphy for an arbitrary v, and no such assertion is needed here. The cited definition of the root comparison gives the precise adjunct, namely pullback of a unit by the fibre-product projection. I wrote the identity and composite projection computations and invoked only the adjunction bijection and the canonical site inverse-image comparisons. This checks the specified maps and their order of composition; it does not invent coherent choices.

**Step 7.** The inverse-limit node states its universal property and coordinate projections. The finite comparisons from step 6 supply a cone with source v^-1 L_T, so the target limit exists without a hypothesis that inverse image commutes with infinite limits. The finite semilinearity equations imply Z_l semilinearity after every projection. This is a routine application of the defining limit, marked elementary.

**Step 8.** The generic ringed-topoi tensor-pullback node applies to the actual small pro-etale geometric morphism with its constant coefficient maps. It states an ordinary, natural tensor comparison for arbitrary module sheaves, so it needs neither flatness nor a derived category. With the displayed reassociation, it identifies exactly the domain used to define b_v. I checked the required square on a pure tensor, where it is the projection equation from step 7. The tensor-section node justifies passing from that equality to equality of sheaf maps.

**Step 9.** I explicitly projected each proposed composite c_L to a finite root level and used the finite comparison equation of step 6. Uniqueness of maps to the limit proves its composition law. The corresponding b maps agree on each pure tensor, and the cited monoidal inverse-image comparisons provide the canonical identifications. Identity is the same calculation at the identity projection. No unsupported assertion that a transport preserves coherence remains.

For C1-C4 I read every cited statement, not merely its proof or title; `citations.json` quotes each whole statement, so its scope and hypotheses remain visible. For C5-C8 I searched existing nodes, avoided the etale-only tools, checked that the proof dependencies do not reach the item again, and declared the generic off-unit tools in `split_report.tool_uses`. These tools supply sheaf operations below the unit and do not change the unit route. No existing maintainer `tool_uses` field was edited.

For E1-E7 I tested the smallest root level r = 1, equal levels r' = r, three increasing levels, the identity and a composite base morphism, and the empty scheme. I also checked the nonflat coefficient example E = Q_l, A = F_l, taking r = 2: multiplication by ell^r still kills A and the local-lift inverse is unchanged, although F_l is not flat over Z/ell^2. For a ramified extension, n = 1 similarly works regardless of its ramification index. A nonreduced base causes no change in the shift calculation, which uses equalities of units in its section rings. The result requires only the given invertibility of ell for the transition epimorphisms and ell^r A = 0 for tensor descent. There is no disputed statement or source counterexample. No proof step exceeds 2000 characters; the largest is the explicit inverse-pairing construction.

## Unfinished work

No mathematical clause remains unfinished. Server checks and the dry-run/push results are recorded below after execution.

## Validation

- Server `review_split`: PASS; 0 new nodes. The existing unit realization warning concerns the unit's key-node work and does not block this item.
- Required `deliver.py --no-push`: exited 0, `OK (not pushed)`, commit `04cfadbdfce`; server preflight passed.
