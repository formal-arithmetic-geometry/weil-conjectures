# Stage-1 delivery: lem-zl-condensed-wcontractible-lisse-evaluation

## Files written

- `dag/nodes/sec-zeta-weil/lem-zl-condensed-wcontractible-lisse-evaluation.json`: statement preserved; split into nine proof steps.
- `dag/nodes/sec-zeta-weil/lem-zl-contractible-derived-sections-tensor.json`: statement-only input for arbitrary ring-sheaf tensor evaluation; no Mathlib match.
- `dag/nodes/sec-zeta-weil/lem-zl-ring-derived-dualizable-perfect.json`: statement-only ordinary commutative-ring theorem, Stacks 0FNS; no Mathlib match.
- `dag/nodes/sec-zeta-weil/lem-zl-component-relative-profinite-site.json`: statement-only geometric construction preceding HRS (4.1); no Mathlib match.

The sandbox also contains `citations.json`, the actual `searches.jsonl`, retained search responses, and working source text. Only the four node files and this report are delivery content. No unit realization fields need changing: this item is a descendant, not the unit's key statement.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for condensed, w-contractible, lisse, perfect and derived dualizability terminology. There is no matching condensed-site theorem. `CategoryTheory/DerivedCategory/PerfectTrace.lean` explicitly does not construct the equivalence between ordinary perfectness and dualizability; its trace result assumes dualizability. `CategoryTheory/DerivedCategory/Monoidal/Dualizable.lean` proves bounded complexes of dualizable terms are dualizable, which gives only one direction of the ordinary-ring input, not its converse. Thus none of these declarations supplies the whole item or the whole new scalar theorem.

## WANTED

None. All source material used is available in the shared literature.

## Audit of the imported item and route

No statement dispute and no change of hypotheses. I read Hemo–Richarz–Scholbach, Section 3, equations (3.1)–(3.2), Remark 3.2, Lemma 4.1 and its proof, the paragraph constructing (4.1), and Proposition 4.3 and its proof. The paper works with derived infinity categories; the adjunction, unit/counit, duality transpositions and canonical scalar comparisons used here also prove the stated ordinary derived-category assertions directly, via K-flat representatives. This avoids treating an equivalence of infinity categories as an unexplained ordinary-category attachment.

The original phrase “exact symmetric monoidal” means triangulated exact. It cannot be strengthened to t-exact scalar realization: HRS Example 4.2 supplies its counterexample. The evaluation functor is t-exact, whereas no such assertion about realization is made. No t-admissibility, finite Tor dimension, flatness of the coefficient-section map, nonzero-ring assumption, or bound on cochain degrees was added.

I read the chapter record and the full unit `sk-prop-smooth-proper-purity`, as well as the ancestor's updated blueprint proof and its current field-stage projection-formula paragraph. This item supplies the coefficient-level evaluation used below the condensed truncation/local-model branch; it changes no unit-level purity or weight route. Generic foundational tools from other units are declared in `split_report.tool_uses` with their intended uses.

## Searches and existing-node checks

Before creating nodes I searched the whole DAG by statement concepts and sources, and ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for w-contractible, dualizable, dual, tensor products, components, profinite test, 07LT and 0FNS. In particular the existing scalar evaluation, exact sections, colimit evaluation, coefficient component evaluation, geometric point construction, and K-flat interfaces were opened and reused where their statements apply. I did not use the local-perfect-model parent: that would be circular and would impose its extra irreducible-component hypothesis.

Every new input was searched by two natural-language LeanFinder phrasings, LeanSearch, Loogle and the prescribed Mathlib grep command. Responses are preserved exactly and the node records use the same tool/query strings. The first short Loogle patterns for two inputs produced unknown-identifier diagnostics; I retained those diagnostics and ran valid fully qualified patterns as additional searches. The latter yielded no derived dualizability theorem; the tensor search yielded sheafification monoidality and monoidal topos-point fibres, neither a derived evaluation theorem at a scheme or a general extremally disconnected profinite set. Component searches returned absolute profinite limit presentations, etale sites, and component homeomorphisms, which do not construct the relative geometric morphism. I read the generic Sites/Monoidal source while rejecting its sheafification result as a match. There are zero new Mathlib leaves.

## Not duplicates

- `lem-zl-contractible-derived-sections-tensor` vs `det-pe-wc-sections-exact`: the existing node gives exact abelian evaluation on scheme affines; the new statement additionally gives coherent unbounded *derived tensor* comparison, and includes the profinite-site case.
- `lem-zl-contractible-derived-sections-tensor` vs `det-pe-wc-sections-derived`: termwise evaluation of an arbitrary complex alone does not identify the derived tensor of its section complexes with sections of its sheaf-derived tensor.
- `lem-zl-contractible-derived-sections-tensor` vs `det-pe-sections-limits-colimits` and `lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`: those are underived limit/colimit interfaces on scheme sites, with no derived tensor theorem and no profinite-site case.
- `lem-zl-contractible-derived-sections-tensor` vs `lem-zl-wcontractible-condensed-scalar-evaluation`: the latter evaluates a scalar-induced object for the fixed global point ring; the new input compares the tensor of two arbitrary complexes of arbitrary ring-sheaf modules. It asserts no perfect/lisse equivalence.
- `lem-zl-ring-derived-dualizable-perfect` vs `lem-pc-perfect-tensor-hom-duality`, `lem-sfb-ringed-site-perfect-duality`, and `prop-pod-biduality-at-the-point`: the existing statements start with a perfect object and construct duality; they do not give the converse for an arbitrary commutative ring's ordinary module derived category. The new input is precisely Stacks 0FNS, absent elsewhere in the searched DAG.
- `lem-zl-component-relative-profinite-site` vs `lem-weil-pbc-profinite-test-object-functor`: the existing functor has absolute profinite source and constructs products with a scheme; the new functor has source the slice over the scheme's component space and constructs relative fibre products with its clopen pieces.
- `lem-zl-component-relative-profinite-site` vs `lem-weil-pbc-condensed-point-basis-evaluation`: the latter evaluates coefficients on a contractible basis but does not construct the relative site morphism for arbitrary affine T. The new node has no lisse or perfect conclusion.

## Review by Q40

I checked B–E with the item, the three new statements, the cited existing statements, and the source text open. The three new nodes contain statements only, no proof sketches or proof dependencies, and introduce their objects and coefficient categories explicitly. Their blueprint origin is the same nearest ancestor as the item, with the item prefixed to the existing ancestry chain. All ordinary-ring definitions apply on the one-object identity-covered site. Every cited statement is quoted verbatim in `citations.json` (complete statements are used where a step needs several clauses).

Step 1 uses exactly the new tensor-evaluation statement, for the two site types and arbitrary ring sheaf that it states. This is the non-elementary calculation in HRS Lemma 4.1(1), not a definition of sections. Its extension from the particular condensed coefficient to arbitrary ring sheaves uses the same finite-partition sheafification/evaluation calculation. I have exposed that calculation as a smaller input rather than calling derived monoidality elementary or assuming evaluation preserves flatness without proof.

Step 2 applies the existing *arbitrary ringed topoi* module adjunction and derived pullback/tensor statements to the geometric global-sections map to Set with coefficient map from the discrete section ring. It does not try to apply a scheme-morphism-only derived adjunction to this map. The generic derived-adjunction Mathlib leaf supplies the normalized unit/counit, and the exact constant-derived functor identifies the displayed realization. Its K-flat hypothesis is precisely the hypothesis of the existing pullback computation, not a flat coefficient-map hypothesis.

Step 3 is an elementary calculation from the adjunction of step 2 and the exact colimit clause quoted in step 1: free modules are sent to sums of the unit; the cokernel of a free presentation identifies the same canonical unit on an arbitrary module. Step 4 uses the named K-flat-resolution statement on the point site and the named derived-pullback computation. Naturality of the underived unit is what makes the degreewise isomorphisms a chain isomorphism. This proves the *derived* adjunction unit on all unbounded objects, not merely an equality of degree-zero sections.

Step 5 writes both duality transpositions, obtained by tensoring evaluation or coevaluation; their inverse-composite identities are exactly the two triangle identities. Applying a strong monoidal functor applies the same expressions. The adjunction at the scalar unit compares the remaining Hom sets, so the bijection really is induced by sections. This is why no unjustified internal-Hom preservation theorem, no compact generation, and no assertion that sections are conservative on all sheaves is needed. It is an elementary categorical step from the established adjunction and monoidal functors.

Step 6 uses Stacks 0FNS (`more-algebra.tex`, `lemma-have-dual-derived`), which I read in full including its converse proof: duality makes the identity factor through a bounded finite-free complex and hence makes the object a perfect retract. This applies to arbitrary commutative section rings, not only fields. The rest of step 6 explicitly inverts the counit by the triangle identity and reflects its inverse using full faithfulness on dualizable objects; it does not assume the desired equivalence.

Step 7 uses the relative site construction preceding HRS (4.1), the actual coefficient-evaluation theorem, the definition of geometric w-contractibility, exact geometric inverse image, and the general derived tensor pullback. The coefficient-evaluation node assumes topos weak contractibility; I checked the bridge, using the existing clopen covering-refinement statement to glue local lifts of an epimorphism. The geometric construction is an independent unsplit node, whose statement gives the required factorization of the point morphism. It does not simply restate the desired lisse equivalence.

Step 8 follows the final square in HRS Proposition 4.3(3): exact identified-coefficient inverse image preserves constants, and K-flat pullback plus the derived tensor comparison give the scalar-square isomorphism. The K-flat localization theorem supplies naturality on all derived morphisms. The two instances of the equivalence proved in step 6 then identify the middle functor with the identity on perfect modules over the canonically identified section ring. No general full faithfulness of component pullback or component-space cohomology theorem is silently assumed.

Step 9 gives the balanced chain maps in both directions for the scalar tower. K-flat extension along R to A is valid without A being R-flat, by the existing ringed pullback theorem on point sites. The existing constant/scalar comparison and localization statements justify the representatives and the naturality on the derived categories. No uncited transitivity theorem with different sheaf coefficients is substituted.

I tested the new statements and the proof on empty T and S (zero section ring and zero derived categories), singleton profinite spaces, finite disjoint unions (product section rings and module categories), zero coefficient rings and zero complexes, and an arbitrary unbounded scalar complex. None requires a connected T or a nonempty space. The new ordinary-ring theorem works for rings with nonfree finitely generated projectives: it uses projective, not free, perfect models. I also checked nonflat coefficient change using the K-flat representative condition, and kept HRS Example 4.2 in view so that no step infers t-exactness of realization. All nine steps are shorter than 2000 characters; the substantive hidden calculations are exactly the three named unsplit inputs, not long elementary steps.

During self-review I corrected the initially tempting use of the existing scheme-only scalar evaluation as a theorem for arbitrary section rings: the split now proves the unit by free presentations and K-flat representatives. I also used the arbitrary ringed-topos derived interface rather than a scheme-only adjunction, and made the geometric-to-topos contractibility bridge explicit. No unresolved mathematical or source discrepancy remains.

## Unfinished work

The three new nodes are intentionally unsplit, as required for a one-level split; they have their sources and recorded searches. No Lean was written, no compiler was run, no repository file was changed, and no git command was run in the shared checkout.

## Validation

The required `deliver.py Q40 lem-zl-condensed-wcontractible-lisse-evaluation --no-push` exited successfully: `OK (not pushed)` at `82713eabca`, with server preflight passed. The final report is revalidated by the same dry-run command before the push.
