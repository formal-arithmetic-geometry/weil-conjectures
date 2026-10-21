# Worker report: lem-sfb-transverse-tame-open-shriek-exchange

Group NV; stage 1; 2026-10-21. Direct delivery and self-review under the current brief.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-transverse-tame-open-shriek-exchange.json`: item, statement unchanged, split into nine steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-product-action-inflation.json`: new statement-only categorical input, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-partial-kummer-boundary-unit-model.json`: new statement-only geometric input, unsplit; no Mathlib match.
- `citations.json`: full verbatim cited statements for each use in every item step.
- `searches.jsonl`: actual msearch results. The two sandbox Python scripts are generation aids, not project files.

There are two new nodes and zero Mathlib leaves. No Lean was written or compiled. Only the sandbox was written; no git command was run by the worker.

## Attachments

None. Searches of `lean/WeilConjectures` and `lean/Sheaf` for the blueprint tag, transverse/tame boundary exchange and related Kummer notions found no exact declaration. The existing KummerCover file constructs root towers of units, rather than this boundary-unit comparison. Existing sorry declarations are not treated as proofs.

## WANTED

WANTED: an exact reference/proof for the geometric partial Kummer-nerve boundary-unit model with ordinary internal modules over the all-continuous norm-topological algebraic-closure coefficient ring, for `lem-sfb-partial-kummer-boundary-unit-model`.

WANTED: an exact reference for Grothendieck abelianness and normalized exact inflation/invariants adjunctions for internal modules with an action of a profinite condensed group, for `lem-sfb-condensed-product-action-inflation`.

The current blueprint proof paragraph (3) only invokes open-image finiteness. It contains neither a tame-boundary calculation nor these two assertions. The item's own source explicitly called its all-continuous geometric input agent-formulated and WANTED. Accordingly the split is marked agent-written; it does not pretend that a finite-coefficient reference proves the missing assertion. No documents were downloaded. The exact geometric model remains an open child to be split later, as one-level stage 1 requires.

## Corrections and source limitations

The imported statement has no change and no detected counterexample. Its empty-part clauses are consistent. No `STATEMENT-DISPUTED` correction was needed.

The imported item had no proof. The crucial deficiency in a prospective direct use of `lem-sfb-tame-stratum-kummer-descent` was that it describes the full open-image object and counit, not the inner closed-unit arrow after outer direct image. I did not take that additional compatibility from its proof or silently assume it. The new geometric model states precisely that arrow, without asserting its invertibility or any shriek/star exchange. The categorical input provides only action categories and underived adjunctions; the existing derived-composition theorem supplies invertibility. The item then carries the localization-triangle, vanishing, adjunction normalization and naturality arguments.

The inherited blueprint ancestor is null: `blueprint_refs.py ancestor` explicitly reports `None`, because the created-item chain ends outside an imported node. I retained that inherited metadata and put the exact source paragraph and the extended via chain on both new nodes. This is not the unit's key node, so no unit realization field was changed. `coord/dag-sync.md` mentioned by the inherited old brief is absent; the current direct-delivery prompt supplies the live-repository policy.

## Not duplicates

lem-sfb-condensed-product-action-inflation vs lem-sfb-derived-composition-adjunction-normalization: the existing theorem assumes three Grothendieck abelian categories and exact left adjoints; the new node supplies these hypotheses for profinite condensed-group actions and identifies the actual underived adjunctions. It does not restate the derived composition theorem.

lem-sfb-condensed-product-action-inflation vs lem-sfb-tame-inertia-continuous-koszul: the latter calculates specific finite-dimensional representations analytically by a Koszul complex; the new node is categorical and gives no cohomology calculation or finite-dimensional model.

lem-sfb-partial-kummer-boundary-unit-model vs lem-sfb-tame-stratum-kummer-descent: the latter describes restriction of a single full open direct image to strata and its open counit. The new node identifies the map Rj_*(K -> h_*h^*K), including the iterated target and its actual closed unit; this is not stated by the full-stratum node.

lem-sfb-partial-kummer-boundary-unit-model vs lem-sfb-transverse-tame-open-shriek-exchange: the new node contains no extension by zero and no assertion that a map is invertible. It identifies a non-shriek boundary-unit arrow with a derived-invariants composition map; the item's argument proves that map invertible, uses localization to derive vanishing, and identifies the requested exchange with the actual open counit.

DAG and whole-blueprint searches covered Kummer, tame, transverse, invariants, inflation, equivariant, boundary unit, partial Kummer and product action. They found no exact existing node for either new assertion. New sources contain no Stacks tag, since no obtained Stacks theorem states those exact all-continuous inputs; no shared-tag pair is concealed. Mathlib searches were made with each new statement in mind and recorded literally from msearch. I read the ordinary `Rep.invariantsAdjunction` source at Mathlib/RepresentationTheory/Invariants.lean (invariantsFunctor at 252, adjunction at 278), the light-condensed AB file, invariant ring extensions for profinite groups, and the abstract-group bar-resolution source. Those are different coefficient/action categories. They do not specialize in one line to either new node. Both semantic phrasings and Loogle and source grep were run; no unavailable query was reported as a successful absence search.

## Review by NV

I read the current main-20261015 direct-images proof, paragraph (3), and the item and its ancestor's proof. The chapter route remains pro-etale six-functor construction with the separate all-continuous obligation; I have not substituted a finite-subextension ring or used a restricted constructible functor for an ambient ordinary derived functor. I also read Stacks proetale.tex `lemma-open-immersion` (09BN) and `lemma-ses-associated-to-open` (09AH), and derived.tex `lemma-compose-derived-functors` (015M) and `lemma-adjoint-preserve-K-injectives` (08BJ). The Stacks composition lemma is bounded below; the item instead cites the existing normalized unbounded exact-left-adjoint theorem. These sources support the formal argument, not an unprinted geometric all-continuous Kummer theorem. Both new nodes honestly retain the blueprint obligation as agent-formulated/WANTED sources.

Step 1 uses the sectionwise internal-module equivalence and the definitions of pullback from the point, together with the exact monoidal site-inverse-image theorem. Their statements give preservation of the underlying sheaves and canonical composition comparisons. I corrected an early draft that had treated exact inverse image as an elementary inference without citing the general theorem. This also avoids applying the admissible-coefficients Cartesian proposition, whose algebraic-closure convention would be wrong here.

Step 2 uses subterminal derived-image calculus for the actual b counit and the general condensed bounded-below recollement triangle. I verified the latter allows any commutative condensed ring, not only the finite-subextension algebraic closure. Quasi-compactness of each open follows from Noetherianity of finite-type schemes; the input is a sheaf in degree zero and all its right derived images remain bounded below. Step 3 uses the ambient exactness clause of derived-exchange-exact-normalization and the new model's exact definition of u. It does not presume closed base change for j.

Step 4 uses exactly the Grothendieck and exact-inflation assertions of the new categorical node, and the actual normalized comparison of derived-composition-adjunction-normalization. The latter explicitly says its conjugate is computed by the underived comparison on K-injective representatives. This is the theta named in the geometric child, rather than an arbitrary isomorphism of cohomology groups. Step 5 uses the new geometric child's statement for both endpoints and that arrow on an actual cover of the entire stratum. Cover conservativity then applies to derived modules, exactly as its cited statement says. No ordinary-geometric-stalk conservativity is asserted for general condensed coefficients.

Step 6 gives a finite closed/open induction using precisely the localization sequence and the jointly reflecting derived restriction functors from the two cited nodes. Normal-crossing strata have closures contained in unions of strata with larger index sets, so a finite filtration exists; empty strata can be omitted. This proves the zero restriction, including crossing points. Step 7 uses the subterminal square for V and Y-circ, the invertible extension/restriction unit, and the actual recollement counit. The formula e=epsilon composed with c_!(rho inverse) is exactly the adjunct definition in the unchanged statement.

Step 8 uses the ring-sheaf-change adjunction statement for arbitrary compatible ring sheaves, not the finite-ring restriction-of-scalars theorem. Its statement explicitly preserves the derived adjunction under scalar restriction. Open extension is the same sheafified extension presheaf with its restricted action. The open-slice identity is given by proetale-open-restriction-counit, and the generic K-injective word model derives that sectionwise identity. I wrote the scalar square as an equation, with the actual map x -> 1 tensor x, instead of saying only that the comparisons transport. The geometric new node need not assert coefficient compatibility: the map's naturality is formal from its definition, once each coefficient's e is proved invertible.

I checked empty divisor, either empty partition, zero rank, trivial action, zero ring for the categorical child, a single inner branch with no outer branch, and the two-axis local model with one inner and one outer branch. For the latter, the nonzero full inertia cohomology maps to the same iterated invariants; the fibre is zero, which is the needed distinction from falsely claiming that the full local cohomology itself vanishes. The geometric child allows nontrivial monodromy and does not assume invariants exact. New nodes are self-contained statements without proofs, not elementary lemmas or clauses simply renamed; each isolates an independent input to an argument written in the parent. Every citation was opened and its complete statement copied verbatim into citations.json. No proof step exceeds 2000 characters. Both new statements use ordinary uncompleted categories and the full norm-topological continuous-map rings. The server check_dag and review_split preliminary checks passed; final delivery preflight is still required.

## Unfinished work

No unfinished obligation in this one-level split besides the two deliberately statement-only children. They are not claimed proved. The maintainer must independently assess the geometric model in particular; its current literature source does not supply a proof.

The first full dry run rejected the context-dependent phrase “the item's” in step 5. I replaced it by the explicit hypotheses on Y, D and L, and reran the dry run. No mathematical or statement change was needed.
