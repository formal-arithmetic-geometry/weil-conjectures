# Stage-1 delivery: lem-pur-ringed-derived-composition-cocycle

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-ringed-derived-composition-cocycle.json`: statement node, split; statement unchanged; no Mathlib match. Eight explicit proof steps reuse existing nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: fourteen literal statement excerpts, one for every cited node in every proof step.
- `searches.jsonl` and `search-result-1.txt` through `search-result-5.txt`: new searches and their actual returned hits. The item's inherited search records are retained unchanged.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, composition/cocycle terminology, and the relevant ringed and derived modules. No declaration there states the full ordinary unbounded ringed-topos comparison and all its laws. The bounded-below constant-coefficient comparison in the étale library does not cover this item. No Lean written or compiler invoked.

## WANTED

None.

## Corrections and proof route

The statement is unchanged. The empty proof is replaced by a common-resolution argument. It is an agent-written coherence proof extending the normalized comparison in Stacks Tag 0D6E, rather than a claim that the short Stacks statement already states these coherence laws. The source's proof establishes composition using adjoints; the prerequisite node explicitly supplies the K-injective normalization used here. No SGA source is used.

The chapter and `sk-lem-sf-mate` unit were read. The nearest blueprint ancestor is `fix-prop-adjunctions`, via `lem-pur-completed-coefficient-pushforward-comparison`. Read the current main-20261015 ancestor under `sec-six-functors-basics/sk-lem-sf-mate/`: the integral adjunction and pasted-composition calculation is the ancestor's relevant place. This item supplies the coefficient-restriction coherence required below that calculation, not a new proof route for the unit. The imported chapter/unit assignment and existing blueprint origin are preserved. Tool-use explanations are in `split_report.tool_uses`; no accepted `tool_uses` field is set by this worker.

The critical issue is that ringed module direct image need not preserve K-injective complexes. We therefore resolve both `g_*f_*I` and `g_*J` separately. A unique homotopy class `u:T -> K` compares these resolutions; the two paths in the cocycle become the classes of `h_*(ut)` and `h_*(kg_*j)`. The existing Hom bijection says these chain maps are homotopic. This is the actual argument, not an invocation of an unproved coherence node. Every proof step is shorter than 2000 characters.

## Existing-node and blueprint searches

Searched the whole DAG for Tag 0D6E, K-injective computation, localization universal properties, derived composition, and cocycle/identity laws. Ran `tools/blueprint_refs.py ancestor lem-pur-ringed-derived-composition-cocycle` and searches for `derived composition`, `K-injective`, `localization universal`, `cocycle`, and `direct image composition`. Opened the statements of the existing normalized composition theorem, K-injective resolution-existence theorem, Hom-to-K-injective bijection, arbitrary-derived-map computation, ringed-topos definition, and the related comparison nodes. No new helper is needed.

## Not duplicates

No new nodes. Related existing results were distinguished as follows: `lem-cbc-etale-derived-direct-image-coherence` assumes scheme étale sites, constant coefficients and bounded-below complexes; it does not state this unbounded ringed-topos result. `lem-sf-normalized-derived-comparison-composition` concerns comparisons across exact change functors and commutative squares; its exactness hypotheses do not cover general ringed-topos direct images. `lem-sfb-ringed-derived-composition-comparison` and `lem-sfb-ringed-derived-identity-comparison` concern normalized lifts with additional comparison data and derived-adjunction formulas, rather than the cocycle calculation here. Their shared Tag 0D6E is not a reason to make another node.

## Mathlib search assessment

All five new searches were run through the required `msearch.py NR lem-pur-ringed-derived-composition-cocycle` command and their outputs were read. Both semantic phrasings returned mainly derived natural-transformation and sheaf-composition lemmas. LeanSearch was available in this run; its actual hits are retained, separately from the inherited unavailable search. Loogle returned `CategoryTheory.Functor.rightDerived_ext`. Read `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean:44-149`: `rightDerived_ext` is uniqueness once a derived pair and its unit comparison are supplied; `rightDerivedNatTrans_comp` is functoriality for transformations of functors with a common source. Neither gives the composite-functor/K-injective normalization or the three-functor cocycle in this item by a one-line specialization. Read `Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean:45-86`: its comparison requires a localizer morphism, so it cannot apply by taking an arbitrary non-exact module direct image as the localizer morphism. Read `Mathlib/CategoryTheory/Abelian/RightDerived.lean`, including `NatTrans.rightDerived_comp` at line 233: this is an individual cohomological-degree derived functor of additive functors on abelian categories, not the total unbounded composite-functor assertion. The general candidates are useful tools but do not finish this item.

## Review by NR

I read Stacks `sites-cohomology.tex`, Tag 0D6E, label `lemma-derived-pushforward-composition`, including its hypotheses and adjoint-uniqueness proof, and the preceding unbounded-construction paragraph (Section 07A5). I read `derived.tex`, Tag 070I, `lemma-K-injective`, including the Hom bijection and its proof; Tag 070Y, `lemma-K-injective-defined`; and Tag 070K, `lemma-enough-K-injectives-implies`. I also read `injectives.tex`, Tag 079P, `theorem-K-injective-embedding-grothendieck`, for the existence and functoriality of resolutions. There are no new-node sources to check.

Step 1 uses `prop-pur-kinjective-resolutions-exist` for the three resolutions on small sites, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` for the quasi-isomorphism `g_*j`, and `def-weil-pbc-ringed-topos-morphism` for additive module direct images. Each of these is explicitly stated in its cited node, including the normalization, rather than extracted from a hidden proof. The source and target module rings agree at each step: I is on X0, J on X1, and K,T on X2.

Step 2 uses `lem-weil-pbc-kinjective-hom-derived`. Its statement allows any source complex and a K-injective target. It therefore supplies a homotopy class from T to K and detects the equality after precomposition by t as a homotopy on the source `g_*f_*I`. No bounded-below restriction is used: the first clause of that node is unbounded. This is precisely the required Hom surjectivity and injectivity, not merely full faithfulness of a different embedding.

Step 3 applies the normalized comparison statement twice, for (hg,f) using j and for (h,g) using k. Its component formula is valid for arbitrary K-injective I and J with those resolutions. The resulting maps really have common coordinates `Q(h_*g_*f_*I)` and `Q(h_*K)`; functoriality of termwise direct image multiplies the two maps to `Q(h_*(kg_*j))`.

Step 4 uses the same normalized comparison for (h,gf) and the full arbitrary-derived-morphism formula in `lem-sf-kinjective-derived-map-computation` to compute `Rh` of the comparison for (g,f). That statement explicitly identifies the representing map between two K-injective targets and says how RF acts on it. The equation defining u in Step 2 exactly matches its hypothesis. The direct-image definition supplies additivity, so applying h to the written chain-homotopy equation preserves it. There is no unmentioned assertion that h preserves arbitrary quasi-isomorphisms.

Step 5 uses resolution existence and the derived-map lemma's canonical change-of-resolution formulas. The step is elementary once those statements are available: naturality transports equality across an isomorphism. It does not assert that a comparison's coordinates on a non-K-injective complex are automatically the same as those on a K-injective one.

Step 6 uses resolution existence and the same derived-map lemma for the identity functor. The formula `epsilon = (Qa)^(-1)c_a` both constructs the identity comparison and proves its naturality by the displayed equality for Qw; the cited change-of-resolution clause proves it independent of a. This is not an arbitrary isomorphism to the identity whose normalization is left unchecked.

Step 7 uses the composition node only for the two normalized unit specializations. For the left unit, its map Qj is canceled by the inverse Qj in Step 6; for the right unit we can choose the identity resolution of the already K-injective I. This is a two-line cancellation after the definitions, appropriately marked elementary. The propagation to all objects is the already written Step 5 argument.

Step 8 uses the ringed-topos definition: coefficient changes on the same underlying topos have exactly the structural ring maps and induced module actions that definition permits. All hypotheses of the existence and composition nodes remain satisfied. This is a specialization, not a new helper statement.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the actual files. No new statement-only nodes were created, no clause was renamed as a new lemma, and every non-elementary input is a cited statement with a verbatim excerpt in citations.json. Tested all morphisms identities (every represented map becomes an identity or a resolution map followed by its inverse), one identity in each of the three positions, zero complexes, and the empty site/zero module category. Also tested the single-point topos with a non-flat map Z -> Z/2: the proof still uses separate resolutions, never preservation of K-injectives or flatness. The coefficient clause therefore has no hidden flatness hypothesis. The only repair during writing was to keep the two X2 resolutions distinct instead of pretending `g_*f_*I` was already K-injective. There is no statement dispute.

## Unfinished work

None in this stage-1 split. The cited existing nodes remain the project's independently managed prerequisites. Server dry-run and push results are recorded by the delivery tool.
