# Q13: lem-sfb-coherent-regular-hyperplane-restriction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-coherent-regular-hyperplane-restriction.json`: statement, split into nine proof steps; no exact Mathlib match for the item.
- `citations.json`: 34 step/node entries, each quoting the cited node's statement verbatim.
- `searches.jsonl`: actual search-command records for this item.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. The sandbox's `write_split.py` is a local writing aid, not a delivered project file. All repository and library files were read only; no git command, Lean edit, compiler, Lake or build was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, the item id, hyperplanes, regular linear forms, and exact-sequence-induction did not find a declaration stating this item. The unrelated regular-sequence and linear-map declarations returned by the concept search do not prove its geometric or cohomological clauses.

## WANTED

None. The required Stacks source is available locally.

## Audit of the imported item and the route

The item was unsplit with an empty proof. Its statement is mathematically correct and was retained exactly. It has no `blueprint_update`. Its source gives Stacks varieties.tex, Tag 08A0 (`lemma-exact-sequence-induction`), the subsequent `remark-exact-sequence-induction` for a finite module collection, Tag 089Z (`lemma-hyperplane`), and Tag 0EGK (`remark-exact-sequence-induction-cohomology`). I read those passages in full, including the proof's references to associated primes and its cohomology comparison. I also read Algebra Tags 00LC (`lemma-finite-ass`) and 00LD (`lemma-ass-zero-divisors`), the closed-pushforward comparison Tag 02UV (`lemma-cohomology-and-closed-immersions`) in cohomology.tex, the natural module/abelian comparison Tag 03FD (`lemma-cohomology-modules-abelian-agree`) in sites-cohomology.tex, and coherent.tex's affine-cohomology and coherent closed-immersion passages to check the coefficient categories.

I read the recorded chapter and unit. The auxiliary item inherits chapter `sec-six-functors-basics` and unit `sk-thm-sf-ctf-stability` from its creation chain; that unit record itself belongs to `sec-six-functors`. Those inherited fields were not changed. This is not the unit's key node, so there is no unit realization edit. The split continues the existing Hilbert-bound hyperplane input under the alteration route. Its generic local-algebra and cohomology inputs do not replace a unit step. The two off-unit nonclosed statements requiring declarations are listed in `split_report.tool_uses`: closed-pushforward cohomology and left exactness of global sections. Other statement tools used here are already Mathlib leaves or Lean-closed in the current records.

`blueprint_refs.py ancestor` reports no imported blueprint ancestor (`None`), consistently with the item's existing `blueprint.from.node=null`. I retained that field and its long precise `from.place`, filled `same_as=[]`, and explained the realized clauses in `split_report.blueprint`. Whole-blueprint searches for hyperplane, regular hyperplane, associated points, linear avoidance, zero divisors, projective bundle, and closed immersion cohomology did not produce an imported node stating the item. I searched the entire DAG's statements and titles as well as the tag references, and reused its existing smaller tools.

## Mathlib searches

The inherited item already had search evidence, retained unchanged. I ran fresh searches with the prescribed `msearch.py` command and read their actual hits:

- LeanFinder: common nonzero regular linear form for finitely many coherent sheaves, with twisted restriction sequences.
- Loogle: `"hyperplane"`.
- Grep: `hyperplane|exactSequenceInduction|regularHyperplane`, subdirectory `AlgebraicGeometry`.
- LeanSearch: nonzerodivisor linear section of O(1) on a coherent sheaf and its short exact restriction sequence.
- A second LeanFinder phrasing: avoiding associated primes on the affine charts of projective space.

Loogle returned convexity, measure and separation hyperplanes. Grep returned no match. The semantic searches returned Proj construction/standard-open declarations, section maps, vector-space projectivization, dual-module maps, and an unrelated Profinite exactness statement. None states the item. Both phrasings are recorded exactly as run, with the search records and verdicts in the node. No new node requires additional searches.

## Review by Q13

I checked the split against delivery-errors B through E with the cited statements open. The proof carries the argument rather than moving an item clause into a new node: it constructs the bad subspaces, verifies they are proper, chooses a common section, proves injectivity, eliminates one homogeneous variable, computes every twisted quotient, and then invokes the existing general cohomology results. There are no new nodes at all, so no statement-only-node, duplicate-tag, or new-definition issue arises.

Step 1 uses `def-pc-proj` for the standard affine charts and their homogeneous localization maps, and `def-pc-projective-space-twist` for the frame description. `lem-wf-affine-noetherian-components` really states Noetherianity for every finitely generated algebra over a field, not just over the integers; each chart ring has those hypotheses. `pqf-lem-coherent-ft-locnoeth` supplies quasi-coherence from coherence on this locally Noetherian scheme. `lem-weil-pbc-coherent-affine-sections-finite` actually states finiteness on every affine open. `lem-weil-pbc-affine-tilde-gamma-adjunction` supplies the counit isomorphism for those quasi-coherent modules. Thus the finite module to which associated-prime results are applied is the actual affine module of the given sheaf.

Step 2 uses `lem-weil-pbc-noetherian-associated-primes-finite` with precisely the Noetherian chart rings and finite modules established in Step 1. `lem-pc-finite-linear-avoidance` states the finite-union assertion over an infinite field for a finite-dimensional vector space; here the space is explicitly k^(n+1). The bad subspace is proper because its j-th coordinate vector maps to 1, outside any prime ideal. The union is finite over all three indices. I explicitly included the zero subspace, so nonzeroness does not depend on any module having an associated prime.

Step 3 uses the module version `lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`, not the version for the ring alone. Its statement allows any module over a Noetherian ring. The principal-open section formulas from `lem-weil-pbc-spec-module-tilde-sections` and the affine counit from `lem-weil-pbc-affine-tilde-gamma-adjunction` apply to our modules. The preservation of injectivity under localization is proved by the displayed clearing-power argument, not left as an uncited claim. Checking a basis of opens makes the sheaf kernel zero.

Step 4 uses the two actual clauses of `prop-nagata-relative-proj-functoriality`: a graded surjection gives a closed immersion, and a graded isomorphism gives an isomorphism of Proj. It does not use that node for an unstated twist compatibility. The section's zero subscheme is verified on every standard affine by the quotient by f_j. The inverse polynomial maps are written explicitly; a_n is invertible because it is nonzero in the field. This proves H is P^(n-1) over k, including n=1. `def-weil-closed-immersion` really includes the affine quotient description used here.

Step 5 proves the twist compatibility separately from its transition functions, using the original gluing definition of twists; it works for every integer d. `lem-weil-pbc-module-pullback-quasi-coherent` gives quasi-coherence, while `lem-weil-pbc-module-pullback-affine-sections` gives the natural tensor-product formula on the affine intersection. The finite-generation argument is written out on the tensor generators, not inferred merely from the definition of pullback. The noetherianity and coherence criterion used at the end have their hypotheses on H from its projective-space identification. Thus G_alpha is actually coherent. No projection formula or flatness assertion is silently assumed.

Step 6 uses the same affine pullback theorem for the actual quotient/restriction map, the tilde-section theorem on both affine spectra, and the explicit cokernel-preservation clause of the affine tilde/gamma adjunction. It does not cite a definition to claim exactness. The isomorphism M/fM ≅ M tensor A/(f) and its inverse are written down. On every principal open the closed pushforward has exactly the localized quotient as sections, so the sheaf cokernel and the restriction arrow agree. The prior step gives the necessary twist transitions. Together with Step 3 this proves all short exact sequences for the one chosen s, with no further choices for different d.

Step 7 uses `lem-sc-module-abelian-zariski-cohomology`, whose statement explicitly gives a canonical comparison natural in the module, and `def-sc-topological-abelian-cohomology`, which explicitly identifies topological and small-Zariski cohomology for schemes. `lem-sc-cohomology-closed-immersion-pushforward` explicitly covers every abelian sheaf on a closed topological subspace, in every nonnegative degree, with naturality. The underlying map of our closed immersion has exactly that hypothesis. Forgetting the module action commutes with pushforward literally on each open. This avoids assuming that a comparison for constant etale coefficients also covers Zariski structure-sheaf modules, or that a forgetful functor preserves injectives.

Step 8 cites `lem-sc-ringed-space-module-sheaves-enough-injectives` for the abelian category with enough injectives, and `lem-sc-global-sections-left-exact` for the additive left exact functor. These check the actual hypotheses of `lem-weil-pbc-derived-functor-long-exact`. `pqf-def-cohomology` identifies the resulting right derived functors with the item's module cohomology. The comparison of Step 7 is inserted only in the third term. The four displayed terms therefore come from a proved short exact sequence and a cited derived-functor theorem, not from an appeal to a tag alone.

Step 9 is elementary after the cited natural affine pullback formula and twist frames: the two equations for a module map and the equation for a second linear form are written in the quotient and commute with localization. They show naturality of the actual arrows and restriction/multiplication compatibility. This is the only elementary-marked step; it uses no new geometric theorem. No step is longer than 2000 characters.

Edge cases: with no modules or only zero modules, avoiding the added zero subspace still produces a nonzero s; all asserted module sequences then have zero terms. For n=1 the quotient graded ring is k[S_0], and H=P^0, with the same twist-frame and cohomology arguments. A coherent sheaf supported on a finite set requires avoidance at its support; the bad-prime subspaces impose exactly that condition, and the restriction may be zero without violating exactness. Negative twists use invertible transition units raised to integer powers, so no positivity assumption is introduced. Degree q=0 is explicitly covered by all comparisons and by the start of the long exact sequence. Only morphisms among the chosen modules are required to share this regular section, as in the statement.

Corrections made during drafting: the nonzero condition was enforced even for the empty collection; twist compatibility was proved from transitions instead of attributed to generic Proj functoriality; and module-to-abelian cohomology comparison was included explicitly before applying the closed-topological-pushforward theorem. No statement correction was needed.

## Not duplicates

No new nodes were created, so there are no new/existing tag pairs. In particular I reused the existing finite associated-prime, module nonzerodivisor, finite-linear-avoidance, Proj functoriality, affine pullback, and closed-pushforward cohomology nodes instead of creating their special cases.

## Unfinished work

None in this one-level stage-1 split. Existing dependency nodes retain their current statuses; no Lean proof or build is claimed. The required server dry run and direct delivery are run after this report is written.
