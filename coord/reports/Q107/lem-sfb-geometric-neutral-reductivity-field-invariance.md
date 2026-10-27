# Stage-1 delivery: lem-sfb-geometric-neutral-reductivity-field-invariance

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-geometric-neutral-reductivity-field-invariance.json: item, statement unchanged, five proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-unipotent-subgroup-spreading.json: new statement-only supporting lemma, unsplit, no Mathlib match.
- citations.json: ten verbatim cited-statement excerpts, one entry for each step/use pair.
- searches.jsonl: actual msearch.py search records; all services returned answers in this session.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for reductivity, normal unipotent subgroups and identity components. Basic.lean has identity-component declarations, but no declaration states the item. The reductivity hits are Lie-algebra results in WeilConjectures/Mathlib/Algebra/Lie/Semisimple/Lemmas.lean. They do not assert any group-scheme field invariance. No compiler or Lake was run.

## Wanted literature

WANTED: Conrad, Reductive group schemes, Exercise 3.4.1(i)-(iii), printed p.104, and Corollary 3.1.11 proof, printed p.89, local file literature/conrad-reductive-group-schemes.pdf, for the item and lem-sfb-normal-unipotent-subgroup-spreading. I read the author's PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. Milne's 2017 book is available locally and was read. The item's proof_origin is agent, as required when the local reference is missing. Nothing was downloaded or written to literature/.

## Defects repaired and scope

There was no prior sandbox split or report. The live item was unsplit with empty proof. Its statement is correct and unchanged. Its source already pointed to the right exercise, but the argument was not yet decomposed. I isolated the finite-type model theorem for a SPECIFIED normal unipotent subgroup. The proof does not mistake separable-algebraic invariance of the unipotent radical (Milne 19.9) for invariance under arbitrary transcendental extensions. The normal-unipotent spreading statement is not reductivity ascent under a different name: it gives a prescribed subgroup model and positive-dimensional unipotent fibres without assuming the ambient group connected or reductive, and without asserting any reductivity conclusion.

The inherited blueprint.from.node is null; blueprint_refs.py ancestor prints None for this item. I retained that origin and the full via list, filling the new node's place by the exact supporting exercise. The latest blueprint is literature/blueprint/latest -> main-20261024. I read the chapter and unit records, the current direct-image detailed proof underlying the inherited route, and searched the whole blueprint with blueprint_refs.py for reductiv, identity component, unipotent, unipotent subgroup, normal unipotent, normal subgroup, and spreading. There is no blueprint equivalent. This remains a field-theoretic supporting input to the reductive-locus pullback identity before the closed-complement limit argument of lem-sfb-reductivity-eventual-ring-colimit; it changes no chapter or unit route.

## Not duplicates

lem-sfb-normal-unipotent-subgroup-spreading vs lem-sfb-geometric-neutral-reductivity-field-invariance: both cite Conrad Exercise 3.4.1; the new assertion models a specified subgroup with controlled geometric fibres over a finite-type subalgebra, while the item compares reductivity at geometric identity components and deduces a locus pullback.

lem-sfb-normal-unipotent-subgroup-spreading vs lem-sfb-smooth-connected-subgroup-noetherian-model: the existing model is over a finite-type integer subring and preserves smooth connected subgroup fibres; it neither preserves normality nor imposes unipotence and nontriviality in all geometric fibres, and does not retain the given F-model of the ambient group.

lem-sfb-normal-unipotent-subgroup-spreading vs lem-sfb-algclosed-group-embedding-existence-descent: the latter concerns existence of some embedding between two fixed groups already defined over an algebraically closed base; here N is only given over K and its specific embedded model, normality and all geometric-fibre properties must descend.

lem-sfb-normal-unipotent-subgroup-spreading vs lem-sfb-perfect-unipotent-additive-series: the latter gives a series over a perfect field, with no subalgebra model or embedded normality in another group. It is a future input to splitting the new model statement, not that statement itself.

## Mathlib searches

I ran leanfinder, leansearch, loogle and grep through the prescribed msearch.py, and read every returned hit. The item searches find geometrically reduced algebras and reductive Lie algebras. The model searches find Algebra.Smooth.exists_subalgebra_fg / exists_subalgebra_finiteType / exists_finiteType in RingTheory/Smooth/NoetherianDescent, abstract AddGroupExtension and module finite-presentation results. I read the smooth-descent source: it produces an algebra model, not group laws, a specified normal subgroup inclusion or nontrivial connected unipotent fibres. None is an exact match or one-line specialization for the new lemma. A second semantic phrasing was run for both the item and model question. All recorded queries are literal queries in searches.jsonl. There are zero Mathlib leaves.

## Generic tools from other units

The split_report.tool_uses declares smooth base change (lem-pc-proper-base-change, clause (2) only), closed-immersion base change, the algebraic-closure embedding lemma, the rational closed-point clause of the affine Nullstellensatz, and the generic base-change definition. These supply generic field/scheme tools rather than replacements of the unit's constructibility route. All remaining cited group-component facts and the new node belong to the item's unit.

## Review by Q107

I read Conrad Exercise 3.4.1 on printed p.104 online, its Corollary 3.1.11 pullback paragraph, Milne Proposition 1.34 on pp.16-17 and Proposition 19.13 on p.400 in the local book. For the new node I checked the subgroup model against the exercise's finite-type construction: a positive-length additive series over the algebraically closed upper field can be modeled together with the ambient conjugation and kernel identities; smoothness and fppf quotient maps persist after enlarging the finite-type subalgebra. After any geometric specialization, induction on the series preserves connectedness and unipotence and leaves positive dimension. This is the intended supporting lemma, left statement-only for a future worker. I also read Milne Corollary 16.24 (printed p.332) for the series and Section 6.45 (p.135) for extension closure. Its lower field F need not be perfect: the additive series is constructed over K, which is algebraically closed. The existing perfect-unipotent-series node agrees with this source but does not supply the model.

Step 1 uses precisely the smoothness clause of lem-pc-proper-base-change, the closed-immersion clause of lem-weil-pbc-closed-immersion-base-change and the field-extension clause of lem-sfb-locally-algebraic-group-identity-component. I opened those node statements. Connectedness of N_E follows by applying the component clause to N=N^0; no arbitrary scheme's connectedness is silently assumed invariant. Normality is tested on E-algebras, already F-algebras. The all-geometric-points matrix definition ensures unipotence after extension. A nonzero augmentation ideal stays nonzero by a vector-space basis argument, so nontriviality is preserved. The same cited component and smoothness facts ensure J_E is in the connected smooth category needed for the reductivity test.

Step 2 applies the new node to the actual subgroup witnessing failure of reductivity, rather than to an unspecified radical or a changed subgroup. Its conclusion supplies all four needed geometric-fibre properties as well as closed normality. The other cited statement, lem-wf-affine-nullstellensatz-vanishing, really states that maximal ideals in a finite-type algebra over an algebraically closed field have base-field residue field. I checked the hypothesis F algebraically closed and A nonzero, the latter because A is a subalgebra of E. A maximal ideal exists, and the resulting fibre is over F itself. No arbitrary field is claimed to admit this rational specialization.

Step 3 uses the embedding clause of lem-weil-pbc-algebraic-extension-embeds-algebraically-closed and the full identity-component statement, including clopenness, finite type and base-change compatibility. The algebraic-closure embedding hypothesis applies to the algebraic extension kbar/k, even when Omega/k is transcendental. A clopen component of an affine group is affine, and an open in a smooth scheme is smooth from the local-chart definition. Thus the connected group C satisfies all hypotheses of steps 1-2. The identity-component node used here has no characteristic-zero restriction, unlike some older matrix-group blueprint nodes, which I did not cite.

Step 4 is elementary logical assembly: both geometric fields contain k, through L for the second one. It neither assumes a chosen inclusion between those two fields nor needs an amalgamation theorem. This proves the arbitrary algebraically closed extension clause as well as the closure clause.

Step 5 uses smooth base change and the fibre definition in def-pc-base-change, both opened and quoted verbatim. The local ring map at t gives the residue-field inclusion kappa(s)->kappa(t). Associativity of the fibre product is justified by its points/universal property, and the affine tensor presentation gives affineness and finite presentation of the fibre. The membership test therefore applies exactly to H_s and its residue-field extension, giving the stated equality of subsets. There is no Noetherian assumption on S or T.

I checked B-E against the files: the new node introduces all fields, groups, morphisms and its unipotence convention, has no proof or proof dependencies, and cites its underlying notions. Every citation excerpt is an actual substring of the cited node statement; citations.json was generated only after checking that condition. I searched the DAG by titles, statements, the exercise number and the relevant model/normality concepts before creating the new id. The smooth-noetherian-model and embedding-existence near misses are distinguished above. The new node is not an elementary two-line fact: it must descend conjugation factorization and preserve a nontrivial unipotent filtration, which is why it is isolated.

Small cases checked: the trivial ambient group makes the new lemma's nontrivial-subgroup premise impossible; a torus likewise has no such subgroup; N=G_a and upper triangular groups give the expected constant models. A finite smooth disconnected group has trivial identity component and satisfies the item's reductivity condition; no argument incorrectly requires G connected. A positive-characteristic infinitesimal group alpha_p or mu_p is not a permissible smooth N, so it cannot masquerade as a nontrivial smooth connected zero-dimensional witness. Imperfect lower fields and transcendental upper fields are allowed, because the upper-field additive series is spread before specialization. Empty base schemes give the empty-set pullback equality. All proof steps are under 1000 characters, so none exceeds the 2000-character long-step threshold. No SGA source was used.

## Unfinished work

Only the new model lemma remains unsplit, as required by the one-level split rule. No item clause remains without an argument.
