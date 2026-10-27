# Q128 — lem-a1-total-limit-shift-resolution-change

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-total-limit-shift-resolution-change.json: statement, split in seven proof steps; inherited statement unchanged; not a Mathlib leaf.
- citations.json: twelve step/node quotations copied verbatim from the cited statements.
- searches.jsonl: actual Q128 searches made by msearch.py; inherited Q27 searches remain intact in the item.
- report.md: this report. No new nodes, no Mathlib leaves, no Lean files.

## Attachments

None. Searched the entire live WeilConjectures source for the blueprint tag and limit/shift/K-injective terminology. Generic rightDerivedFunctorObjQIso and K-injective resolution declarations cover ingredients, not all clauses of this item. No project declaration found stating the whole result. The Mathlib K-injective Hom and shift declarations already belong to existing leaves.

## WANTED

None. The Stacks source and current blueprint are present locally.

## Corrections and route

The imported item had no proof, although its search history correctly identified generic ingredients. Its statement is sound and was retained verbatim. The recorded nearest blueprint ancestor is lem-a1-finite-map-purity. Read the current main-20261015 finite-map-purity statement/proof and its chapter and unit: the unit's finite-stalk/Frobenius route is unchanged. This item serves the later integral comparison and normalized Roos shift refinements recorded in its ancestry, not an alternative proof of finite-map purity.

The useful existing general node lem-sf-kinjective-derived-map-computation gives the arbitrary-derived-morphism formula and changes of K-injective resolution. Reusing it avoids creating nodes restating clauses of the item. The proof still supplies the actual termwise-limit homotopy and shift computations, cancellation of resolution comparisons, the derived naturality square, and zero/addition coherence.

Tool uses of lem-weil-pbc-ringed-strict-tower-homotopy-limit and lem-sf-kinjective-derived-map-computation are declared in split_report.tool_uses. These are generic unbounded derived-category tools for the integral comparison; the affine-line unit provides no replacement for either. The K-injective Hom and shift nodes are existing Mathlib leaves. No SGA source is used.

## Not duplicates

No new nodes were created. Searched the whole DAG by K-injective, total right derived, termwise limit/shift, and the Stacks tags 070I and 070Y; searched imported blueprint records with blueprint_refs.py. Reused the general map computation, Hom bijection, shift lemma, and total-derived unit definition. Neither bounded-below InjectiveResolution naturality nor the exact-functor mapDerivedCategory shift declarations state the whole item: the former works on nonnegative injective resolutions, and the latter assumes an exact underived functor. Inverse limit here is merely additive, without exact countable products.

## Review by Q128

I read derived.tex Lemma 070I (lemma-K-injective), its proof of the Hom bijection, Lemma 070Y (lemma-K-injective-defined), and Lemma 070K (lemma-enough-K-injectives-implies). I also read sites-cohomology.tex Section 0940 (section-derived-limits), including Lemma 0941 (lemma-derived-limit-is-ok). The latter uses a degreewise-injective representative for its product triangle; I do not apply that extra condition to arbitrary resolutions. Arbitrary-resolution computation instead uses the full statement of def-sfb-right-derived-functor and the generic map formula, which explicitly require only K-injectivity. I checked the actual Mathlib KInjective.lean Hom and shift declarations, HomotopyCategory/Shift.lean's additive-functor shift construction, and DerivedCategory/ExactFunctor.lean to distinguish its exact-functor hypotheses from this item. These searches found ingredients, not a one-line specialization proving the item.

For step 1 I opened def-weil-sheaf-of-modules-category and used its sectionwise module morphisms to construct compatible tuples. Gluing is coordinatewise; joint monicity of projections proves additivity. Applying that additive functor to the explicit homotopy equation gives exactly the limit homotopy. This is a direct calculation, not a claim that ordinary limit is exact.

For step 2 I opened lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-sfb-right-derived-functor and def-weil-abstract-derived-category. The first supplies the total-derived tower construction; the second explicitly supplies the natural unit and its invertibility on every K-injective; the third inverts q. Multiplication by L(Q_Tq) inverse gives existence and uniqueness of d_q. Module sheaves on a site small in the module universe and their strict towers are precisely the setting of the tower computation node, so no boundedness or product-exactness hypothesis is imported.

For step 3 I opened lem-weil-pbc-kinjective-hom-derived. Its Hom bijection applies first to I,J, then to X,J, and also to J,I for the inverse. Thus the comparison is a homotopy equivalence, and the equation vq homotopic to q' follows from injectivity, rather than from an unjustified strict lift. The unit naturality used here is explicitly part of def-sfb-right-derived-functor. The displayed cancellation yields d_{q'} Q_A(limit v)=d_q with the correct orientation. Step 1 proves representative independence.

For step 4 I opened lem-weil-pbc-kinjective-shift; it explicitly covers both shifts of K-injective complexes and shifts of resolutions for all integers. The remaining square is checked in each degree as limit v_n^{i+r}; the differentials on each side are (-1)^r limit d. The tuple identities give zero and addition before localization, and def-weil-abstract-derived-category supplies the localized shift identifications. Negative shifts have the same parity/sign calculation.

Step 5 uses the equations already proved in steps 3 and 4, not an additional comparison theorem. I checked all domains: E goes from limit I to limit J, E_r from limit(I[r]) to limit(J[r]), and Lambda_J E_r = E[r] Lambda_I. Substituting d_q=d_{q'}E and its shifted counterpart cancels E_r inverse in precisely that order.

For step 6 I opened lem-sf-kinjective-derived-map-computation. Its statement quantifies over every derived h and explicitly gives c_b RF(h)c_a inverse=Q_B(Fg), so it is sufficient for the step's arbitrary-derived-morphism assertion. Its inverse comparison is exactly d, hence L(h)d_q=d_p Q_A(limit g). Its resolution-existence premise is supplied by the existing strict-tower computation, and step 1 proves additivity. Applying it again to q[r],p[r] and g[r] is justified by step 4 and the canonical Q shift identification. The displayed square and cancellation prove full naturality, not only strict-map naturality.

For step 7 I checked the zero identity directly. For addition the two middle d comparisons cancel using the simultaneous shifted resolutions; the tuple lambda identity is already proved in step 4. The source reindexing must also be transported: the proof explicitly introduces the canonical a_X and a_I and applies step 6 to their strict commuting square, giving L(Q_Ta_X)d_{q[r][s]}=d_{q[r+s]}Q_A(limit a_I). This supplies the previously easy-to-hide associator comparison. The only new citation here is def-weil-abstract-derived-category for the prescribed shift identifications; the rest is substitution into proved equations.

I checked zero complexes, the identity resolution of an arbitrary K-injective, identity homotopy comparisons, distinct representatives in one homotopy class, r=0, r=1, r=-1, and r+s=0. In the identity-resolution case d_id=eta_I; the shift formula then has the required unit normalization. A two-term acyclic noncontractible complex is never assumed K-injective. Ordinary inverse limit is never applied to an arbitrary quasi-isomorphism with a claim it remains one; only homotopy equivalences between K-injectives are used. No degree-term injectivity or exact countable products is required. I checked delivery-errors B–E: no new-node obligations, no clause moved to a new node, no proof-only citation, all cited statements read, and all twelve quotations verified as literal substrings. All seven steps have fewer than 2000 characters; the longest is the explicit associator cancellation, not a hidden auxiliary lemma.

## Unfinished work

None in the stage-1 split. No statement dispute or missing literature. Delivery verification is recorded by the required deliver.py invocation.
