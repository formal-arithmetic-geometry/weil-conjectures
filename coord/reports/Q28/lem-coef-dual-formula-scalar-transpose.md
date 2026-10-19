## Worker report

Files written:
- `dag/nodes/sec-six-functors/lem-coef-dual-formula-scalar-transpose.json`: statement, statement dependencies and historical fields retained; eleven proof steps; status split.
- `dag/nodes/sec-six-functors/lem-coef-finite-free-compact-composition.json`: one new statement-only node; status unsplit; no Mathlib match.
- `citations.json`: for each cited node of each item step, its full verbatim statement, so the manifest retains all hypotheses and every clause used.

Attachments: none. A search of WeilConjectures/ for the exact blueprint tag and for scalar/duality/transpose terminology found no declaration of this integral pro-etale identity. I read the relevant coefficient-change and Verdier-exchange declarations in `WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean` (in particular the generic coefficient-change two-square around lines 179-250 and finite etale exchange around lines 320-435). They concern finite ordinary etale categories and comparison squares whose exceptional comparisons are already mates; they do not attach this integral formula identity. The master checkout was not treated as a proof certificate.

WANTED: none.

The item is a supporting lemma extracted from `lem-coef-rational-operations`. I read its current `blueprint_update.proof` paragraph 8 and the main-20261015 blueprint statement at `sec-six-functors/sk-thm-sf-package/lem-coef-rational-operations.md`. The sentence about transposing the dual-formula comparison is the place realized here. I also read the actual four-arrow Hom proof in the master's `sk-prop-sf-biduality-general/lem-coef-finite-exceptional.md` and the current finite-exceptional node's explicit absolute-trace construction. This proof is marked agent-written because it expands that assertion. It uses no prohibited source or purity route.

The unit is `sk-prop-sf-biduality-general`; I read its record and the chapter record. This is supporting coefficient transport within the integral-to-rational route. It is not the unit's key statement, so no unit binding is edited. Blueprint searches `scalar duality`, `transpose scalar`, `absolute trace` and `compact coefficient composition`, and the whole-DAG searches, found no blueprint node with the exact item or new statement. The ancestor is `lem-coef-rational-operations`; the new node records the item in `from.via`.

## New nodes

`lem-coef-finite-free-compact-composition` states the finite-free coefficient square for compact-support composition along arbitrary composable separated finite-type maps, including its identity on specified coherent coefficient-system constructions. It contains no duality, formula identification, exceptional counit, or conclusion of the item. It is not a relabeling of the item. The natural route for its later split is to compare the proper/open compactification composition construction and its units/counits under restriction and finite-free extension, then realize the same identity on the simultaneous section models. Mere naturality of an unspecified coefficient-level composition map would not suffice. The statement introduces all fields, rings, schemes, domains, comparisons and system conventions; it has no proof or proof dependency.

The new node was searched with msearch.py in all four services/kinds, including two semantic phrasings and two grep patterns. Queries and service responses are in searches.jsonl and were read. LeanFinder returned ordinary Scheme.Modules pushforward/pseudofunctor composition; Loogle returned generic mate-pasting identities; LeanSearch returned algebraic/continuous-map scalar facts; grep returned linear-category scalar axioms and topological compact support. None is the compactified derived pro-etale coefficient square. No unavailable service was recorded as a negative result. The item also has newly run searches as well as its retained inherited searches. No unrun query is claimed.

## Not duplicates

lem-coef-finite-free-compact-composition vs lem-sf-compact-coefficient-composition: the existing node only covers the quotient of two powers of one uniformizer; the new node covers the finite-free map A_n to S/pi^n S, and states the corresponding coherent identity. A quotient cannot be substituted for this extension.

lem-coef-finite-free-compact-composition vs det-prop-scalar-six-compact-support: the latter uses the condensed module-object framework and listed coefficient maps. The new node concerns ordinary constant finite-coefficient module sheaves, without identifying the two frameworks.

lem-coef-finite-free-compact-composition vs lem-coef-finite-free-extension: the existing node gives direct-image, closed-exceptional, dualizing and internal-Hom comparisons with coefficient and adjunction compatibility; it does not state the compact-support composition square for f and g.

lem-coef-finite-free-compact-composition vs lem-pur-composition-comparison-scalar-compatibility: the existing node concerns rational smooth exceptional/purity comparisons, not finite compact-support composition for arbitrary separated finite-type maps.

lem-coef-finite-free-compact-composition vs thm-sf-comp-composition: the existing node gives fixed-coefficient compact-support composition and associativity; it has no finite-free coefficient square.

## Review by Q28

I read the item and new statement alongside the sources named above, and opened the statement of every cited node. I kept all hypotheses of the item. In particular B_n is A_{L,en}, not A_{L,n}; the completed coefficient sheaves are ordinary sheaves, not condensed ring objects. The fixed compactification and canonical evaluation/counit normalizations are retained. No statement dispute was found.

Step 1 uses finite-free extension for the coefficient indices and actual comparison maps, finite exceptional preservation and finite biduality for their domains, pullback-Tor preservation for Q, and flat models plus constructible tensor cohomology for the absolute-adjunction tensor inputs. I checked that the latter tensor theorem only asserts constructible cohomology: the required boundedness is supplied separately by the flat models. Finite dimensionality supplies a bound (zero on the empty scheme), ordinary adjunction uses only clause (1) of fix-prop-adjunctions, and ordinary direct-image finite-Tor preservation restricts that adjunction. The constructible-origin equivalence supplies the etale-origin hypothesis of finite composition. No exceptional admissibility datum is assumed.

Step 2 uses exactly the composition isomorphism of thm-sf-comp-composition, the finite-Tor projection isomorphism of fix-prop-projection-formula, and the structure-morphism exceptional adjunction of lem-coef-finite-exceptional. I checked the source and target of the displayed trace equation: both start at P_Y(FK tensor D_YM).

Step 3 uses the Hom-action clause of lem-sf-absolute-trace-exchange, not merely its invertibility conclusion, and the actual finite double-dual map. Expanding its two evaluation symmetries recovers the four-arrow Hom chain of the source, which is the normalization of kappa. The finite-diagram realization statement supplies that tensor-Hom evaluation transpose as a system map with the same finite counit. I checked the direction: Psi takes a map into D_X f* D_Y M to FK -> M, and hence Psi(kappa z)=epsilon Fz.

Step 4 uses the explicitly counit-normalized dualizing comparison of lem-coef-finite-free-extension. I corrected an early draft here: it tried to justify the coefficient/composition square by an informal diagonal-matrix argument. The fixed-coefficient composition statement does not identify its realizations over two coefficient rings. I replaced that inference with the new, strictly smaller composition node. The quotient-composition node and the condensed coefficient node are deliberately not applied outside their hypotheses.

Step 5 uses precisely evaluation compatibility in finite-free extension and tensor reassociation in the finite pullback definition. I checked q:TQ_A -> Q_B and D(q^-1):D(TQ_A) -> D(Q_B); the order inside the contravariant dual is the order in the item. Substitution cancels q^-1 q. This is elementary from the cited evaluation identity, not a geometric lemma.

Step 6 uses the scalar-compatibility clause of projection and the already established absolute trace and composition squares. Both candidate maps into omega_Y are transposed under the actual absolute adjunction from the finite-exceptional node. I checked their common transpose, including precomposition by alpha_Y. Step 7 uses evaluation/double-dual preservation in the finite-free statement and finite biduality to cancel delta. The Koszul symmetries occur in the same order on both sides. Step 8 merely specializes that Hom square to K=G_AM and h=kappa_A; the cited finite-scalar-mate node specifies precisely the transpose that results. These three steps do not use that node to assert the desired dual-formula equality.

Step 9 uses the statements of the finite adjunction-diagram realization, semilinear sections, system evaluation calculus, new composition node and finite-scalar-mate realization. I checked the restriction on fiberwise internal Hom: all its first inputs here are cartesian normalized systems. Each equality is formed by evaluation, transpose, cancellation or the new coherent composition equation on the supplied simultaneous models; it is not inferred from faithfulness of evaluation on morphisms.

Step 10 uses the specified integral adjoint/formula, integral Verdier evaluation comparisons, integral finite-extension evaluation comparisons and pullback reassociation. The evaluation calculus expresses the substitution as e_N R(b')=b'_bullet a, an identity of system constructions. Step 11 explicitly applies the reduction/limit adjunction, not a supposed injection of integral Hom into the product of finite Homs: both maps have the same actual system adjoint b_bullet a, so the adjunction bijection identifies them. Its unit/counit formulas are in the calculus statement. Total inverse limit is a functor by the strict-tower theorem, finite-free completed-scalar comparison fixes the source completion, and the finite-scalar-mate statement identifies the total-limit map's exceptional transpose. This gives the exact equation of the item.

I checked E=L (all coefficient comparisons are units), f=id (the two duality comparisons combine by actual biduality), M=0 and empty X or Y (all pairings and equations reduce to the unique maps of zero objects). For the new composition statement I also checked f=id, g=id, K=0 and an arbitrary ramified extension: the exponents remain en in both routes, and neither smoothness nor flatness of a quotient is used. No uniform Tor interval is imposed on an arbitrary normalized system in the new statement; the finite hypotheses are checked at each level.

The new statement has no proof sketch; each notion has a definition reference or an inline meaning. All new-node searches are logged. I checked B-E against these files: no item clause moved to the child, no claim is taken only from a cited node's proof, no hypothesis is silently strengthened, no integral Hom faithfulness or ambient exceptional adjoint is used. The source's omitted transpose argument is now the item's Steps 2-8. Every proof step is below 2000 characters and the longest ones are single Hom/evaluation computations rather than concealed geometric lemmas. The manifest quotes entire statements verbatim to avoid dropping qualifiers. Generic off-unit tools and why they are tools are listed in split_report.tool_uses, with no maintainer-owned tool_uses field added.

All work stays in the Q28 sandbox. No Lean file, compiler, Lake command, live project file or launcher file was written or run.

## Validation

The full deliver.py --no-push run exited successfully: OK (not pushed), preflight passed, commit 31e1b1706d. This includes the server DAG and split review checks, citation validation and logged-search validation. Server review_split also passed during drafting. The report records this completed check; the final report text is checked again before the direct push.
