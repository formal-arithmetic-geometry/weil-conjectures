# Stage-1 worker report: Q114

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-wf-geometric-jacobian-galois-action.json — item, statement corrected and split into six steps; Mathlib verdict: no match after two semantic phrasings, Loogle, LeanSearch and two source greps.
- citations.json — one entry for every cited node in every step, quoting its statement verbatim.
- searches.jsonl — searches actually executed through msearch.py; retained unchanged.
- report.md — this report.

There are 0 new DAG nodes and 0 new Mathlib leaves. The elementary product, conjugation, torsion and inverse-limit calculations are proof steps, not new nodes. No Lean, compiler, Lake or git command was run, and no shared-project or launcher file was written.

## Attachments

None for this item. Searched the entire WeilConjectures/ source for the exact blueprint id, geometric Jacobian, Jacobian/Galois and semilinear terminology, and inspected the matching Picard/Jacobian.lean and AbelianVariety/TateModule.lean declarations. AlgebraicGeometry.exists_jacobian_descent (Picard/Jacobian.lean:2069) gives the existing general-field Jacobian theorem's existence and equivariant point comparison; AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv and galoisRepresentation give general group-scheme point and Tate actions. Neither declaration states this item's complete semilinear action and canonical comparison on the geometric Jacobian scheme. In particular, the current item's lean_audit.slopmaster2 state is none, so these partial matches do not justify ATTACH. No claim of a transitive sorry audit is made for them.

## WANTED

None. The current and older blueprint text and the existing DAG statements required for this split were available locally. No SGA source is used.

## Statement corrected

STATEMENT-DISPUTED: the imported statement labels a left action on schemes by field automorphisms while prescribing id × Spec(sigma). Spec is contravariant, so these scheme automorphisms form a right action: (id × Spec(sigma)) composed with (id × Spec(tau)) is id × Spec(tau sigma), not id × Spec(sigma tau).

An explicit small-case counterexample to the imported scheme-action assertion is C0 = P1 over Q. Its geometric Jacobian is the zero abelian variety Spec(Qbar). Take automorphisms sigma and tau of Qbar whose restrictions to the splitting field of X^3 - 2 are the noncommuting transpositions (12) and (23). The prescribed scheme maps have composites Spec(tau sigma) and Spec(sigma tau), which differ on that splitting field. Thus the displayed left action already fails in genus zero. This is a variance error, not a difficulty with Jacobian existence.

There is also a type error in the first proof paragraph: id_C0 × Spec(sigma) is not a K-morphism of C. Its pullback does not define an ordinary natural endomorphism of the Picard functor on K-schemes with the base parameter held fixed. An ordinary Yoneda endomorphism on that category would represent a K-morphism and cannot give a map over a nonidentity base automorphism. The cited uniqueness statement does not supply a semilinear version of that inference.

The repaired statement fixes multiplication sigma tau = sigma composed with tau, writes s_sigma = Spec(sigma), and uses b_sigma = Spec(sigma inverse) for the base of the LEFT semilinear scheme action a_sigma. On the descended Jacobian model the formula is id_J0 × b_sigma. On geometric points the formula is a_sigma composed with x composed with s_sigma; it becomes u composed with Spec(sigma) on J0(K). On line bundles it is pullback by id_C0 × Spec(sigma). These point and Picard actions are exactly those explicitly stated by thm-pd-jacobian-general-field, and they are the intended arithmetic coordinate actions. The inverse is only the necessary correction to the scheme-level convention.

No hypothesis on C0 was added or dropped. Existence is obtained from the already-cited general-field Jacobian and its base-change clause rather than repeating a separate smooth-connected-implies-integral argument. Torsion equivariance still holds for every prime ell, including the characteristic, and every n >= 1. The inverse-limit module is expressed using the already-existing def-tate-module-abelian-group, which is valid for all primes. Its identification with the abelian-variety definition def-wf-abelian-tate-module is asserted under that definition's explicit ell != characteristic hypothesis. This clarifies the scope of the imported definition without removing the equal-characteristic inverse-limit assertion.

The unit is a definition of Jacobian torsion data with no proof steps, not a unit whose route this repair replaces. The construction still uses the original item's general-field Jacobian comparison, representing uniqueness, torsion and Tate-module route. No chapter or unit record was changed.

## Existing-node and blueprint searches

Ran tools/blueprint_refs.py search for Galois, semilinear and Jacobian, and ancestor for the item. Read the matching Jacobian comparison/uniqueness and Tate definitions and searched all DAG nodes by semilinear/canonical Galois action terminology. The existing general-field theorem already contains geometric-point and torsion equivariance; no second node for either clause was created. The whole item is not stated by another blueprint node: the general-field theorem does not state the transported semilinear LEFT scheme action or its canonicity. The item's same_as is therefore [].

The semantic searches returned Weierstrass Jacobian coordinates, variable changes and Hilbert 90 on the first phrasing, and InfiniteGalois limit maps and pre-Galois category automorphisms on the second. LeanSearch returned field/integral-closure Galois actions. Loogle with AlgebraicGeometry.Scheme and galois had no hits. The first Mathlib source grep returned only elliptic-curve Jacobian-coordinate files, whose Basic.lean introduction and definitions were opened: these are weighted projective coordinates for Weierstrass curves, not Jacobian varieties representing Pic0 of arbitrary curves. The second grep returned Weierstrass Picard comments and semilinear structure-sheaf maps. None states the item's geometric Jacobian, Picard comparison and semilinear action. All actual query texts, results and verdicts are in the item and the command-generated search log.

## Downstream audit

Four existing nodes cite the item: lem-wf-curve-kummer-jacobian-tate-module, lem-wf-curve-h1-dual-tate-module, lem-wf-finite-field-tate-no-fixed, and lem-wf-proper-curve-compatible-h1-no-fixed. Their uses concern the coordinate Galois action on points, the Picard comparison, torsion, or the induced Tate module; these conclusions are retained with explicit formulas. The first proof step of lem-wf-finite-field-tate-no-fixed still repeats the old ambiguous scheme expression id_J0 × sigma_Q and allows either inverse convention on points. Maintenance should replace that scheme expression by id_J0 × Spec(sigma_Q inverse) and use the unambiguous arithmetic point formula. Its fixed-vector conclusion is unaffected; I did not edit another worker's node. The proper-curve node already distinguishes arithmetic from geometric action on the Tate factor.

## Review by Q114

I read the item statement and both proof paragraphs in literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-d-real-jacobian/lem-wf-geometric-jacobian-galois-action.md, and the separate statement and proof files in the main-20261015 snapshot. They have the same variance problem. I also opened the main-20261015 general-field Jacobian statement and proof, specifically Steps 8–11; that proof explicitly says that the two contravariances (Spec and the functor) produce a left point action. I checked the current DAG statements themselves, not just those blueprint proofs, for every citation. No new nodes require further literature or statement tests.

Step 1 uses thm-pd-jacobian-general-field for a model over the actual arbitrary ground field, its representation and its base-change clause. All its hypotheses are present and it assumes no rational point. def-sc-jacobian supplies the fixed representing isomorphism of the input J. lem-sc-jacobian-unique states precisely the unique GROUP-SCHEME isomorphism respecting the two representing isomorphisms; I used it for alpha, rather than attributing group-law preservation to a statement about representing schemes alone. The general-field theorem itself calls the base change a Jacobian, so its base change has the hypotheses of that uniqueness comparison.

Step 2 is an elementary fibre-product calculation, without a hidden purity or descent theorem: the two projections specify every map, its inverse and its composition law. I checked the ordering of field maps under Spec explicitly. The multiplication diagram is checked on the J0 projection, where it is the original multiplication, and the base projection, where it is b_sigma. The same projection check gives the unit and inverse diagrams. This works also for the zero Jacobian, the identity automorphism and an arbitrary imperfect ground field.

Step 3 uses lem-pc-representable-unique exactly for an isomorphism between two representatives of the same functor with fixed representing isomorphisms, first over k0 and then over K. It is not used for the general Yoneda lemma on arbitrary natural transformations or for semilinear representability. The remaining equations are substitution and equality after the two product projections; these prove independence of the model rather than silently saying 'transport'. The group isomorphism needed for the construction was already obtained in Step 1.

Step 4 uses the actual equivariant geometric-point clause of thm-pd-jacobian-general-field, whose statement spells out BOTH the point action u composed with Spec(sigma) and the pullback action on Pic0. The displayed base map cancels to the identity, so the twisted formula really is a K-point. I expanded the double composition and the formula under alpha to verify the exact left action, rather than using an unspecified convention on geometric points. Compatibility with the given representing isomorphism is part of the choice of alpha from Step 1.

Step 5 cites the same theorem's explicit torsion clause; it applies to every prime and positive n, without an etaleness or invertibility hypothesis. The transition calculation Phi(ell z) = ell Phi(z) follows directly from its group-valued identification. No claim about finiteness or etaleness of characteristic-primary torsion is used.

Step 6 cites def-tate-module-abelian-group for the exact compatible-sequence model and the residue definition of Z_ell scalar multiplication, and def-wf-abelian-tate-module for its explicit agreement with that group Tate module when the characteristic hypothesis holds. I checked each defining condition after applying sigma, the identity and multiplication laws coordinatewise, and commutation with a scalar via an integer residue. Thus no inverse-limit exactness or continuity theorem is being smuggled into a definition citation. The assertion is an abstract group-ring module, as in the imported item; no unproved topological continuity assertion is added.

For delivery-errors B–E: all introduced objects and conventions are explicit in the corrected statement; no unsplit or duplicate new node was introduced; TeX has single backslashes after JSON decoding; every proof citation is backed by a verbatim statement quote in citations.json. The only non-elementary steps are applications of the existing general-field theorem and Jacobian uniqueness, and they cite those statements. Every step is below 2000 characters. The explicit genus-zero noncommuting example checks the corrected variance, and the inverse-limit argument also handles the zero module and characteristic-primary torsion. I corrected the false functor-endomorphism inference and the missing point twist rather than moving either clause into a new node. Off-unit uses are declared in split_report.tool_uses for the maintainer to accept. No maintainer-owned field was changed.

## Unfinished work

None in this stage-1 split. The downstream notation repair described above is outside this item's edit scope. Independent mathematical review remains the maintainer's responsibility.

## Validation

Server review_split passed before this report was written, with zero new nodes. The full deliver.py --no-push run exited successfully with preflight passed (dry-run commit 58ecbb990d). A final rerun checks this corrected source line reference before the authorized push.
