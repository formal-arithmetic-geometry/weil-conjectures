## Files written

- `dag/nodes/sec-trace-formula/lem-trf-relative-proj-invertible-twist.json`: statement node, now split into seven proof steps; Mathlib searches found no matching relative projective-bundle theorem.
- `citations.json`: 22 verbatim statement quotations covering every step/node citation.
- No new DAG nodes and no Mathlib leaves were created. `searches.jsonl` contains the six searches actually performed in this sandbox; their records were appended to, rather than substituted for, the item's inherited search history.

## Attachments

None. Searches under WeilConjectures in slopmaster2 for the exact blueprint id, 02NC, relative Proj, projective bundles and twisting found no project declaration giving this statement. The upstream master reference likewise supplies no finished attachment for this item. The existing project twisting-sheaf declarations concern O(m) on an absolute Proj, not invariance of P(E) under a line-bundle tensor factor.

## WANTED

None. All sources needed here are present locally.

## Corrections and scope

The statement is unchanged. The imported item had no proof: Stacks 02NC's instruction to trivialize and glue did not yet expose the independence from a generator. The split now proves that independence on homogeneous degree-zero chart fractions, and explicitly verifies restriction to affine refinements, gluing and the inverse equations. The proof follows 02NC, not a replacement route through a new theorem restating its conclusion.

I read the chapter sec-trace-formula and unit sk-i-curve-zero. This is a generic geometric tool below the inherited 087S projectivity-conversion chain, specifically step 2 of lem-trf-projective-bundle-to-h-projective, rather than the key node of that unit. No chapter or unit file is changed. The blueprint ancestry and via chain are retained; whole-blueprint searches for '02NC', 'projective bundle' and 'twisting proj invertible module' found no duplicate statement, so same_as remains empty. The generic off-unit tools are declared individually in split_report.tool_uses; they implement the stated trivialize-and-glue route.

The human's stage-1-only restriction was followed: no Lean was written and no compiler, Lake or build tool was invoked. No live-project or launcher file was edited. All generated files are in the item sandbox.

## Unfinished work

None in this one-level split. The cited nodes retain their current states and are not edited or silently assumed Lean-closed.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The tag search finds the item and lem-trf-projective-bundle-to-h-projective: the latter converts projective-bundle projectivity to H-projectivity under an ample-line-bundle hypothesis and uses this twisting lemma; it does not state it. The imported projective-bundle geometry elsewhere assumes a locally free module and supplies tautological and base-change properties, rather than the present arbitrary finite-type quasi-coherent E twisting statement.

## Review by Q66

I read constructions.tex Tag 02NC, label lemma-twisting-and-proj, including its context defining the graded twist and its entire proof (lines 4565–4640), and Tag 01OB, definition-projective-bundle, immediately following it. The item is the projective-bundle specialization with the line bundle L tensor-powered n times; it neither assumes E locally free nor assumes S Noetherian, quasi-compact or separated. The construction below uses the same trivializations as 02NC and proves the gluing calculation omitted there. I also read constructions.tex Tag 01MY, lemma-morphism-proj, property (2) and proof, and Tag 01NQ, lemma-glue-relative-proj; modules.tex 01CG, lemma-local-tensor-algebra, and 01CL, lemma-whole-tensor-algebra-permanence; schemes.tex 01IT, lemma-basis-affine-opens; and the gluing discussion recorded by the existing scheme-morphism-gluing node (including the mapping property of gluing in sheaves.tex 00AN). There are no new nodes requiring a separate source audit.

For step 1 I opened def-sc-invertible-module, def-pur-sheaf-tensor-product, pqf-def-coherent and lem-weil-pbc-affine-opens-basis. The first really gives local rank-one frames, the tensor definition gives the displayed mutually inverse maps, and the affine-basis lemma permits refinement. The two locality clauses of pqf-def-coherent prove that E' has the required quasi-coherence and finite-type properties; this is not an uncited general tensor-permanence theorem. L tensor-powered zero is explicitly the unit, avoiding an unmentioned positivity restriction.

For step 2 I opened the entire statements of lem-weil-pbc-quasi-coherent-symmetric-algebra and lem-weil-pbc-symmetric-algebra-graded. The first gives quasi-coherence, the sheaf universal property, functorial maps and the affine-section identification, exactly as used. The second gives the symmetric grading and its monomial generators, so the maps preserve degree and later scale degree k by u^(nk). Uniqueness in the first statement makes the two maps inverse. No theorem about Sym(E tensor L) being a graded twist is imported without a node: the proof constructs and compares the local algebra maps directly.

For step 3 I opened def-nagata-homogeneous-localization-degree-zero and def-weil-affine-spectrum. The former supplies the full fraction relation and degrees, not a claim about a special domain, and the latter supplies the contravariant spectrum functor and uniqueness of the ring map. The step actually proves the localization formula and its inverse, rather than taking a formula out of the proof of another node. Applying an algebra isomorphism preserves every localization relation, including when a denominator is zero or nilpotent.

For step 4 I opened prop-nagata-proj-standard-open, lemma-nagata-proj-chart-ring-cocycle, lem-weil-pbc-scheme-morphism-gluing and def-nagata-relative-proj. The first states both the chart-ring identification and the cover; the second states that the overlap equivalences are induced by localization and satisfy the cocycle; the third supplies existence and uniqueness for compatible morphisms; the fourth gives the actual affine-base restriction identifications. Consequently the gluing step is supported by statement-level assertions, not merely a definition of Proj or the internal construction of one of these lemmas. Compatibility of the fraction maps with localization is checked on numerator and denominator; inverse equations are checked chartwise and then use uniqueness.

For step 5 I rechecked the rank-one-frame definition and the monomial-grading statement against every exponent. On W, e_j=u e_i gives beta_j(a)=u^(nk) beta_i(a) in degree k. A numerator over f^m has degree md, hence both numerator and denominator gain u^(nmd); this is the reason the fractions agree. Only a unit is cancelled. This two-line calculation is elementary once the cited grading and fraction definitions are in place and does not warrant a new node restating invariance under scalar multiplication. The chart opens are the same because multiplying a homogeneous element by a unit does not change the primes containing it.

For step 6 the symmetric-algebra theorem's functorial uniqueness identifies the restriction of beta_i with the map of the restricted module; def-nagata-relative-proj explicitly specifies the coefficientwise localized restriction maps. I checked that applying coefficient restriction before or after the numerator/denominator formula gives the same answer. No claim that an arbitrary intersection of affine opens is affine occurs here.

For step 7 the affine-basis theorem covers every intersection by affine refinements. The chart theorem, spectrum-map uniqueness and scheme-morphism-gluing then turn the explicit equalities in steps 5–6 into equality of local maps, and subsequently glue the maps and their inverses. The gluing node's uniqueness also proves the global inverse equations, the equality with the structure morphisms and independence of all frame and cover choices. The projective-bundle definition is cited only for the meaning of P(E), not for a gluing or twisting theorem it does not assert.

Against delivery-errors B–E: every use above was checked against its node's statement and every quotation in citations.json is copied from that statement; there are no new-node format, source-tag, hollow-definition or missing-notion issues. There is no new statement that is a clause of this item, no proof moved into a child node, and no backward dependency on the parent. All seven steps are below 2000 characters. The non-elementary constructions (Sym, Proj charts and gluing) have cited nodes; the elementary steps are only explicit inverse maps, fraction calculations or restrictions. The six logged searches include two concept phrasings and grep of the actual Proj source directory. I read their hits: the tensor-equivalence hits concern ordinary modules, projective-point scaling concerns a different object, and the Proj hits concern affine charts or properness, not a relative line-bundle twist. No hit is falsely marked a match or unavailable.

Small-case checks: n=0 gives the identity after unit identifications; L globally trivial gives the isomorphism induced by the chosen frame, independent of any other frame by the same unit calculation; E=0 gives empty Proj on both sides; E of rank one gives the expected identification of its projective bundle with S locally; an empty base gives only empty schemes and the gluing equations are vacuous. Torsion and non-locally-free E cause no problem because the maps use actual module isomorphisms, and nonreduced bases cause no problem because cancellation is only by units. No finite-type-base, characteristic, coefficient-ring, separation or quasi-compactness assumption has been added.
