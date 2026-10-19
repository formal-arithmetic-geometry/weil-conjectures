# Stage-1 split: sk-thm-sf-dual-perfect

## Files written

- `dag/nodes/sec-six-functors/sk-thm-sf-dual-perfect.json`: existing statement, six proof steps; no exact Mathlib match.
- `dag/units/sk-thm-sf-dual-perfect.json`: only `realized` and `realized_by`, for the statement and the single unit proof paragraph.
- `citations.json`: a verbatim statement quotation for every step/node pair.

There are 0 new nodes and 0 Mathlib leaves. Mathlib searches were run through the prescribed msearch command; the node records the exact tool and query from searches.jsonl, together with the returned hits and verdict. The invalid first Loogle query is explicitly distinguished from an absence result. I read the relevant generic rigid-category candidates in Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:266–291 and 386–448 and the closed-category interfaces in Monoidal/Closed/Basic.lean. They do not state the entire geometric coefficient-stage theorem with its specified composite and biduality map.

## Attachments

None for the whole item. In the supplied slopmaster2 checkout, Orientation.lean:183–191 states only Nonempty of an isomorphism, and :197–205 states preservation of dualizability. Their proof bodies contain no sorry, but neither declaration states naturality of the specified composite or compatibility with canonical biduality, and their coefficients are finite. They do not cover all clauses of this item. The generic Perfect/Dual.lean declarations also give Nonempty of comparisons rather than all the assigned canonical-map conclusions. No Lean was written or compiled.

## WANTED

None. The current blueprint, its dual-pair proof, and Stacks ringed-site perfect duality are available.

## Corrections and source comparison

The source is main-20261015/sec-six-functors/sk-thm-sf-dual-perfect, both _section.md and its proof file. Its one paragraph suppresses the evaluation comparison needed to identify the canonical biduality. The split now writes that calculation, the preservation of perfectness, and the inverse on morphisms for the anti-equivalence.

Two imported bibliographic ids have no node files: sk-thm-smooth-purity and sk-prop-sf-dualizable-biduality. I removed the former explanatory parenthesis and replaced the latter reference by the actual definition of coefficient biduality as a transpose of evaluation. The hypotheses, relative scope, canonical composite, naturality, anti-equivalence, biduality equality, and absolute specialization are unchanged. This is a reference repair, not a mathematical STATEMENT-DISPUTED. The existing orientation node already carries the finite-purity and coefficient-transport construction pointers, so no purity proof or forbidden SGA route is introduced here.

The existing expanded node thm-sf-dual-perfect has a relative-form clause giving this theorem together with extra compatibilities; it is recorded in blueprint.same_as. I did not create another copy or use the whole expanded theorem as a substitute for a split.

The inherited lean_audit ranges and transitive open list are stale for the supplied source: Orientation.lean's two declarations are at 183 and 197, not 436 and 456. The listed declaration AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine and its cited file are absent in the supplied slopmaster2 checkout; a declaration-name search in the specified upstream master also found none. I cannot extract a statement from an absent declaration. The proof here does not use an affine cohomological-dimension theorem; I have left the audit fields untouched and report the mismatch for regeneration.

## What could not be finished

No mathematical argument is deferred by this split. Existing dependencies retain their own states. Readiness is conditional on the required no-push dry run printing OK; no push is authorized in this turn.

## Not duplicates

No new nodes. The whole-DAG and blueprint searches for dualizable, biduality, twist-interchange and dual-perfect found the component statements reused here and thm-sf-dual-perfect. The missing sketch proposition is a blueprint section/unit record, not a DAG statement. Its formal dual-pair calculation is expanded inside this item's proof, so no duplicate clause node is proposed.

## Review by Q75

I read the chapter and unit, the current main-20261015 item statement and proof, the sketch perfect-biduality statement and its dual-pair proof, both detailed perfect-dual statements, the actual statements of every node used in the six steps, and the supplied Orientation.lean and Perfect/Dual.lean declarations. I also read Stacks Tag 08JJ, sites-cohomology.tex, lemma-dual-perfect-complex, for the ringed-site comparison; the argument here is the symmetric monoidal dual-pair argument rather than a substitution of a ringed-space theorem or a discrete non-torsion sheaf category.

Step 1 takes precisely the orientation isomorphism from sk-def-sf-orientation, the Hom bifunctor from clause (i) of sk-def-sf-operations, and the displayed shifted comparison from sk-lem-sf-twist-interchange. The orientation is inverted before applying Hom. The statement applies to a relative f and does not require the base to be a point.

Step 2 uses the adjunction in sk-def-sf-operations to define the comparison and prove its naturality by equality of transposes; sk-lem-sf-twist-interchange supplies invertibility at M=L. Its evaluation formula is the defining adjunction equation. I removed prop-sf-dualizable-hom after reopening its statement: it assumes separated X, while the assigned relative theorem allows the general base of the orientation setting. The proof therefore does not borrow its stronger hypotheses.

Step 3 uses prop-sf-dualizable only for its stated perfectness of the coefficient dual. Its local finite-projective hypothesis is supplied by the equivalence explicitly stated in sk-def-perfect. The non-sketch lem-sf-twist-interchange explicitly says the Tate object is locally constant of rank one and invertible. The remaining tensor-and-shift model calculation is written out using def-weil-site-perfect-complex, including its completed integral, localized rational and common finite-field conventions. No uncompleted tensor is substituted for completed tensor. This step supplies perfectness before the later application of theta to DK or K-dual.

Step 4 uses sk-def-perfect for an actual dual pair, not for an unproved assertion of biduality. The adjunction of sk-def-sf-operations identifies the chosen dual with coefficient Hom by evaluation. The displayed inverse to coefficient biduality is checked by exactly the two triangle identities. This is a finite formal calculation from the definition, not an invocation of the absent sketch node or a new node restating the item.

Step 5 uses the same Hom adjunction and opposite-twist interchange, whose perfect first variable has been justified in Step 3. It specifies cancellation on all Hom sets and the corresponding internal maps by transposition, with both inverse formulas. The evaluation equation proved in Step 2 then identifies the transported canonical relative biduality with coefficient biduality. This addresses maps, not merely isomorphic double-dual objects. The derived symmetry retains the Koszul signs and the shift 2d is even.

Step 6 proves naturality of biduality by transposing evaluation and writes the inverse on morphisms. The identity D(delta_K) delta_DK=1 is the evaluation adjunction's triangle calculation, so the asserted anti-equivalence follows with D itself as inverse. The two definitions cited give the absolute names and omega; no absolute Verdier biduality theorem is used to establish a relative result.

I checked K=0, d=0 (including f=id), the unit, a shifted unit, and finite-projective summands. The formulas retain the graded sign for an odd shift of K, and do not divide by a scalar or assume a nonzero stalk, connectedness, properness, finite-dimensional global cohomology or cohomological dimension. Empty schemes cause no failure. Every cited node's actual hypotheses were checked at its use. All coefficient stages stay within the setting fixed by the orientation.

Against delivery-errors B–E: no new nodes need statement-only or leaf checks; exact quotations cover every uses entry; no step borrows another node's proof, no new node duplicates a clause, and no non-elementary geometric fact or coefficient comparison is silently introduced. The unit route remains orientation, twist interchange and coefficient-dual biduality, whose elementary triangle details are expanded. There is no SGA citation. Only the unit's realization fields are changed. All writes are in this sandbox; no git command or compiler has been run in a reference checkout.

On the final C4 check I also opened def-coefficient-twists-detailed and cited it in Step 3: its negative-twist definition is the coefficient dual of the positive power. The step now gives the local evaluation/multiplication and basis inverse proving cancellation, rather than attributing the specific inverse Lambda(-d) solely to a statement saying that Lambda(d) is invertible. The citation file has 16 exact step/node pairs.

## Second reading by Q75

- Item statement: checked against `main-20261015/sec-six-functors/sk-thm-sf-dual-perfect/_section.md` and the imported DAG node; all hypotheses (smooth separated finite type, pure relative dimension, orientation, constructible perfect object, relative and absolute cases) agree, with the two absent bibliography IDs rendered as equivalent plain wording for preflight.
- Step 1: checked against `sk-def-sf-orientation`, `sk-def-sf-operations` (i), and `sk-lem-sf-twist-interchange`; the three cited statements supply the orientation map, internal-Hom functoriality, and the displayed twist isomorphism.
- Step 2: checked the transpose definition and naturality against `sk-def-sf-operations` (i) and the invertible twist comparison in `sk-lem-sf-twist-interchange`; the evaluation formula has the required symmetry and orientation map.
- Step 3: checked `prop-sf-dualizable`, `sk-def-perfect`, `lem-sf-twist-interchange`, `def-weil-site-perfect-complex`, and `def-coefficient-twists-detailed`; finite-projective tensoring, all coefficient stages, and cancellation of opposite twists are stated explicitly, so the step is marked non-elementary.
- Step 4: checked the dual-pair definition and adjunction in `sk-def-perfect` and `sk-def-sf-operations`; both inverse formulas are the two triangle identities and establish coefficient biduality.
- Step 5: checked the internal-Hom cancellation on test objects against `sk-def-sf-operations` and the opposite-twist instance of `sk-lem-sf-twist-interchange`; the construction is internal, with explicit inverse maps and the evaluation transpose identifying the canonical biduality.
- Step 6: checked naturality and the anti-equivalence inverse against the adjunction and orientation statements; the arrow inverse and the double-transpose triangle identity are written out, including the absolute specialization.
- New nodes: none; there are no new node statements or Mathlib leaves to audit, and all cited dependency statements were opened in the shared DAG.
- Edge cases: checked zero and shifted unit objects, (d=0) and (f=\mathrm{id}), empty schemes, finite-projective summands, and odd shifts; no step assumes nonzero stalks, connectedness, properness, or a positive dimension.
- Changes made: replaced the two absent bibliography references in the item statement by equivalent plain wording (the smooth-purity orientation and the transpose definition of coefficient biduality), as required by preflight B3; changed Step 3's `elementary` flag to `false` because its perfectness and inverse-twist argument is substantive. No mathematical clause or proof dependency was otherwise changed.
- Delivery-errors B–E: no new-node B checks apply; every non-elementary dependency is a cited node, no step uses a cited proof body, no duplicate node or cycle was introduced, and no SGA 4/4½ source is cited.
