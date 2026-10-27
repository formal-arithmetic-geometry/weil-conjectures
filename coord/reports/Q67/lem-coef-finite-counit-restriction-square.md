# Stage-1 report: lem-coef-finite-counit-restriction-square

## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-counit-restriction-square.json`: statement node, now split into six steps. No exact Mathlib match. The statement, statement dependencies, source, provenance, and earlier searches are retained; five searches actually run for Q67 are appended.
- `citations.json`: one verbatim statement excerpt for each node cited by each proof step.
- `report.md`: this report.

There are zero new nodes and zero Mathlib leaves. No unit or chapter file is changed. All writes are in this item's sandbox; no Lean was written or compiled, and no git command was run in the shared repository.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for counit/restriction, dualizing/coefficient, finite-dualizing counit, and quotient-counit notions. The results concern ordinary scalar adjunctions, unrelated open or closed counits, or only ingredients. For example, the project’s `ProEtale/FiniteCoefficient/Derived/AlgClosedField.lean` proves projectivity of the unit and vanishing of degree-one self extensions, not this item. No project declaration found states all of this item's clauses.

## WANTED

None. The relevant blueprint and Stacks sources are available locally.

## Problems found and changes

The live item was statement-only and had no Lean audit/declaration attachment. The sandbox contained no earlier item, report, citations, or searches to resume. I retained the imported statement exactly and supplied the explicit argument that its source's final sentence leaves implicit. The restriction square is obtained by applying restriction to the finite counit identity and using the scalar unit's naturality. The target comparison is normalized by constant sections; the scalar unit followed by the multiplication unitor sends `a` to its actual quotient class, so it cannot introduce an unspecified automorphism of the target.

The underlying blueprint source is `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-dualizing.md`, proof paragraph 2, final sentences. I also read the current `main-20261015` separate proof file under `sec-smooth-purity/sk-lem-sp-tower/`, which has the same final counit-normalization argument, and its `lem-coef-finite-dualizing.proof.md`. This stays on the finite-adjunction/coefficient route; it introduces no purity or ambient pro-etale exceptional-adjoint premise.

The existing finite-dualizing node already supplies the counit equation, quotient cocycle and specified finite pro-etale realization. The existing point extension/sections node already supplies exact sections and the constant-value coefficient-ring isomorphism. Making either into a new node here would duplicate existing material. The remaining calculations are short arguments within the proof, not new nodes.

## Not duplicates

No new nodes. The whole-DAG keyword searches and `tools/blueprint_refs.py search` queries `counit restriction`, `finite counit`, `quotient targets`, and `dualizing` were used to locate existing results. The blueprint ancestor is `prop-coef-integral-dualizing`; the item's existing `from.place` and `via` are retained and `same_as` is empty. The broader finite-dualizing result does not itself state the restriction square with the point-section quotient normalization, so it is a dependency rather than a merge or exact attachment.

## Mathlib searches

The sandbox's `searches.jsonl` records the five calls made with the required `msearch.py` command: LeanSearch, Loogle, grep, and two different LeanFinder phrasings. All services answered. I read the returned hits. The LeanFinder hits concern ideal quotients or algebraic traces. The grep hits concern bialgebra and coalgebra quotient counits. LeanSearch includes abstract derived counits, coextension adjunctions, and unrelated coalgebra results. Loogle finds abstract unit/counit naturality, including `CategoryTheory.Adjunction.unit_naturality`; I read its actual declaration at Mathlib/CategoryTheory/Adjunction/Basic.lean:291. It is the direct naturality calculation used in step 2, but it does not state the geometric item, its coefficient realization, or its target normalization. Accordingly the item remains a split statement, not a Mathlib leaf. All earlier searches in the copied item are preserved as inherited records; none is presented as a new Q67 call.

## Review by Q67

I read the worker brief, all of delivery-errors B--E, the stage-1 contract, the three-level route rules in SETUP, GOAL, the chapter and unit records, and the item and all statements cited below. The unit has no recorded proof steps to realize here, and this item is not its key statement. The natural-language proof is agent-written: the blueprint supplies the counit-normalization route, while the explicit scalar and section calculations are written out here.

Step 1 uses `lem-coef-finite-dualizing`. Its statement gives exactly the counit identity for the specified comparison, not merely existence of some dualizing isomorphism, and explicitly identifies the finite pro-etale realization. I substituted its large coefficient ring A=A_m and small ring B=A_n, inserted the scalar-unit isomorphism that its equation suppresses, and cancelled the displayed inverse of c. The hypothesis m>=n>=1, the finite-field datum, and the separated finite-type structure morphism are all precisely the item's hypotheses. The compactification is kept fixed throughout.

Step 2 uses `def-coef-normalized-dvr-tower` only for the tensor-restriction adjunction and its unit. Naturality here is part of being a natural transformation: the proof displays the entire equality and its substitution into the composite defining d. It does not take a theorem about flatness or exceptional functors from a definition. The categorical naturality lemma was also located and read in Mathlib; there is no reason to create a separate node for this one-line calculation.

Step 3 uses `lem-pod-point-exact-extension-sections`. Its statement explicitly asserts both exactness and the constant-value ring isomorphism, so it is sufficient to identify derived sections of the degree-zero regular coefficient object with A_n[0], including the actual constant-section normalization. Its finite alternative applies here; no completeness assertion for integral coefficients is used. For the exactness source I additionally read Stacks proetale.tex, labels `lemma-w-local-strictly-henselian-extremally-disconnected` (0982) and `lemma-w-contractible-is-weakly-contractible` (098H), including the latter's lifting proof: the algebraically closed point is weakly contractible. This is consistent with the supplied point-section statements. This citation is declared as a generic tool use because the item's own unit has no separate point-normalization statement.

Step 4 again uses the explicit tensor-restriction unit formula in `def-coef-normalized-dvr-tower`, not an identification of an arbitrary derived tensor with an ordinary tensor. Only the regular A_m-module sheaf is used as a degree-zero flat rank-one model. The composite is a -> a tensor 1 -> q(a). The constant-value map of step 3 sends each coefficient to its own constant section, so evaluating this formula gives precisely the R-linear quotient. No arbitrary choice of an isomorphism A_n[0] with the target is made.

Step 5 is just application of a functor to the step-2 equality and substitution of the step-4 formula. All finite objects and maps are restricted to the original constant valuation ring R before comparing them. Its equality lives in D(R), not just in its degree-zero cohomology. No further lemma is hidden in this step.

Step 6 cites `lem-coef-dualizing-construction`, `lem-fix-compact-support-coefficient-change`, `lem-coef-finite-dualizing`, and `def-coef-normalized-dvr-tower`. I added the construction citation during self-review because coefficient comparison's finite-Tor hypothesis must be verified explicitly, rather than inferred from a lemma's proof. Its statement says every ordinary-etale omega is bounded constructible finite-Tor at every positive quotient level. The finite-dualizing isomorphism identifies the intermediate reduced omega with omega_m. The calculation is first made on those ordinary-etale realizations and then transported using the finite-dualizing statement; it does not assume an adjunction on arbitrary pro-etale objects. The coefficient-change statement explicitly asserts successive-reduction compatibility, and the finite-dualizing statement explicitly asserts the cocycle and identity. The proof writes out the naturality substitution between them to get the cocycle for b, and then applies the explicit scalar-adjunction transpose rule to get the cocycle for d. Scalar adjunctions and their composed coefficient identifications are exactly those defined in the normalized-tower node. The coefficient coherence citation is declared as a generic tool use. The target v compositions are the elementary compositions of the quotient ring maps already identified in step 4.

I checked the edge cases m=n (unit tensor and identity comparisons), r=m or m=n in the three-level cocycle, n=1 (the residue coefficient field), X empty (the counit has zero source), and X=s with the identity compactification (the square reduces to the quotient map itself). For the nonflat reduction A_2 -> A_1 I checked that no step tensors a general object underived: the sole underived computation is on the regular rank-one A_2 module, which is flat over A_2. No n=0 is admitted. Empty X requires neither a dimension bound nor a stratification argument.

Against B--E: there are no new statement-only leaves, no uncited auxiliary mathematical fact, no restatement of the item as a new dependency, no new source tag duplicate, and no modification of the statement. Every step citation has an exact excerpt in citations.json, checked against the cited node's statement. The successive-quotient computation uses the cocycle from the statement, not its proof. I checked the reachable dependencies for a path back to this item before delivery. Every proof step is shorter than 2000 characters; the longest is the explicit successive-quotient calculation, with no independent comparison lemma hidden in it. The server-side review_split check passed before this report was written; the full delivery dry run follows.

## Unfinished work

None in the mathematical split. Final validation and direct push are recorded below after the delivery tool exits.

## Validation

The full `deliver.py Q67 lem-coef-finite-counit-restriction-square --no-push` invocation exited successfully and printed `OK (not pushed)` at `0c1fa5ec4c1`, with the server preflight passed. The local citation-substring check also passed. A local dependency traversal found no return path to this item among the available records; that broad traversal encounters 13 pre-existing absent or stale identifiers elsewhere in the shared read clone, so the authoritative graph validation is the successful server preflight, rather than a claim that the entire local clone is complete. None of this delivery's direct dependencies is missing. The final dry run is repeated after this report addition, then its successful exit is followed by the direct delivery invocation.
