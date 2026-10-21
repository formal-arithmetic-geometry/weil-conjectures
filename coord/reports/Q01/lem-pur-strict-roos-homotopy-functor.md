# Stage-1 report: lem-pur-strict-roos-homotopy-functor

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-strict-roos-homotopy-functor.json`: existing statement, now split into eight explicit elementary steps; no full Mathlib match.
- `citations.json`: fourteen verbatim statement quotations, one per step/node citation.
- `searches.jsonl`: the six additional searches run through the prescribed msearch.py command.
- `report.md`: this report.

No new nodes and no Mathlib leaves were created. No repository, launcher, Lean file or unit record was written. No compiler, Lake or build tool was run.

## Attachments

None. Searched the blueprint tag and the Roos/homotopy notions under `lean/WeilConjectures/`. Read `WeilConjectures/Algebra/Homology/RoosComparisonHomotopyRetract.lean` and the relevant homotopy constructors in `RoosComparisonHomotopies.lean`. The former theorem concerns homotopy retractions with specified comparison presentations. It does not state the present functor, its action on arbitrary compatible homotopies, and its scalar linearity. In particular it cannot be attached for every clause of this item. `Sheaf/CategoryTheory/StrictRoosModel.lean` provides the existing strict model, not an attachment meeting the brief's project-root and all-clauses requirements.

## WANTED

None. The relevant Stacks source and the current blueprint are present.

## Problems corrected

The statement is true as written and has been retained verbatim. The node had no proof. The delivery supplies the product naturality equations, the signed homotopy calculation, the quotient construction, and the scalar check. The proof does not infer functoriality from arbitrary choices of triangulated cones or derived limits.

The source tags 014E and 08TC define the cone and the derived-limit shape; they do not assert this full strict homotopy calculation. Accordingly `proof_origin.by` is `agent`. Added exact source labels for the quotient and linear-category conventions, and marked each step elementary only after writing its calculation. None of the steps exceeds 2000 characters or invokes an omitted auxiliary lemma.

## Unfinished work

None for this one-level stage-1 split. Formalization is outside this brief.

## Searches and reuse

Retained the existing item's five Mathlib search entries, which came from the preceding creation of the item, and read their candidates. The current sandbox initially contained no split, report or search log to resume. The six searches of this attempt are logged by msearch.py and appended to the item's search record with their exact query texts and observed top results. Both semantic phrasings were tried, together with Loogle, LeanSearch and two source greps. All six services returned successfully.

Read the candidate sources: `mappingCone.mapOfHomotopy` in Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:103 constructs a cone map from a square commuting up to homotopy; it is not a statement that the two diagonal maps induced by a compatible tower homotopy are homotopic. `mappingCone.descHomotopy` and `mappingCone.liftHomotopy` in Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean:421 and :535 require specified cochains and differential identities. They provide useful implementation constructors, but the product, transition, sign and quotient calculations in this item still have to be supplied. `CategoryTheory.Functor.mapHomotopyCategory` in Mathlib/Algebra/Homology/HomotopyCategory.lean:232 applies a functor of the underlying categories termwise; the shifted Roos cone is a functor on complexes that mixes adjacent degrees. It is not that one-line specialization. The grep scoped to the single MappingCone.lean file prints malformed path columns (the launcher parses single-file rg output as if it had filename prefixes); the actual read source and correct line numbers are given above, and the search results are recorded as returned.

Searched the full imported blueprint using `tools/blueprint_refs.py search` for `Roos`, `homotopy`, `compatible homotop`, `Roos cone`, and `homotopy functor`, and read the relevant DAG statements. There is no blueprint equivalent of this full item. The existing homotopy-retraction statement is narrower in its maps and has no linearity/functor clauses; the general cone-descent statement has additional shift, triangle and lower-bound hypotheses. Neither is used as a substitute. No new node was needed, so there are no new/existing pairs requiring a Not duplicates entry.

The item's nearest blueprint ancestor was checked with `tools/blueprint_refs.py ancestor`: it is `def-weil-rationalization-karoubi`, with the existing via chain through integral scalar extension. Read its current main-20261015 text in sec-proetale-coefficients/sk-def-sf-operations: the final paragraph defines completed extension on integral representatives levelwise before rationalization. The split supplies only its required strict-model homotopy functoriality; it does not change the chapter or unit route. The sandbox retains the item's existing non-unspecified `blueprint.from.place` and records `same_as: []`.

## Review by Q01

I read delivery-errors B–E in full and checked this split against the statement of every cited node, not its proof. I read the chapter and unit records, the current blueprint scalar-extension paragraph, Stacks derived.tex definition-cone (014E), definition-derived-limit (08TC), definition-complexes-notation (013H), the cochain homotopy definition and compose-homotopy-cochain (0112) in homology.tex, and definition-linear-category (09MJ) in dga.tex. These fix the conventions. The strict-model definition node supplies the actual signed coordinates; I did not assume Stacks defines a functorial arbitrary derived-limit choice.

Step 1 uses def-weil-strict-roos-model for the termwise products and def-sp-abelian for preadditivity and biproducts. Its additivity/composition assertions are proved by projecting the universal-property maps. This needs existence of countable products only. Step 2 uses def-weil-inverse-system for the adjacent-transition naturality equation, def-weil-abstract-derived-category for cochain maps, and def-weil-strict-roos-model for the differential. I checked both the product shift equation and both components of the chain-map equation explicitly. Step 3 applies only the product identities already proved to the model's two diagonal blocks; no external additive-functor theorem is being smuggled in.

Step 4 uses the strict model and inverse-system definition for the product projections and transitions. The product homotopy identity and the equation v_Y H = H v_X follow after every projection from precisely the two hypotheses on h in the item. There is no exact-products, boundedness, injectivity, Mittag–Leffler, or derived-category hypothesis. Step 5 uses only the strict model's signed differential. I checked the degree of H^i is P_X^i to P_Y^(i-1), that T^i maps the cone's degree i into degree i-1, and that the mixed block has sign H^i v_X^i minus v_Y^(i-1) H^i. It cancels by Step 4; the diagonal blocks are the two required map differences.

Step 6 uses the inverse-system definition to identify natural transformations in towers, and the cochain definition from def-weil-abstract-derived-category. It defines the homotopy quotient explicitly instead of taking its well-definedness from a definition-only citation. It writes the witnesses 0, -h, h+h' and bha, and the differential equation for composition. Adjacent compatibility implies compatibility for composite transitions, so the homotopy relation is exactly the one for complexes in the tower category. Step 7 then defines the map on classes and derives its functor and additive laws from Steps 3–6. Its strict-model citation specifies the object/map construction, not a missing descent theorem.

Step 8 uses def-weil-linear-category for bilinearity and the strict model for the product and biproduct projections. I checked that projection after a scalar multiple is the scalar multiple of the projection, so product maps and diagonal maps are linear. Scalar multiples of a compatible homotopy remain compatible and satisfy the scalar-multiplied homotopy equation; this also makes the scalar action on the quotient legitimate.

For the B checklist there are no new nodes, unsourced notions or new Mathlib leaves. The five definition statements used above introduce all of the constructions needed, and the proof explicitly defines the homotopy quotient. For C each of the fourteen citations has a verbatim quote in citations.json; no step uses a cited node's proof, or a theorem that its statement fails to provide. The dependency union is exactly proof_deps, and only pre-existing definition nodes are cited, so this introduces no off-unit theorem route or new dependency path. For D the proof contains actual projection and matrix equations, not new nodes relabelling the conclusions. For E I checked all degrees, signs and hypotheses rather than relying on an unspecified transport.

Small cases checked: the zero tower and zero maps; f = g with h = 0; towers with zero transitions, where v = 1 and the mixed terms cancel; constant towers with identity transitions, where shift compatibility still gives exactly the required commutator equation; complexes concentrated in one degree, where any possible h has the prescribed degree; and scalar 0, scalar 1, and characteristic 2, where the two opposite mixed terms still sum to zero. The computation works without boundedness. In particular changing the first component of T from -H to +H would fail in general, confirming that the sign is substantive. No statement dispute or route departure was found.
