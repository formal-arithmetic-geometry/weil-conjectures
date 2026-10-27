# Stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-open-internal-kflat-mate-normalization.json`: item, statement unchanged, six proof steps, status split. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for all 17 step-node citations.
- `searches.jsonl`: five actual searches logged by msearch; inherited item searches retained as well.

## Attachments

None. Searched the project source for the exact blueprint tag and for scalar mates, internal modules and K-flat comparison terminology. The nearby `AlgebraicGeometry.ProEtale.mateEquiv_leftDerivedUpperStarExtendScalarsIso_inv` in `SixFunctors/ProEtale/FiniteCoefficient/Derived/ExtendScalars/RestrictScalarsMate.lean` concerns fixed ring coefficients with a noetherian hypothesis; it does not state this item for arbitrary condensed coefficient rings and reconstructed internal modules.

## WANTED

None. The blueprint and the relevant Stacks source are available locally.

## Corrections and scope

The item was statement-only. Its statement, statement dependencies, ancestor, and ancestor place are unchanged. The split supplies the missing four-corner comparison calculation and the final actual-unit transpose; it does not defer a clause to a new node. The sectionwise K-flat theorem already supplies the comparison on the entire unbounded category. The transfer uses the existing general equivalence-square lemma, with all four functors and all comparison directions specified, and verifies its square rather than treating equivalences as identities.

The chapter and scalar-six unit were read. This realizes the balanced pullback paragraph (1) and the normalization needed by the alternative open-adjunction paragraph (2) of `det-prop-scalar-six-pullback`. It changes neither the unit route nor its statement. The imported reference 06YV is not treated as an exact tag for every auxiliary result: the already existing K-flat normalization node carries the more precise supporting tags. No SGA source is used.

## Mathlib verdict

The five logged searches include two semantic phrasings. Their hits concern ordinary modules/presheaves, ordinary sheaf pullback compositors, and abstract mates. Read `Mathlib/CategoryTheory/Adjunction/Mates.lean`, lines 123–155: `unit_mateEquiv` and `unit_mateEquiv_symm` supply the general transpose identity, not the identification of the actual transported internal/section K-flat comparison. Hence the item is not a Mathlib leaf. No claim of absence rests on a failed service.

## Not duplicates

No new nodes. Blueprint searches for `balanced K-flat` and `internal scalar` returned no imported nodes; broader scalar/mate searches and the DAG search found the existing scalar normalization and equivalence transport interfaces that this split reuses. The parent open-scalar-conjugate normalization depends on this item and is not cited back.

## Review by NS

I read the item's current statement and its source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md`, particularly (1) and the alternative in (2). I also read Stacks `sites-modules.tex`, section-tensor-product (03EK), lemma-sheafification-tensor (0GMW) and lemma-tensor-product-pullback (03EL). Those describe the balanced sheaf tensor and its inverse-image comparison. The source does not itself expand the internal-module adjunction normalization; that expansion is explicitly agent-written here. There are no new nodes whose sources need review.

In step 1, the module-pullback node states the tensor formula used. The alpha-isomorphism node applies to every condensed ring, so it covers A and B without an admissibility restriction. The geometric inverse-image exactness node covers transported modules, not merely abelian sheaves. The operations-transport node gives the exact underlying-sheaf-preserving equivalence and the pullback comparison, and the exact-functor-derived-factorization node gives the termwise unbounded derived realization. I checked the inverse to the balanced collapse: balancing really gives x tensor m = 1 tensor alpha-inverse(x)m. Thus exactness requires no flatness of a.

In step 2, the internal-section scalar-adjunction node explicitly identifies the derived adjunctions including their units and counits, and the localized extension comparison on flat-term K-flat complexes. The operations-transport node supplies the specified pullback comparisons. Part (1) of the general equivalence-square node gives uniqueness of the left comparison normalized by the right comparison; its hypothesis is satisfied by these full adjunction identifications. We therefore cannot accidentally choose a twisted scalar adjunction.

In step 3, restriction really is identity on underlying sheaves by the change-of-scalars node. The coefficient-change node states alpha_B composed with j-inverse(a_X) = a_U composed with alpha_A; rearranging gives precisely the action equality used. The scalar equivalence and pullback comparison nodes preserve the underlying maps used to check the displayed square. The check is first an equality of linear sheaf maps, then of chain maps, and finally of their localizations; it does not infer equality of derived morphisms merely from their effect on sections or cohomology. This step is elementary relative to those specified comparison interfaces.

In step 4, the K-flat scalar-comparison-normalization statement explicitly says its inverse comparison is the mate of the action identification and is invertible on the entire unbounded derived category. I verified its direction: the source is T_U R_A and target R_B T_X. Its topos-site assumptions use the item's small pro-etale-site conventions, and its pulled-back ring convention is identified via the specified alpha maps. The ring map is arbitrary. No preservation of K-flatness by scalar restriction is assumed.

In step 5, part (3) of the equivalence-square node has exactly the square and conclusion displayed here. The assignments J=T_X, J'=T_U, U=r_X, U'=r_U, P=R_A, Q=R_B give the correct types at all four corners. Its normalized left comparisons are c_X,c_U from step 2 and its square hypothesis was checked in step 3. The displayed conclusion solves for precisely the transformation defined by transport in the item, so faithfulness identifies actual transformations and invertibility follows. This is a generic tool use from another unit, declared in split_report, not a replacement of the scalar-six proof route.

In step 6, the inverse formula in the adjunction-mate definition gives theta = counit composed with T_U(d) composed with T_U R_A(unit). Naturality of the specified unit then moves the composite k across that unit, and the right-adjoint triangle identity cancels the remaining unit and counit. I checked that k has source R_A V and target r_U R_B T_X V. The result is exactly the requested transpose using eta_U and eta_X from the statement. This is a written triangle-identity calculation, not a new theorem left as a clause-node.

I checked delivery-errors B–E: no new statement-only or duplicate nodes, no invented source tags, no unlogged searches, all cited statements opened, no use of a cited proof in place of a statement, no use of the parent which depends on this item, and no extra boundedness/flatness assumption. Small cases: j the identity makes the balanced collapse and right square identities; a the identity leaves the ordinary pullback comparison; the empty open and the zero complex give zero maps; a nonflat map such as Z to F_p still uses the unbounded K-flat theorem without exactness of scalar extension. No statement dispute arose. Every step is shorter than 2000 characters.

## Unfinished

None at stage 1; all existing dependencies remain existing nodes. No Lean was written and no compilation or build was invoked. Server dry-run and direct delivery follow this report.
