# Q22 stage-1 delivery

## 1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-normalized-adjunction-square-transpose.json`: item, statement, now split in five explicit steps; unchanged statement and statement dependencies; no complete Mathlib match.
- `citations.json`: the verbatim unit-expression clause from the existing cited node for Steps 1 and 2.
- `report.md`: this report. `searches.jsonl` is the required search-command log.

There are **0 new nodes, 0 new Mathlib leaves**. The existing Mathlib leaf `lem-weil-pbc-adjunction-of-natural-bijection` is reused. The existing Mathlib definition leaf `def-weil-pbc-adjunction-mate` remains the statement's conventions dependency.

## 2. Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, normalized adjunction squares, and transpose terminology. Read the nearby generic `CategoryTheory/Adjunction/ExchangeMate.lean` and `AlgebraicGeometry/OriginalCounitAdjunctionTransport.lean`: the former treats four adjunctions and an exchange composite with a left-inverse hypothesis; the latter compares geometric derived adjunctions. Neither states the present eight-category result with its three given normalization identities and arbitrary augmentations. No project declaration covering every clause was found.

## 3. WANTED

None. All sources actually used are available locally. This calculation does not use the Kelly–Street reference mentioned in the inherited conventions node.

## 4. Corrections and source comparison

The item was statement-only and unsplit. Its statement is well typed and remains byte-for-byte unchanged. Its Stacks 07A6 reference is background for the derived application, not a claim that Stacks states this general square formula. I read `literature/stacks-project/sites-cohomology.tex`, Tag 07A6 (`lemma-adjoint`) and 07A7 (`remark-base-change`), and `literature/stacks-project/categories.tex`, Tag 0037 (`definition-adjoint`) and the following paragraph. The latter explicitly identifies a transpose with the unit followed by the right functor of the original map; it is the elementary categorical input actually used here. Accordingly `proof_origin.by` is `agent`, with this precise source place. The new steps derive the square formula rather than attribute it verbatim to Stacks.

Read the proper-base-change chapter and unit records and the current `main-20261015` perfect-projection-formula proof. The item serves the inherited detailed-form passage “Hence it contains every perfect complex,” through the ringed restriction and slice-normalization descendants. Its computation is exactly the global-unit/local-transpose argument needed by Step 4 of `lem-weil-pbc-ringed-slice-pullback-mate-normalization`. No chapter or unit route changes. The existing `blueprint.from` chain and exact place are preserved, and `same_as` is confirmed empty. Whole-blueprint searches for `normalized adjunction`, `transpose`, `homEquiv_unit`, and `unit formula`, and DAG/source concept searches, found no blueprint node stating the entire result. General Hom-unit material already has its existing node, so no duplicate is created.

Mathlib searches were run through the mandated `msearch.py` only, in all four modes, with a second semantic phrasing. Their exact queries and returned top hits are appended in the item and logged in `searches.jsonl`; inherited searches remain untouched. Read `Mathlib/CategoryTheory/Adjunction/Basic.lean` lines 159–182 (`homEquiv`, whose forward function is unit followed by the right functor of the map, and the `homEquiv_unit` alias), and `Mathlib/CategoryTheory/Adjunction/Mates.lean` lines 230–255 (`mateEquiv_square`). The former supplies a subfact already in the DAG; the latter is a pasting law with six adjunctions, not a one-line specialization to the present arbitrary augmentation hypotheses. Other hits for derived adjunctions and adjoint composition have additional derived/composition data. No hit states the entire item.

## 5. Unfinished work

None for this stage-1 split. No Lean was written and no compiler, Lake, local DAG checker, or local preflight was run. The required server dry run and delivery follow this review.

## Review by Q22

I reviewed the item with the three source places above and both dependency statements open. This is a self-review for direct delivery; the maintainer's independent review remains the next reader. I retained every category, functor, natural transformation, orientation, and stated hypothesis. In particular the comparison arrows need not be isomorphisms, and there is no hidden assumption that the q functors are localizations or that G_v has a left adjoint. The given adjunctions provide natural Hom bijections and their units, so they satisfy the hypotheses of the existing natural-bijection node. Its statement, not its proof, includes exactly `Psi(a) = G(a) composed with eta`, quoted verbatim in citations.json.

For Step 1 I checked that this formula applies to both T_0 and T_D. Setting I = FA and h = identity_FA in the assumed normalization gives equation (1), with source q_A(A) and target R(q_B(FA)). Functorial preservation of identity removes q_B(h). This step does not presume alpha or iota invertible. The cited existing node explicitly gives the needed unit expression.

For Step 2 I checked the same cited statement for T_v: c_A starts at L_v(r(q_A(A))) and ends at q_Bv(s_0(FA)), so its transpose is eta_v followed by R_v(c_A). Expanding a functor on the composite and applying exactly the assumed unit square at X = q_A(A) gives the displayed equality. No uncited theorem about derived mates or localizations is needed.

Step 3 is elementary: I wrote the naturality equation for beta at alpha_A in full. Its two sides run from r(R(L(q_A(A)))) to R_v(s(q_B(FA))). Substituting it in Step 2 and combining r of the first two factors are just the defining naturality and functor laws. There is no new assertion requiring a separate node.

Step 4 is elementary substitution of equation (1), followed by the assumed augmentation square at I = FA. I checked that rho's component must be rho_(GFA), not rho_A yet: the preceding factor is r(q_A(eta^0_A)), landing at r(q_A(GFA)). This makes the new composite well typed. Nothing about augmentations is imported from the proof of the parent node.

Step 5 is elementary naturality of the forward transformation of rho at eta^0_A: A to GFA. I wrote the naturality equation rather than say “transport.” Its right side is rho_A followed by q_Av(r_0(eta^0_A)); functoriality combines this with q_Av(tau_FA). The common codomain is R_v(q_Bv(s_0(FA))), as required. No inverse, cancellation, faithfulness, or resolution argument enters any step. Steps 1 and 2 cite a genuine theorem node, and Steps 3–5 are explicit few-line calculations, so neither D1/D2 relabelling nor D3 reliance on definitions in place of a missing theorem occurs. All five steps are below 2000 characters and contain no suppressed lemma.

I checked small cases as a safeguard for E1–E5. With every functor and comparison the identity, the result becomes the familiar identity transpose = unit. With identity adjunctions on an additive category, identity q/r/s/r_0/s_0, rho = zeta = identity, alpha = iota = scalar a, theta = beta = scalar b, iota_v = identity and tau = ab (central scalars), all three hypotheses hold and the conclusion is ba = ab; choosing a = 0 explicitly checks a noninvertible alpha/iota/tau. Taking empty categories where the functors exist makes the A-indexed conclusion vacuous. These checks expose no missing nonemptiness, invertibility or exactness hypothesis. The written proof works in arbitrary categories, not only these tests.

For delivery-errors B I checked self-containment, single TeX escaping, exact source labels and the verified existing Mathlib declaration; there are no new statement-only nodes to format or search. For C I read the actual statement of each cited node, quoted its unit formula, and checked every use against its hypotheses. The only new proof dependency is an existing Mathlib leaf in sk-def-exchange, explicitly recorded as a generic tool use, so it creates no cycle or route replacement. For D the five displayed calculations carry the argument themselves, with no clause repackaged as a new node. For E I checked the indexed objects and composite types above and the small cases. I found no statement dispute, source error requiring correction, or unfulfilled geometric hypothesis. The correction made was to replace the missing proof by these explicit steps and add the actual adjunction-unit dependency and the precise agent-proof source.

## Not duplicates

No new nodes. The existing general unit-expression node is cited rather than recreated; it does not itself state the normalized square conclusion.

The first delivery-tool attempt rejected the quotation length (the correct unit formula alone was under 40 characters). I expanded both entries to the complete concluding clause of the existing statement, retaining the same proof and cited fact.
