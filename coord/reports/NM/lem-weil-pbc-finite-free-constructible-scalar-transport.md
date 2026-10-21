# Stage-1 report: lem-weil-pbc-finite-free-constructible-scalar-transport

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-free-constructible-scalar-transport.json`: item, statement, now split into seven proof steps. Mathlib verdict: no exact match after two phrasings with LeanFinder, LeanSearch, Loogle and logged source grep.
- `citations.json`: eleven step/dependency records with verbatim statement quotes.
- No new nodes, no Mathlib leaves, no unit changes, no Lean files.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and finite-free/constructible/scalar-transport notions. The finite-coefficient results in `SixFunctors/ProEtale/FiniteCoefficient/Derived/Perfect.lean` concern a different coefficient category and do not establish the completed integral statement. The item has Lean audit state `none`.

## WANTED

None. Read the available Bhatt--Scholze PDF and Stacks source. No SGA source is used.

## Corrections and scope

The original item has no proof. Its statement is retained verbatim. Added explicit statement dependencies for perfect algebra complexes, finite generation, projectivity, and the local-model realization convention. Preserved all source, creation, chapter/unit and Lean audit fields. Inherited Mathlib search records are retained as historical records; eight actual searches from this run are appended with their logged queries and outcomes. Loogle's unknown-identifier response is reported, not interpreted as a mathematical absence theorem. LeanSearch was available in this run. Its second query returns ordinary scalar-extension infrastructure, not the item.

The proof does not confuse the constant coefficient sheaf with its completed coefficient sheaf: the algebra complex is first made constant and then extended to the completed ring. The conclusion uses the existing characterization that explicitly includes the uniform tower and compatible witnesses. It does not infer that characterization from Stacks 09C1 alone.

Amplitude here is the bounded representative's chosen degree interval: if P is zero outside [a,b], so is B tensor_A P. The proof also gives finite-projective terms there. No change in a or b, or additional refinement of the specified strata/covers, is made.

## Not duplicates

No new nodes. Whole-DAG statement searches and `tools/blueprint_refs.py search` for finite-free constructibility, stratified perfectness, and scalar extension led to reuse of the existing characterization, strict-perfect pullback and normalized scalar-comparison nodes. The blueprint scalar-extension proposition is the ancestor, not a separate attachment or an assertion used to prove its own input. The more general condensed bounded-constructible scalar lemma has a different category and is not used.

## Review by NM

I read the chapter and unit records, the current main-20261015 scalar-extension statement, the retained parent proof's membership step, and the full statements of every dependency cited in the seven proof steps. The chapter/unit route is kept: this supplies the integral membership input to the ancestor's finite scalar-extension package. The proof is marked agent-written because it assembles those inputs and writes out the elementary formulas, rather than claiming the whole adapted tower-category assertion is printed in a single source.

For the item, I read Bhatt--Scholze Proposition 6.6.11 (including its reverse proof using completeness and étale origin) and Proposition 6.8.11(3), Stacks sites-cohomology.tex `lemma-strictly-perfect-pullback` (Tag 08H3), `lemma-derived-pullback-composition` (Tag 0D6D) and `lemma-pullback-tensor-product` (Tag 07A4), and sites-modules.tex `lemma-tensor-product-pullback` (Tag 03EL). No new-node sources are needed. The adapted category equivalence is specifically taken from the statement of `lem-weil-pbc-integral-stratified-perfect-characterization`, whose condition (i) retains the tower and witness requirements, and not silently substituted for the paper's definition.

Step 1 uses exactly implication (i) => (ii) of the existing characterization. Its hypotheses are finite extension of Q_ell, noetherian finite-dimensional T, and ell invertible on T, all in the item. A given system of local models can be retained instead of reselected for the precise clause. The theorem is applied on T itself, not on possibly nonnoetherian pro-etale covering members.

Step 2 uses the actual finite-generator definition to obtain the finite free surjection and the projective definition's lifting clause to split it. Tensoring the splitting identity with B gives the displayed splitting over B. Images of the finite standard basis generate the retract, and the same project's definition supplies its projectivity. This is an elementary argument from the two cited statements, not an unrecorded flatness theorem. It makes no claim that all projective modules have finite rank.

Step 3 uses the coefficient-package definition's explicit constant-sheaf package, then applies the general strict-perfect ringed-pullback statement to the identity topos with a changed ring. Its statement provides K-flatness and the comparison with the termwise complex, not merely preservation of perfectness. The same application over B is legitimate because step 2 has already constructed the finite-projective B-terms. This avoids assuming global projectivity of finite locally free sheaf objects.

Step 4 uses the completed restriction statement separately for A and B, including its stratum and slice cases and exact module restriction. Equality after all finite quotient projections proves compatibility of the structural ring maps. The normalized scalar-comparison theorem assumes identified inverse-image coefficients and supplies the scalar-square isomorphism on the whole unbounded derived category; those coefficient hypotheses are supplied here, not by an unjustified claim that inverse image preserves arbitrary limits. For slices the ringed-site restriction definition gives exact restriction. I declare the off-unit normalized scalar theorem as a generic tool use in split_report.tool_uses: the unit has no theorem specifying this scalar square. It does not replace a unit proof step with another route.

Step 5 again uses the strict-perfect theorem's exact derived-model clause for F, with identity underlying topos and R -> S. This supplies the image of the given local isomorphism, composed with the canonical representative comparison. A theorem saying only that pullback preserves perfectness would not suffice; the cited statement includes the comparison and its naturality.

Step 6 is elementary balancing, with both maps written explicitly. I checked the A-, R-, and B-balancing relations, the two composites, and compatibility with restrictions and the differential. The sheaf-tensor definition is cited for passing these balanced presheaf maps to sheaf tensor products. This is why no new node restating the item's local-model conclusion is introduced.

Step 7 uses exactly implication (ii) => (i) of the characterization, now with B and its own uniformizer v. It gives all three required clauses, including compatible étale-origin witnesses; merely showing that the local complexes are bounded would not do so. T, rather than its covering members, again satisfies the noetherian and finite-dimensional hypotheses. No hypothesis comparing t and v powers is needed for this local-model argument.

I checked delivery-errors B--E: no unsplit new node or source-less notion is introduced; TeX is retained with a single backslash in decoded strings; every non-elementary assertion is one of the cited statements; the quoted citations are copied verbatim. I also checked that none of the cited nodes has a dependency path back to this item, that proof_deps is exactly the union of uses, and that no step exceeds 2000 characters. Nothing is moved into a newly named clause of the item.

Small cases: for P=0 or T empty all complexes and maps are zero and the assertion is valid. A rank-zero term uses the zero splitting; different degrees need not have equal ranks. For E'=E, the maps reduce to ordinary tensor unit identifications. For a ramified extension, no reduction A/t^n = B/v^n is asserted: the argument uses the canonical completed map and the actual B-complex. For nontrivial differentials the maps in step 6 commute with 1 tensor d, so the comparison is a chain isomorphism, not only a degreewise module isomorphism. Finite coefficient results found in Lean were rejected because they do not address this integral category.

## Unfinished work

None in this stage-1 item. The cited unsplit inputs remain their own DAG items, as required by the one-level split rule.
