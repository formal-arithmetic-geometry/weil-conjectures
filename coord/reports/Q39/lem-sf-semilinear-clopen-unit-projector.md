# Stage-1 report: lem-sf-semilinear-clopen-unit-projector

## Files written

- `dag/nodes/sec-six-functors/lem-sf-semilinear-clopen-unit-projector.json`: statement, status split; six proof steps, no Mathlib match for the whole assertion.
- `citations.json`: one checked verbatim statement quotation for each of the 15 step/node citations.
- `report.md`: this report.
- `searches.jsonl`: the six actual searches logged by the prescribed msearch.py command.

New nodes: 0. New Mathlib leaves: 0. No Lean files, unit records, repository files or launcher files were edited. No compiler, Lake or build was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, semilinear, clopen, projector, and the varying-ring names. The fixed-coefficient declarations in `SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Proper.lean` and `Derived/ClopenIdempotent.lean` do not assert the arbitrary strict semilinear-system theorem. The read-only `lean/Sheaf/` varying-ring files supply ordinary partial constructions, but are not an eligible whole-item project attachment under this brief, and I do not use their proof bodies as DAG statements.

## WANTED

None. The ringed-site extension-by-zero and exact-functor sources used are present locally. The extension of the clopen argument to arbitrary coefficient sequences is an agent-written argument, explicitly marked as such.

## Corrections and findings

The item statement is unchanged. Its imported proof was empty. Its source correctly singles out Stacks 03DI but that tag only constructs the general ordinary extension by zero: it does not itself state this system/derived/unit theorem. I therefore supplied the clopen section argument and marked proof_origin.by as agent. I did not treat the definition of the proper/open arrows as a theorem proving its own clopen assertion: step 3 takes only its normalization of the arrow, and proves the equality by computing its transpose.

I kept the original blueprint ancestry and filled same_as after whole-blueprint searches for clopen, 03DI, and extension by zero. The nearest ancestor is fix-prop-coherence. Its main-20261015 proof sentence about adjunction units/counits is read directly; this split makes precise its clopen normalization input via the system-realization and semilinear mate-pasting nodes. The current unit record places the same compatibility clause under sk-thm-sf-compatibility. This item is not that unit's key statement, so its realized record is not edited.

I read the real Mathlib search hits, including `SheafOfModules.pushforwardPushforwardAdj` and its unit/counit formulas at Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:274,298,303. These concern ordinary continuous-site pushforwards and require a site adjunction with ring-map compatibilities; they do not give the present varying-ring unbounded assertion by one-line specialization. Scheme.Modules.restrictAdjunction and the condensed/topological sheaf hits likewise concern other categories. The second LeanFinder phrasing and second grep query also found no whole-item match. All six new search records preserve the tool and exact query of searches.jsonl; original records were retained.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches found fixed-coefficient clopen lemmas (notably lem-weil-pbc-clopen-section-direct-image) and the ordinary varying-ring complementary-zero clause; neither states the full current item. I reused the existing general exact-functor and natural-isomorphism localization nodes instead of making new ones. The item remains strictly smaller than its parent proper/open pasting theorem and does not cite that parent.

## Review by Q39

I read Stacks sites-modules.tex, Tag 03DI, label lemma-extension-by-zero, including the direct-sum presheaf, sheafification, and its adjunction proof; I also read Tag 03DJ, label lemma-extension-by-zero-exact. I read derived.tex Tag 015F, label lemma-right-derived-exact-functor, in particular its unbounded clause and the assertion that every complex computes RF. I read the blueprint proof of fix-prop-coherence and the chapter/unit records. There are no new-node sources to check.

For step 1, I read the full statements of def-weil-pbc-proetale-site, def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category, and lem-coef-semilinear-derived-sections. The first says which families cover, the second explicitly states the sheaf equalizer, the third states linearity of sheaf maps, and the fourth says transitions are compatible componentwise semilinear maps. The two-open cover works without quasi-compactness of U or X: each affine test open is quasi-compact. The empty-site sheaf axiom gives M(empty)=0; the disjoint-cover equalizer is exactly the asserted product. Its compatibility with transitions is checked as equality of restrictions, rather than inferred from derived evaluation. This is a direct elementary use of the definitions.

For step 2, I read def-sp-varying-ring-operations in full. It supplies the actual section formula for E, the specified ordinary adjunctions, and exactness of J and P. The map from a Hom(F,PM) element to Hom(EF,M) is written explicitly as x maps to (a(x),0), with the inverse given by restriction to U. Their two composites are checked on the disjoint cover. This establishes the left-adjunction comparison; it is not a reference to an uncited clopen equivalence. Uniqueness is justified by transposing the two composites to the common unit.

For step 3, I reread that operation statement and def-sp-varying-ring-proper-open-arrows. The latter specifically defines the arrow as the inverse open-unit mate; that sentence is what the citation quotes. I verified the direction: kappa is J to E, its right transpose is P kappa, and P kappa composed with u is identity, hence P kappa equals u inverse. The right unit q has formula (x,y) maps to x. Thus pi has the selected identity/zero formula, t pi equals eta, and its pullback is u on U and zero on the complement. There is no inversion of a general noninvertible mate and no reliance on the definition's claimed clopen invertibility as a black-box proof.

For step 4, I opened all five cited nodes. Exactness of E follows from its just-proved isomorphism with the already exact J; it is not deduced from sectionwise surjectivity. lem-coef-semilinear-derived-sections supplies abelian system categories and the actual derived operations. lem-weil-pbc-exact-functor-derived-functor explicitly applies to arbitrary abelian categories and all unbounded complexes, giving the canonical termwise comparison to RE. lem-sfb-exact-derived-natural-iso states exactly descent of the natural isomorphism of additive exact functors. def-weil-exact-derived-adjunction says its units and counits are the localized original ones. The operation definition supplies the ordinary-induced normalization of the given derived adjunctions. I added the resolution formula for the unit to spell out why the comparison is normalized, rather than relying on an arbitrary isomorphism of right adjoints.

For step 5, the exact-derived-adjunction definition gives localization of the transpose formula, and lem-coef-semilinear-derived-sections explicitly says the constructed adjunction transposes agree with the simultaneous ordinary constructions. I checked that the localized transpose is precisely u_s inverse, so it identifies the actual t_s. The three ordinary identities are then localized as whole-system transformations. P_s pi_s equals u_s P_s, which is the identity only under the open-unit identification, exactly as the statement says. No claim that level evaluation detects equality of derived maps is made.

For step 6, lem-coef-semilinear-derived-sections actually supplies the compatible-map derived scalar extension and K-flat models. I expanded the coefficient argument: the disjoint-cover equivalence sends a pair to the direct sum of its two pushforwards, balanced bilinear maps and tensors are componentwise, and acyclicity and K-flatness are componentwise by their definitions. This proves the needed coefficient squares on the actual models; it is not an appeal to unspecified transport. Restriction of scalars literally retains the maps. Tensor preserves the specified identities and zero maps. The proof works for arbitrary ring homomorphisms without flatness, finite generation, or cartesian transitions.

I tested X empty, U empty, U=X, the zero system, a coefficient zero ring, a two-component X with a section (x,y), and a noncartesian tower with zero transitions. For U empty all maps have zero targets; for U=X the complement is zero and all the comparison maps are the normalized identities. The nonflat map Z/4 to Z/2 causes no change to the section and unit calculations and is covered by derived scalar extension, not by an unjustified exact tensor. Unbounded complexes cause no additional issue because E is exact and Tag 015F covers every complex. None of the six steps is longer than 2000 characters, and none packages a hidden comparison lemma: each comparison is calculated, while the non-elementary localization facts are cited as existing nodes.

The two generic proof tools from other units are declared in split_report.tool_uses: lem-weil-pbc-exact-functor-derived-functor and lem-sfb-exact-derived-natural-iso. They only localize the maps constructed here; they do not substitute another geometric route for the compatibility unit. Definition citations do not require a route change.

## Unfinished work

None in the one-level split. The required remote dry run and push are the remaining delivery actions; their final results are recorded below when available.
