# Stage-1 repair: lem-sfb-adic-localizing-exceptional-cohomology

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-localizing-exceptional-cohomology.json`: existing item; the statement is byte-for-byte unchanged. Its proof is now a 2221-character assembly in six steps (longest step: 518 characters), replacing the returned 5702-character proof.
- `dag/nodes/sec-six-functors-basics/lem-sfb-adic-constructibility-predicate-comparison.json`: new statement, not a Mathlib match. It extracts the coefficient-specific comparison from old step 2, for arbitrary Noetherian schemes and modules, independently of proper morphisms or exceptional adjoints. Complete proof in words below.
- `dag/nodes/sec-six-functors-basics/lem-sfb-adjunction-transport-left-iso.json`: new Mathlib leaf; `CategoryTheory.Adjunction.ofNatIsoLeft`, `Mathlib/CategoryTheory/Adjunction/Basic.lean:497`, together with its Hom formula at line 509.
- `citations.json`: verbatim statement witnesses for every citation of the item's six proof steps.
- `searches.jsonl`: actual msearch records; no unavailable or invented searches were used as evidence of absence.

The sandbox initially contained only dispatcher marker files, with no node, report, citations or search log to resume. I therefore copied the current repository's returned item, retaining its accepted statement, proof route, earlier searches and review metadata, and refined that version. No repository or launcher file was written; no git command, Lean compiler or build tool was run by the worker.

## Attachments

None. The live theorem `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible` in `lean/Sheaf/AlgebraicGeometry/EllAdicLocalizingExceptionalConstructibleCohomology.lean:64` ends in `sorry`. Searches in `lean/WeilConjectures/` by blueprint tag, declaration name and exceptional-constructibility terminology found no finished declaration stating the item.

## WANTED

None.

## What was wrong and what changed

The returned split contained the right established restriction route, but bundled coefficient-predicate identification and adjunction transport into a long proof. The mathematical statement is unchanged, including positive characteristic, specified multiplication, the finite-subextension-valued algebraic closure, the supplied adjunction, every cohomological degree, ordinary ambient coproducts and the absence of a completeness condition.

Old step 2 is now a separate comparison obligation with its own hypotheses and short argument. Old step 4's categorical transport is an exact Mathlib leaf. Old steps 1, 3, 5 and 6 retain the existing nodes for Noetherianity, finite Tor amplitude, rational/integral restriction and uniqueness; the remaining elementary checks are written explicitly. In particular, the last step composes actual presentation isomorphisms, rather than using an unexplained assertion that constructibility transports.

The stage-1 delivery contract requires a new non-Mathlib node to be statement-only (`status: unsplit`), so its complete requested proof in words is supplied in the next section, rather than placing proof steps into a new unsplit JSON node. The proof is already below the human's 3000-character limit. The Mathlib node has no postponed mathematical argument.

`tools/blueprint_refs.py ancestor lem-sfb-adic-localizing-exceptional-cohomology` reports `None`: the existing item's maintainer-owned `created.item` is a Lean module name, so the creation chain ends there. The new nodes faithfully record this computed null ancestor and `via: [lem-sfb-adic-localizing-exceptional-cohomology]`; their `from.place` names the actual blueprint proof and the exact returned step. The existing item's valid explicit blueprint reference is retained. I did not alter creation metadata or pretend that the broken creation chain reached an imported node.

## Proof in words for lem-sfb-adic-constructibility-predicate-comparison

1. Apply [def-weil-pbc-internal-abelian-sheaf-module-equivalence]. Its forward equivalence keeps underlying abelian sheaves, section groups and restriction maps identical. The regular module, its finite powers and the section actions of maps between them are therefore identical. A local cokernel presentation in one description is the same local cokernel presentation in the other.
2. For $E$, take a finite stratification witnessing general constructibility. Each stratum has Noetherian underlying space. Apply [lem-weil-pbc-condensed-lfp-local-triviality] on that stratum: its local finite presentations become finite free local models, with scalar module $E^r$. For the finite-subextension-valued algebraic closure use [lem-weil-pbc-condensed-qbar-lfp-local-triviality] instead, giving scalar module $\overline{\mathbf Q}_\ell^r$. Conversely, on every stratum [det-def-sfb-constructible-local-model] turns a finite constant scalar model into a local finite presentation. This proves both implications for the field cases.
3. For $\mathcal O_E$, [lem-sfb-integral-lfp-constant-model-comparison](i)–(ii) states precisely the two implications, including refinement of the stratification and torsion scalar modules. Apply it to the section-action description from step 1. The hypothesis is exactly that $X$ is Noetherian.
4. Apply the module equivalence degree by degree to the definitions [sk-def-sfb-bounded-constructible; sk-def-sfb-constructible]. Boundedness is the identical condition on the same cohomology modules, so the two bounded constructible object properties coincide. No completion is taken.

The topological hypothesis in proof step 2 is the ordinary consequence already used in item step 1: [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal] gives stabilization of descending closed chains; subspaces of a Noetherian space are Noetherian. This is a cited general tool, not an extra hypothesis on the field coefficients. This short proof is an agent assembly of the existing comparison statements; the blueprint restriction bullets motivate the interface but are not claimed to prove the lfp bridge themselves.

## Proof in words for lem-sfb-adjunction-transport-left-iso

This is a Mathlib leaf. At Basic.lean:497–504, `ofNatIsoLeft a e` constructs the required adjunction with unit `a.unit` followed by whiskering of `e.hom`, and counit given by whiskering `e.inv` followed by `a.counit`. At lines 509–512, `homEquiv_ofNatIsoLeft_apply` identifies its Hom equivalence with $f\mapsto a(f\circ e_M)$. The statement requires neither an equivalence of the categories nor any smallness hypothesis beyond their category universes.

## Not duplicates

lem-sfb-adic-constructibility-predicate-comparison vs lem-sfb-integral-lfp-constant-model-comparison: the existing comparison concerns only integral sectionwise module sheaves; the new statement handles all three specified ring-object coefficient families and identifies the two bounded derived object properties. Its integral argument cites the existing theorem, without restating its proof.

lem-sfb-adic-constructibility-predicate-comparison vs lem-weil-pbc-condensed-lfp-local-triviality: the existing statement converts a globally lfp $E$-module into locally finite free modules; it does not compare the two stratified predicates for all adic coefficient families or their bounded derived subcategories.

lem-sfb-adic-constructibility-predicate-comparison vs lem-weil-pbc-condensed-qbar-lfp-local-triviality: the existing statement is the algebraic-closure local-triviality implication only, not the integral/field comparison and derived-category equality.

lem-sfb-adic-constructibility-predicate-comparison vs det-def-sfb-constructible-local-model: this existing lemma says constant scalar presentations imply general local presentations for any coefficient ring; it explicitly warns that the converse fails in general. The new coefficient-specific statement establishes the converse only under the stated Noetherian and certified adic hypotheses, citing the relevant coefficient comparisons.

lem-sfb-adic-constructibility-predicate-comparison vs det-def-localizing-closure-ctf-equals-bc: the existing theorem compares finite Tor amplitude with bounded constructibility in the finite-model convention; it does not identify general ring-object constructibility with that convention.

lem-sfb-adjunction-transport-left-iso vs det-sp-unique-right-adjoint: uniqueness compares two already supplied adjunctions with one fixed left functor; the new leaf constructs an adjunction for a second, isomorphic left functor.

lem-sfb-adjunction-transport-left-iso vs lem-weil-pbc-adjunction-of-natural-bijection: the latter starts from natural Hom bijections and constructs an adjunction; the new leaf starts from an existing adjunction and an isomorphism of its left functor, and includes the resulting Hom formula.

lem-sfb-adjunction-transport-left-iso vs def-sfb-dc-upper-lower-adjunction: this blueprint node restricts an ambient geometric adjunction to fully faithful constructible subcategories; it does not state transport along arbitrary isomorphic left functors.

The whole DAG and blueprint were searched for finite constant local models, local finite presentations, adjunction transport, the expected Mathlib declaration, and potential generalizations. The current project Lean sources were searched as well. No existing node states either new obligation or a one-line generalization covering it. Searches found no same-statement blueprint node, so both `same_as` lists are empty. No new source carries a Stacks tag shared with another new node.

## Review by Q39

I read the chapter and the unit `sk-cor-existence-ii`, the item's six returned steps, the current restriction statement and proof in `main-20261015/.../sk-thm-existence/det-existence-restriction(.proof).md`, and the proper comparison proof in `sk-cor-existence-ii-restriction.proof.md`. The unit's reduction through compact-support adjoints and the integral/rational restriction theorems is preserved. I also read Stacks Tags 01T6 (`morphisms.tex`, `lemma-finite-type-noetherian`) and 01OZ (`properties.tex`, `lemma-Noetherian-topology`). For the comparison helper I checked the live `ConstructibleSheaf/ProEtaleModule/Def.lean` definitions at lines 69 and 87, the section-action equivalence statement, the two field local-triviality statements, the integral equivalence, and the finite local-model lemma. The new categorical leaf was verified against the actual pinned Mathlib declaration and Hom formula, not just search descriptions.

In item step 1 the finite-type permanence theorem really concludes Noetherianity including quasi-compactness, since the source is the Noetherian field spectrum. The closed-subsets-minimal theorem really gives the chain condition used for topology; the affine quotient description checks the separated-diagonal quasi-compactness. In step 2 the new comparison applies to exactly the certified multiplication and the finite-subextension-valued algebraic closure. Its statement covers general module-object constructibility and equality of bounded object properties, so the step takes no information merely from a proof. Step 3 uses the explicit qcqs hypothesis and conclusion (2) of the finite-Tor theorem. Both hull definitions specify ordinary ambient coproducts, and I fixed the same indexing universe; no completed category is smuggled into the argument.

In step 4 the existence theorem provides $Rg_!\dashv J$ on the localizing categories, while proper comparison clause (1) supplies the isomorphism to the actual ambient restriction. The new Mathlib leaf has the correct orientation $Rg_!\cong F_g$ and preserves the right functor, so both adjunctions used in the final step have exactly left functor $F_g$. Step 5 checks the three constructors separately: the rational theorem covers both field cases; the integral Brown statement explicitly identifies its adjoint with the general one after the ctf/bc equalities; integral restriction applies to that functor. Characteristic, separatedness and finite type are present, and properness supplies the morphism hypotheses. Step 6 uses precisely the counit-compatible isomorphism given by uniqueness. Cohomology and stratum restriction are functors, so they carry that isomorphism to isomorphisms; composing each cokernel presentation with its inverse proves local finite presentation on the same finite stratification. This last operation is elementary, not an unrecorded preservation theorem.

For small cases I checked the zero module and zero complex, an empty scheme, the identity proper morphism, all degrees outside an input's cohomological range without imposing a false bound on the output, and integral torsion such as $\mathcal O_E/(\varpi)$. The comparison retains torsion scalar models and permits different stratifications, so it does not accidentally claim integral local freeness. The field assertions rely on the Noetherian-topology hypotheses of their existing nodes, and do not assert the result for arbitrary condensed rings. The algebraic-closure statement has the bounded finite-subextension meaning required by the retained target. There is no SGA citation. I inspected each residual argument for hidden lemmas; all non-elementary inputs are explicit citations, no proof step is over 2000 characters, and the assembly and extracted proof are each well below 3000. This is my direct-delivery review, as authorized by the worker brief; no other agent was started.

## What could not be finished

Nothing mathematical remains to complete the requested stage-1 refinement. The non-Mathlib helper is intentionally delivered statement-only under the stage-1 contract; its full proof and supporting dependencies are supplied above for its future claimant. Server dry-run and push results will be recorded after the required commands finish.
