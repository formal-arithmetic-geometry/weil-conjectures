## Worker report

Q47 repaired `def-sfb-derived-extend-comp-iso` for the 2026-10-21 finer-split return. The sandbox initially contained only dispatcher marker files: no prior node, report or search log. I used the current repository's reviewed four-step split as the returned baseline. I retained its statement verbatim, source, imports' metadata, existing Lean attachment and earlier searches. The only change of mathematical organization is to extract the two independent derived-localization interfaces from old step 4. The item now has 1695 characters of proof, down from the returned 3193; no individual step exceeds 600 characters.

Files written: the item JSON, the two new statement-node JSON files listed below, `citations.json`, this report, and the sandbox-only repair script. `searches.jsonl` was produced by the prescribed msearch command. No repository/launcher file was written; no Lean, compiler, Lake or build command was run.

## New nodes

- `lem-sfb-exact-derived-composition`: statement; not a direct leaf in the pinned Mathlib. Gives the normalized comparison D(GF) ≅ D(G)D(F) for arbitrary exact additive functors. Exact project attachment candidates exist.
- `lem-sfb-exact-derived-natural-iso`: statement; not a direct leaf in the pinned Mathlib. Gives descent of a specified natural isomorphism F ≅ G, with its representative normalization. Exact project attachment candidates exist.

These are separate interfaces, neither of which states the coefficient-extension theorem: the first has no underived comparison to another functor, and the second has no composition or scalar-extension assertion. Their complete proofs in words are immediately below. The new node records remain statement-only with status unsplit, as required by the stage-1 delivery format; these are not unexplained new mathematical obligations, because the existing project declarations below already prove their existence interfaces. The maintainer can verify the attachment candidates instead of formalizing them again.

## Proof of lem-sfb-exact-derived-composition

Let C(H) be termwise application and a_H:D(H)Q ≅ QC(H) the exact factorization of `lem-weil-pbc-exact-functor-derived-factorization`. Composition of exact functors is exact, since preservation of each finite limit and finite colimit composes, and additivity composes. At a complex K, first apply D(G) to a_F,K and then a_G,C(F)K. This identifies D(G)D(F)Q_A with Q_C C(G)C(F). Termwise objects, differentials and maps are G(F(K^n)), G(F(d^n)) and G(F(u^n)), so C(G)C(F)=C(GF). Thus D(GF) and D(G)D(F) are two lifts of the same functor Q_C C(GF). Apply clause (2) of `lem-weil-pbc-localization-universal-property` to the identity of that functor: it gives μ and precisely the displayed normalization. Clause (3) gives uniqueness. No resolution, boundedness, adjoint, or flatness condition is used.

This is the construction in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, `mapDerivedCategoryCompIso` (current lines 175–195) and its normalization `mapDerivedCategoryCompIso_fac` (202–216). The composition comparison on complexes is Mathlib `Functor.mapHomologicalComplexCompIso (Iso.refl _)`, read at Additive.lean:212–216. This proof is under 1300 characters.

## Proof of lem-sfb-exact-derived-natural-iso

For a complex K, naturality gives G(d^n)η_K^n=η_K^(n+1)F(d^n), so the degreewise η components form a chain map C(F)K→C(G)K. The inverse components form its inverse; both inverse identities hold degreewise. Naturality against chain maps follows degreewise from naturality of η. Apply Q_B and conjugate by a_F,a_G from `lem-weil-pbc-exact-functor-derived-factorization`. This is a natural isomorphism between D(F)Q_A and D(G)Q_A. Clause (2) of `lem-weil-pbc-localization-universal-property` descends it to D(η), including its inverse and the stated representative formula. Clause (3) gives uniqueness. Exactness supplies the factorizations and preservation of quasi-isomorphisms; it is not inferred from the mere existence of η.

This is `mapDerivedCategoryNatIso` (current lines 107–116) and `mapDerivedCategoryNatIso_fac` (122–143), in the same project module. Its ingredients are Mathlib `NatIso.mapHomologicalComplex` (Additive.lean:198), whiskering by Q_B, and `Localization.liftNatIso` (Predicate.lean:357). This proof is under 1100 characters.

## Attachments

`CategoryTheory.Functor.mapDerivedCategoryCompIso` belongs to `lem-sfb-exact-derived-composition`, together with `CategoryTheory.Functor.mapDerivedCategoryCompIso_fac`, in `lean/WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`:175 and :202.

`CategoryTheory.Functor.mapDerivedCategoryNatIso` belongs to `lem-sfb-exact-derived-natural-iso`, together with `CategoryTheory.Functor.mapDerivedCategoryNatIso_fac`, in the same file :107 and :122.

I read the constructions and factorization equations. The full retained sorry map `local/sorry_map_slopmaster2_full.jsonl.gz` has s=false, ts=false for both construction declarations and their auxiliary proofs (its older line ranges are 161–186 and 94–105). The current bodies use Mathlib operations only, rather than a project existence axiom. The representative-normalization lemmas were read in the current source; the uniqueness assertion is localization faithfulness. New nodes record these as `lean_candidates`, leaving the maintainer-owned Lean/audit fields to the maintainer.

The item itself is not an ATTACH outcome: its existing composite is sorry-free in its own body but depends on the still open flatness/derived-extension framework. I retained its existing Lean record and did not claim its transitive closure is finished.

## WANTED

None. The blueprint, Stacks source, project source and pinned Mathlib used here are available locally. No SGA source is used.

## What was wrong and what changed

The returned proof placed exactness, the ordinary scalar comparison, and both distinct derived-functoriality constructions in one item. The human specifically requested finer stage-1 decomposition while preserving its statement. I kept the correct scalar-extension route and removed the chain-level lifting/composition arguments from the item into the two independent interfaces above. I did not recreate the underived scalar-composition node that the previous review correctly removed: the restriction-action calculation and the pasted Hom bijections are elementary, while uniqueness of left adjoints already has a node. No statement dispute, counterexample to the source, target weakening, or route change was found.

Mathlib searches used the prescribed command only and their results were read. Two semantic phrasings were tried for each extracted interface. Online Loogle exposes a newer `mapDerivedCategoryCompIso_hom_app_Q_obj`, but the pinned local Mathlib contains no `mapDerivedCategoryCompIso` or `mapDerivedCategoryNatIso`; I did not turn that index hit into a false pinned-Mathlib leaf. Mathlib supplies the termwise isomorphisms, exact factorization and localization lifting individually; the actual assembled interfaces are in the project module. Each new node records the exact logged queries. The initial zero-hit grep included `def mapHomologicalComplexCompIso`, which misses Mathlib's qualified declaration spelling; the subsequent grep with `mapHomologicalComplexCompIso` found Additive.lean:212 and that file was read. A grep directed at a single file caused msearch's output formatter to treat the line number as a filename; I repeated the substantive grep on the Algebra/Homology directory and used its correctly formatted paths/lines.

## Not duplicates

lem-sfb-exact-derived-composition vs lem-sfb-adjunction-localization: the existing node derives an adjunction given lifts of both adjoints; the new node constructs composition of exact induced functors with no adjunction hypothesis.
lem-sfb-exact-derived-composition vs lem-weil-pbc-derived-square-iso-commshift: the existing assertion is shift compatibility for a bounded-below geometric pullback square; the new one is the arbitrary unbounded exact-functor compositor.
lem-sfb-exact-derived-composition vs lem-weil-pbc-localization-universal-property: the existing node supplies the abstract lifting/uniqueness theorem used in the proof; the extracted interface supplies the assembled exact-derived compositor and its explicit factorization equation.
lem-sfb-exact-derived-natural-iso vs lem-sfb-adjunction-localization: deriving units and counits of an adjunction is different from descending a specified isomorphism of two exact functors without adjoints.
lem-sfb-exact-derived-natural-iso vs lem-weil-pbc-derived-square-iso-commshift: the latter concerns shifts of a particular geometric square on D+; the new node gives the general natural-isomorphism lift on D.
lem-sfb-exact-derived-natural-iso vs lem-weil-pbc-localization-universal-property: the existing abstract theorem is cited by the proof; the new interface includes the termwise chain isomorphism and its exact-derived representative normalization.
lem-sfb-exact-derived-composition vs lem-pod-derived-exact-square-composition: that node assumes a full diagram of exact squares and compositors to prove a pasting equation; it does not independently construct the two-functor compositor interface.
lem-sfb-exact-derived-natural-iso vs lem-pod-derived-exact-square-composition: the existing result is a composition coherence identity in a six-category diagram, not the single pair of functors and prescribed natural isomorphism here.
lem-sfb-exact-derived-composition vs lem-kun-derived-single-constants-comparison: the latter evaluates a composite comparison on single complexes; it requires and uses the comparisons extracted here, rather than stating their general construction and uniqueness.
lem-sfb-exact-derived-natural-iso vs lem-pc-ext-exact-functor-square: the latter is an equality of maps on Ext groups, not a comparison on all unbounded derived objects.

## Review by Q47

I read the current blueprint item's statement and its entire `.proof.md`, its chapter record and the two-colimit unit record, the preserved four-step repository split, and the actual `derivedExtendScalarsCompIso` source in TwoColimit.lean:131–145. The prime, arbitrary scheme, finite inclusions and full unbounded internal-module categories are unchanged. In particular there is no restriction to bounded constructible objects, no invertibility-of-ell hypothesis and no finite-type hypothesis on X.

For both new nodes I read Stacks categories.tex Tag 04VG, label lemma-properties-left-localization (4406–4427), and its actual scope: it states functor factorization, not the full natural-transformation enhancement. I explicitly use the existing localization-universal-property node for that enhancement, whose statement includes lifting natural isomorphisms and full faithfulness. I read Mathlib Predicate.lean:278 and :357 and the exact-derived factorization in ExactFunctor.lean:36–56. Stacks derived.tex Tag 015F, label lemma-right-derived-exact-functor (5884–5904), supplies the background exact-termwise route; it is not misquoted as a theorem about natural transformations. The project source constructions and their normalization equations give the two interfaces exactly. Complete independent short proofs are above, with all non-elementary ingredients named by existing nodes.

For item step 1 I reopened `sk-def-sfb-change-of-scalars`: clause (2) states that Ext is left adjoint and preserves finite colimits. I reopened both flatness nodes: subfield-flat gives finite-limit preservation for E≤F, and qlbar-flat gives it for each finite field, hence separately for F and E. Right and left exactness here mean the required finite-colimit and finite-limit preservation; additivity is supplied by these abelian scalar-extension functors. I read both derived-extension definitions, which identify exactly the three total left-derived functors and their source/target categories. No flatness of an unrelated coefficient map is substituted.

For step 2 I checked the action formula against clause (1) of change-of-scalars, including the action order and the fact that the underlying morphisms do not change. Pasting its two Hom bijections is a direct calculation of the adjunction, so this step remains elementary. For step 3 I reopened `lem-weil-pbc-conjugate-iso-unit-equation`: its equal-right-adjoint case explicitly gives the needed unit-compatible isomorphism, rather than merely full faithfulness of Yoneda. The coefficient-map-composition node states precisely ψφ=χ for every X, and `def-sfb-extend-scalars-iso-of-eq` explicitly defines the equal-map comparison via equal restriction functors. Those are exactly the two identifications made in the step.

For step 4 I reread the exact-functor clause of `sk-def-sfb-derived-categories`, including its existence hypotheses. These are the very left-derived functors fixed by the two statement dependencies in the existing module-object framework; no new universal existence claim is made for arbitrary abelian categories. The new generic composition and natural-isomorphism lemmas require only exact induced functors and derived localizations, so apply to A,B,BA,C from steps 1–3. BA is exact by composition of finite-limit/colimit preservation. I checked the direction: μ goes D(BA)→D(B)D(A), hence its inverse precedes D(θ) in the item's assembly. All types end in D(Mod_QbarX). `citations.json` contains a verbatim statement quote for every cited node of every item step.

I searched all DAG node statements/source places and the whole imported blueprint by `blueprint_refs.py search` for exact functors, natural isomorphisms, composition, composite exact functors and the shared tag. I read the potentially overlapping localization, exact-factorization, derived-square and single-complex comparison nodes; the distinctions are recorded above. The abstract localization theorem and exact-factorization theorem are reused, not reproved. The two new interfaces correspond to already independent project declarations and represent precisely the smaller formalization boundaries requested by the human; they do not replace the item's coefficient-specific proof by a renamed theorem.

Edge checks: F or G equal to the identity gives the standard identity comparison; F=G and η=id gives the identity transformation by uniqueness. Zero functors and zero complexes give identity maps of zero objects. The chain-map equation applies in every integer degree, so unbounded complexes cause no truncation or convergence issue. E=F, E=Q_ell and X empty all satisfy the unchanged coefficient proof. There is no small indexing category, tensor-product-flatness claim or geometric support factorization hidden in these arguments. None of the new statements adds hypotheses to the item. All item steps and both supplied auxiliary proofs are well below 2000 characters; nothing is left as 'standard compatibility'.

The accepted off-unit adjoint-uniqueness tool remains declared in the item's `split_report.tool_uses`. The auxiliary proofs use the already existing Mathlib-leaf exact-factorization and localization interfaces as generic tools. The delivery requests no maintainer-field changes. The one return point has been repaired by a substantive change of proof dependencies, not a rebase: the old long inline argument has become two named interfaces, with short source-checked proofs and existing Lean candidates.

## Unfinished work

None within this stage-1 repair. Independent attachment verification and review remain the maintainer's responsibility. The required dry run and push results are recorded by the delivery command.
