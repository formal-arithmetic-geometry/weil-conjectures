# Stage-1 delivery: lem-sfb-ind-finite-free-scalar-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ind-finite-free-scalar-model.json`: item, statement; split into eight steps. The statement and statement dependencies are unchanged. No exact Mathlib match.
- `citations.json`: 25 verbatim statement quotations, one for every step/node citation.
- `searches.jsonl`: actual search-command log, retained unchanged.
- `report.md`: worker report and signed review.

New nodes: 0. New Mathlib leaves: 0. No unit/chapter record changed: this auxiliary item is not the unit's key statement.

## Attachments

None. The project source search for the full blueprint tag, ind-finite-free variants and scalar-model terminology found no declaration covering the complete item. Existing ordinary-module K-flat scalar-extension results do not assert the ringed-site filtered cocone, exactness and canonical unbounded counit together. In particular `WeilConjectures/Algebra/Homology/KFlatScalarExtensionDerivedIso.lean` concerns ordinary modules and homology equivalences, not this item.

## WANTED

None. All sources used for the split are present.

## Corrections and scope

The imported item had a complete statement but no proof. I retained every clause and supplied the argument. I did not replace the filtered category by a directed poset: the existing `lem-sfb-filtered-colimit-flat-module-sheaves` only states the poset case, so citing it here would lose a hypothesis check. Instead, tensor preserves the given small colimit and its assumed exactness suffices directly.

The ordinary restricted tensor is identified by `lem-weil-pbc-extension-tensor-comparison`, whose statement includes its effect on sheafification-unit images. A closed tensor adjunction alone would not justify that normalization. The derived comparison uses the existing K-flat-derived extension, rather than introducing another derived coefficient functor. The proof distinguishes quasi-isomorphism preservation on arbitrary inputs from the K-flat model theorem.

The blueprint ancestor is `lem-sfb-dc-hom-preserves`, via `lem-sfb-dc-hom-filtered-colimit`. Its final coefficient-descent paragraph is the place served. I read the chapter, the unit and this paragraph in the current main-20261015 snapshot. This is generic scalar infrastructure underneath that paragraph, with no change to the unit route. The unit's restriction-of-functors realization is outside this auxiliary item's scope.

## Mathlib searches

I ran the prescribed search command with two LeanFinder phrasings, Loogle, grep and LeanSearch. All five returned successfully and are recorded exactly in `searches.jsonl` and appended to the item's existing records. The inherited Q36 searches and their recorded results were retained. LeanFinder returned light-condensed internal projectivity/AB5 and ordinary-module flatness. Loogle returned no hits. Grep located the sheaf scalar-restriction implementation, which I read in `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean`: its declaration is scalar restriction, not the proposed theorem. LeanSearch returned ordinary-ring extension results; I read `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat` and `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` at `Mathlib/Algebra/Category/ModuleCat/Descent.lean:36-45`. Their objects are modules over ordinary rings and they do not specialize in one line to the full sheaf and derived assertion.

DAG and whole-blueprint searches covered scalar models, ind finite free, finite free scalar, tensor colimits and exact functors. I reused the existing generic tools rather than creating specialization nodes.

## Not duplicates

No new nodes were created; there are no new/existing-node pairs to distinguish.

## Review by NV

I read the item's source in `literature/stacks-project/sites-modules.tex`, Tag 03EU (`lemma-colimits-flat`), including its reference to 03EP (`lemma-tensor-commute-colimits`). I also read Section 03EK, 03EO (`lemma-internal-hom-adjoint-tensor`), 03CY (`lemma-sheafification-presheaf-modules`), and 03DA (`lemma-abelian`). The unbounded comparison was checked against `derived.tex`, 015F (`lemma-right-derived-exact-functor`), and `sites-cohomology.tex`, 06YY (`lemma-derived-base-change`) and `lemma-K-flat-resolution`; localization against `categories.tex`, 04VG (`lemma-properties-left-localization`). This is an agent assembly of these results and the stated existing DAG interfaces, not a verbatim theorem of one source. There are no new-node sources to review.

I opened the statement of every cited node and checked the following uses individually.

1. `lem-pc-sheaf-modules-tensor-closed` supplies symmetry, additivity and tensor unit R. `def-weil-sheaf-of-modules-category` supplies the abelian module category and kernel/cokernel formulas. Finite-biproduct exactness is written explicitly, rather than deferred to a new finite-free lemma. The finite ranks need not be positive.
2. `lem-weil-pbc-independent-sheaf-tensor-colimits` really states preservation of all coefficient-universe-small colimits, so it applies to the category I in this item. Symmetry is supplied by the closed-tensor node; `lem-weil-pbc-extension-tensor-comparison` supplies the actual restricted scalar-extension identification. The colimit definition supplies the specified legs. I checked that the *underlying module* colimit is an assumption, so no algebra-forgetful theorem is being assumed without citation.
3. Exact I-colimits are explicitly hypothesized, and Step 1 provides exact input sequences. `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` explicitly gives preservation of finite limits and colimits by scalar restriction. The scalar-restriction definition keeps the underlying abelian sheaf, and the module-category definition gives the kernel/cokernel constructions proving reflection of exactness in a few lines. Thus no assumption about sectionwise surjectivity, enough points or a nonzero coefficient ring is used.
4. The tensor definition specifies sheafification of sectionwise tensor. The extension/tensor comparison explicitly preserves the original pure-tensor images, and module sheafification has unique factorization of maps to a sheaf. These are the statements needed to justify the formula and its differential equation, not properties borrowed from a cited proof. Degreewise isomorphisms that commute with differentials have degreewise inverses commuting with them, so form a chain isomorphism.
5. I checked the two formulas for chain maps and coefficient maps. Their equality is precisely `h q_i = q'_i h_i`. Pure-tensor generation and the two stated universal properties finish this elementary step; no assertion that arbitrary sections are globally pure tensors is made.
6. The cohomology node asserts a natural isomorphism in every integer degree. The factorization node asserts preservation of quasi-isomorphisms and an induced unbounded derived functor. Their hypotheses hold by Step 3. Neither one requires bounded complexes.
7. `lem-weil-pbc-exact-functor-derived-functor` explicitly gives the *left* derived universal property as well as the right one. `lem-pur-derived-change-of-rings` supplies the existing K-flat-derived functor and canonical model comparisons. `lem-pc-kflat-resolution` supplies resolutions for arbitrary unbounded complexes on this site. I wrote the two-universal-properties argument for uniqueness, and the naturality equation identifying the counit with Q(Ep). Exactness of E permits arbitrary A here; it is not necessary to assume A K-flat or to choose functorial resolutions.
8. Exact scalar restriction and exact-functor cohomology justify inverting quasi-isomorphisms on every functor involved. `lem-weil-pbc-localization-universal-property` explicitly states fully faithful descent of natural transformations and their equations. I wrote both the inverse-arrow argument and the coefficient/resolution square, so the final compatibility is not merely asserted by the word transport. Coefficient comparisons are read after the indicated exact restriction to a common scalar category.

I checked small cases: all-zero complexes, unbounded complexes, zero coefficient rings, finite free rank zero, a constant one-object diagram, and general filtered categories with parallel arrows. Zero-rank stages and the zero ring cause no nonzero/fidelity assumptions. No monotonicity of ranks, compatible bases, injective transition maps, or sectionwise formula for sheaf colimits is used. On the one-object diagram the cocone comparison reduces to the canonical tensor/scalar comparison. The argument uses no property special to a poset. Every step is below 2000 characters and no long-step sublemma is concealed.

The off-unit statements are generic tensor, scalar, K-flat and localization tools; the item's `split_report.tool_uses` lists each with its purpose. Definitions and the existing Mathlib leaves remain their own notions/tools. These citations implement the scalar model already selected by the item's parent and do not replace a constructibility argument of the unit.

This checks delivery-errors B through E: no statement-only new node or duplicate to audit; no hidden new notion; citations refer to the statements actually used; the substantive proof stays in the item; and all hypotheses and normalization formulas have been checked. The statement needed no dispute or correction.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes keep their current independent status. No Lean was written and no compiler, Lake or local DAG/preflight checker was run. The server `review_split` check passed with zero new nodes before the full delivery dry run.

The first full dry run found one citation excerpt shorter than the tool's 40-character minimum. I replaced it with the complete scalar-restriction definition, preserving its exact text; the mathematical step was unchanged.
