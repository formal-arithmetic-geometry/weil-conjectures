# Stage-1 delivery: lem-sf-ringed-localization-rhom-orthogonality

## Files written

- `dag/nodes/sec-six-functors/lem-sf-ringed-localization-rhom-orthogonality.json`: statement node, split into six steps; unchanged statement and statement dependencies. No Mathlib match for the item.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report. The sandbox also retains the actual search log and the sandbox-only writing helper.

No new DAG nodes or new Mathlib leaves. No unit file changed: the item is a descendant tool, not the key statement of the unit.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` tree for the exact blueprint tag and for localized/derived internal Hom, coinduction and scalar restriction. No declaration states this ringed-site derived isomorphism and its vanishing consequence. The master source was consulted as reference only. General homotopy-category internal-Hom constructions do not constitute an attachment for this item.

## WANTED

None. All needed sources are present in `literature/stacks-project/`.

## Corrections and route

The imported statement is correct and remains verbatim. It is exactly Stacks Tag 0996, `algebraization-lemma-map-twice-localize`, clause (2), followed by Tag 0997, `algebraization-lemma-hom-from-Af`, implication (1) to (2). The previously empty proof is now the K-injective calculation in those sources. The ordinary sheaf coinduction formula cited there as Tag 0932 is written out with its inverse instead of being left as an uncited fact. Its K-injective consequence is an application of the already existing, general `lem-weil-pbc-right-adjoint-preserves-kinjective` (Stacks 08BJ).

The proof needs K-injectivity of coinduction as an O_f-complex. It never uses K-injectivity after forgetting back to O, so the source's additional flatness-based preservation assertion is unnecessary for this clause. No flatness assumption is added. Both rings are commutative sheaves on the same small site; there is no switch between module objects, sheaf modules, ordinary modules or completed coefficient categories.

I read the chapter and unit records, the current main-20261015 ancestor `prop-sf-dualizable-hom`, and the corresponding older node proof. The ancestry through `lem-sf-ringed-rhom-derived-complete` and `lem-sf-rational-thick-evaluation` is retained. This input supplies orthogonality used in completeness for the evaluation construction; it does not replace the unit's bounded finite-projective computation. `blueprint.same_as` is empty after whole-blueprint searches for the concept, coinduction, 0996 and 0997. Generic resolution and right-adjoint preservation are declared tool uses in `split_report`; the homotopy/derived mapping comparison is an existing Mathlib leaf.

## Mathlib searches

I preserved the item's earlier N9 search records. I ran and read seven additional logged queries using the required `msearch.py` command, including two semantic phrasings, Loogle, LeanSearch, a broad source grep and targeted greps in sheaf modules and derived categories. The broad case-insensitive grep returned false positives such as `inrHom`, star-hom names and `mkCoinductive`; the targeted greps returned zero hits. LeanSearch found `ModuleCat.restrictCoextendScalarsAdj` and `SheafOfModules.restrictScalars`. Reading `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` and `Sheaf/ChangeOfRings.lean` confirms that these concern ordinary modules and underived sheaf restriction, respectively. They do not give the item by a one-line specialization. The second LeanFinder query returned derived degree-vanishing facts, whose hypotheses and conclusion do not assert localization orthogonality. Every new record uses exactly the tool and query text actually run; no unavailable service is treated as evidence of absence.

## Not duplicates

No new nodes. In particular I did not duplicate the existing general right-adjoint/K-injective lemma, K-injective existence, or the ordinary-module coextension interface. The sheaf coinduction maps and exactness of restriction are elementary steps derived explicitly from the existing sheaf-Hom, module-category and restriction definitions. The scheme-specific `lem-sc-sheaf-coinduction-adjunction` is insufficient as a black box for an arbitrary ringed site and is not cited. The module-object coextension statements would require a separate realization comparison and are not substituted silently for sheaf modules.

## Review by Q11

I read the complete statement and relevant proof of Stacks 0996 and 0997 in `algebraization.tex`; 0932 in `sites-modules.tex`; the kernel/cokernel discussion and 03DA in that file; 08BJ and 070I in `derived.tex`; and the K-injective and internal-Hom sections 07A5 and 08J7 of `sites-cohomology.tex`. There are no new-node sources to review. I opened the statement of every cited DAG node and generated citations only from verbatim substrings of those statements.

Step 1 takes the actual kernel and sheafified-cokernel descriptions from `def-weil-sheaf-of-modules-category`, the unchanged additive sheaf from `def-pc-sheaf-restrict-scalars`, and the cohomology/localization description from `def-weil-abstract-derived-category`. These show exactness and detection of acyclicity; I do not assume sectionwise surjectivity of an epimorphism. I corrected an early draft's source reference from 03EM (internal sheaf Hom) to the correct 03DA/03D9 kernel-cokernel source.

Step 2 uses `def-pur-sheaf-hom` for the existing sheaf of morphisms on each slice, not as a citation of an adjunction theorem. The proof supplies that adjunction: multiplication on the argument defines the O_f-action, and the maps a(m) to (c to a(cm)) and evaluation at 1 are inverse. O_f-linearity gives the second inverse equation. These formulas respect restriction, addition and pre/postcomposition. This is a short direct argument from the definitions and is marked elementary; there is no new node merely for this calculation.

Step 3 uses `prop-pur-kinjective-resolutions-exist` with its required small site, and `def-weil-sheaf-of-modules-category` for abelianness at both coefficient rings. It then uses precisely the conclusion of `lem-weil-pbc-right-adjoint-preserves-kinjective`, after verifying its additive-adjunction and exact-left-adjoint hypotheses in steps 1 and 2. Its variables are instantiated as u=coinduction, v=restriction, A=O-modules and B=O_f-modules, in the direction the node states. `def-pur-derived-internal-hom` explicitly permits computation using any K-injective target, so H(I) really represents the inner derived Hom with the required O_f-action. No locally free or flat representative is presumed.

Step 4 uses the product-of-sheaf-Homs terms and signed differential given by `def-pur-hom-complex`, together with the local-section meaning of `def-pur-sheaf-hom` and scalar restriction. The inverse formulas from step 2 apply on every slice. I checked the displayed differential identity: d_F is O_f-linear, so d_F(cm)=c d_F(m), and the same sign (-1)^n occurs on both sides. Taking a product of these mutually inverse component maps gives an actual isomorphism; there is no claim that infinite products preserve arbitrary exact sequences.

Step 5 uses `def-pur-derived-internal-hom` for computation, representative independence and functoriality. The generic Mathlib leaf `lem-weil-pbc-kinjective-hom-derived` really states the bijection from homotopy classes to derived maps into every K-injective target; it supplies the assertion about arbitrary morphisms of K used for naturality. Additivity and the componentwise Hom formulas preserve homotopies. Thus naturality is for derived objects, not just for the chosen chain maps. The right side is explicitly restricted from D(O_f) to D(O), so both sides have the same type.

Step 6 uses cohomology factoring through localization from `def-weil-abstract-derived-category`, the computation and invariance of `def-pur-derived-internal-hom`, and the actual zero-target K-injective and Hom-complex definitions. The underlying coinduction complex being zero in D(O) implies acyclicity over O_f by step 1. The map 0 to that complex is then a quasi-isomorphism; computation against the zero K-injective gives zero derived internal Hom. This proves the consequence without assuming that O generates its entire sheaf-derived category.

I checked f=1 (both rings agree and both evaluation formulas reduce to the identity), f=0 or nilpotent (O_f is the zero sheaf, whose module category is zero), K=0, L=0, and an empty site. On a one-object ring site the calculation is the usual restriction/coextension adjunction. Unbounded complexes only require products already present in the Hom-complex definition; no boundedness or finite-generation step enters. No statement dispute or source error was found.

I reviewed B through E of `coord/delivery-errors.md`: no statement-only child carries a proof because no child is created; every non-elementary input is an existing cited statement with its hypotheses checked above; the proof neither restates its clauses as new nodes nor forms a circular dependency. All six steps are shorter than 1,000 characters, so none triggers the long-step threshold or hides a separate non-elementary lemma in a long comparison.

## Unfinished work and verification

Nothing mathematical is left unfinished in this one-level split. Existing cited unsplit nodes remain their owners' work. No Lean was written, no compiler or Lake command was run, and no live/shared project file was changed. The server-only `review_split` preliminary check passed with zero new nodes. The required delivery dry run and push follow this report.
