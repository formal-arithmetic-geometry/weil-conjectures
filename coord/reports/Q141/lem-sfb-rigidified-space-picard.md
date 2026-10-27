# Worker report — Q141, lem-sfb-rigidified-space-picard

## Files written

All node files are in `dag/nodes/sec-six-functors-basics/` in the item sandbox.

- `lem-sfb-rigidified-space-picard.json`: item, statement unchanged, six-step split.
- `lem-sfb-space-geometric-h0.json`: statement, unsplit; Mathlib no match. Universal functions for proper flat finitely presented spaces with nonempty reduced connected geometric fibres, Stacks 0E0S.
- `lem-sfb-space-picard-sheaf-representability.json`: statement, unsplit; Mathlib no match. Unpointed Picard sheaf representability and quasi-separated local finite presentation for algebraic-space total spaces, Stacks 0D2C/0DNI.
- `lem-sfb-space-fppf-invertible-locality.json`: statement, unsplit; Mathlib no match. A quasi-coherent module whose fppf pullbacks are line modules is a line module, Stacks 060X/0DFQ. Effective module descent itself reuses `lem-sfb-space-fppf-qcoh-descent`.
- `lem-sfb-space-valuation-line-triviality.json`: statement, unsplit; Mathlib no match. The valuation-ring line-module argument in the proof of Stacks 0DNJ, not the theorem's separatedness conclusion.
- `lem-sfb-space-valuative-separatedness.json`: statement, unsplit; Mathlib no match. Quasi-separatedness and valuative uniqueness imply separatedness for morphisms of algebraic spaces, Stacks 03KV.

`citations.json` contains a literal statement quote for every use in every proof step. The existing item's searches, source, statement, provenance and inherited blueprint chain have been retained. `searches.jsonl` records the actual Q141 searches; the sandbox Python scripts in the sandbox only assembled and audited these JSON files. No Lean file, compiler or Lake tool was used. No repository or launcher file was written.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, the blueprint docstring tag, rigidification and Picard terminology. Read the relevant scheme Picard presheaf and rigidification interfaces: `AlgebraicGeometry/PicardFunctor.lean`, `AlgebraicGeometry/Modules/Rigidification.lean`, and the scheme Picard descent references. No project declaration states all clauses for algebraic-space total spaces. The final additional search for all five new ids and algebraic-space Picard/fpqc/generic-triviality terminology returned no hits. Scheme-only statements are not treated as attachments.

## Wanted literature

None. All sources used are in `literature/stacks-project/`. No SGA source is used.

## Audit of the imported item and route

The item was unsplit, with no proof and no repair note. Its imported statement is correct against 0E0S, 0D28, 0D2B, 0D2C, 0DNI and 0DNJ. No statement dispute or weakening was necessary. The source's normalization argument needs actual descent, and source 0DNJ supplies a valuation-ring argument, rather than a reason to assume that the whole Picard space is proper. I kept these two issues separate in the proof.

Read SETUP's three levels, GOAL, the chapter and unit records, and the latest blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`. This is an auxiliary prerequisite along the inherited direct-images (3), alteration, stable-curve, Jacobian and Poincare route, not a new realization of the unit's main theorem. No chapter or unit record was changed. `blueprint_refs.py ancestor` returns no surviving imported ancestor (`None`) for this inherited chain; the new nodes keep that result, prepend the item to the existing via chain, and give their precise role in `from.place`. Whole-blueprint searches for Picard, rigidification, descent, global sections, geometrically reduced fibres, valuative criteria and the source tags found no blueprint node stating any of the five new space-level tools.

`lem-trf-space-fibre-products-etale-covers` is declared in `split_report.tool_uses`: it supplies underlying algebraic-space fibre products and pullbacks of etale atlases, not a substitute proof route. The other reused space-locality result is in the same unit. Canonical module direct image and tensor pullback use the existing definition `def-trf-space-etale-module-functors` in the statement dependencies; they are not newly chosen operations.

## Mathlib searches

Every new node has logged LeanFinder, LeanSearch, Loogle and source-grep searches. The natural-language LeanFinder and LeanSearch queries use different formulations, recorded verbatim in each node. The item itself was searched again while retaining its earlier searches. All services used answered successfully; no unavailable service was recorded as a negative result.

For geometric H0 the hits were scheme flatness, geometrically reduced scheme morphisms and ring-module facts, not proper-space H0/base change. For the unpointed Picard sheaf the hits were scheme local representability, finite presentation, and `CommRing.Pic`/`CommRing.relPic`. I read the ring Picard file introduction and definitions: these classify invertible modules over a ring, not the relative Picard sheaf of a proper algebraic space. The final invertibility-locality searches found generic `SheafOfModules.IsLocallyFree` data and constructors, faithfully flat ring-module tests and scheme morphism descent. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean:47` and `:61`: they concern local freeness on a fixed site, not detection of etale-local rank one after an fppf map of algebraic spaces. They do not state the new invertibility-reflection theorem. The original effective-descent queries remain in searches.jsonl for audit, but that draft node was removed after the dry run located the reusable existing quasi-coherent descent node. Valuation-line searches returned valuation-square fields/rings and topological trivial bundles, not generic triviality for proper families.

For valuative separatedness there is a close hit, `AlgebraicGeometry.IsSeparated.of_valuativeCriterion`, `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:246`. I read lines 232–260. Its variables are schemes; it cannot be specialized to arbitrary algebraic spaces in one line, so the new node is unsplit rather than a Mathlib leaf. This is the principal type mismatch checked in the search review.

## Not duplicates

The following comparisons include all existing records found by full-DAG source-tag searches, including incidental references and the parent item, plus the relevant keyword candidates. A common source is not treated as evidence that the statements agree.

lem-sfb-space-geometric-h0 vs lem-sfb-rigidified-space-picard: the new theorem has arbitrary algebraic-space target and only nonempty reduced connected fibres, with no section, integrality or Noetherian requirement; it does not assert Picard representability or rigidification.

lem-sfb-space-geometric-h0 vs lem-sfb-abelian-space-poincare-calculus: the existing theorem concerns dual abelian spaces and Poincare identities; it does not state universal functions for arbitrary reduced connected proper flat families.

lem-sfb-space-geometric-h0 vs lem-sc-proper-flat-global-sections: the existing theorem has scheme source and target; the new theorem allows algebraic spaces.

lem-sfb-space-geometric-h0 vs lem-sc-proper-flat-global-sections-criterion: the existing criterion is for schemes and assumes fibre H0 directly; the new theorem concerns spaces with reduced connected geometric fibres.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-rigidified-space-picard: the new theorem represents the unpointed fppf sheaf without a section or integral fibres; the item must construct its identification with actual rigidified objects and its universal family, and prove separatedness.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-flat-proper-picard-algebraic-space: the existing theorem requires X and S to be schemes; the new theorem permits an algebraic-space total space.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-picard-space-curves-smooth: the existing result has scheme total space and fibre dimension at most one; the new theorem permits arbitrary-dimensional algebraic spaces and makes no smoothness assertion.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-projective-picard-identity-representability: the existing theorem treats smooth projective geometrically integral schemes over an algebraically closed field with a point and identity-component properties; the new theorem needs neither projectivity, a field base nor a section.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-stable-relative-picard-kummer: the existing statement gives the neutral Picard space and Kummer comparison for stable curves; it does not state general space-level unpointed representability.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-nodal-multidegree-zero-locus: the existing statement concerns the multidegree-zero locus of an already represented stable-curve Picard functor; it assumes rather than proves representability.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-nodal-picard-etale-schematic: the existing statement concerns the represented multidegree-zero part of a projective nodal curve family; it does not construct the full unpointed sheaf for arbitrary spaces.

lem-sfb-space-picard-sheaf-representability vs lem-sfb-abelian-space-poincare-calculus: dual abelian spaces are a special family with extra structure, and their dual represents only algebraically trivial line modules; this new theorem represents the full relative Picard sheaf of arbitrary proper flat spaces.























lem-sfb-space-valuation-line-triviality vs lem-sfb-rigidified-space-picard: the new theorem is a line-module triviality result over an arbitrary valuation ring, with no section, Picard object or rigidification; the item uses it for a tensor difference and still has to prove valuative uniqueness and separatedness.

lem-sfb-space-valuation-line-triviality vs lem-sfb-abelian-space-poincare-calculus: the existing theorem states duality and universal identities for abelian spaces, not a valuation-ring criterion for arbitrary proper flat spaces.

lem-sfb-space-valuation-line-triviality vs lem-sc-picard-locus-closed-valuation-triviality: the existing theorem concerns a scheme over a valuation ring; the new result permits an algebraic-space source. The existing theorem cannot be applied etale-locally on the source because an etale chart need not be proper.

lem-sfb-space-valuative-separatedness vs lem-sfb-rigidified-space-picard: the new theorem is the general separatedness criterion for an arbitrary quasi-separated space morphism, with no Picard, properness or line-module hypotheses.

lem-sfb-space-valuative-separatedness vs lem-a1-space-fpqc-separated-valuative-descent: the existing theorem descends separatedness and the full valuative lifting property from a cover; the new theorem derives separatedness from uniqueness alone and has an arbitrary algebraic-space target.


lem-sfb-space-fppf-invertible-locality vs det-thm-picard-descent: the existing detailed theorem concerns scheme covers; the new statement permits algebraic spaces throughout.

lem-sfb-space-fppf-invertible-locality vs lem-pc-fpqc-descent: the existing theorem detects finite local freeness on scheme covers; its source and target are schemes, whereas the new statement concerns modules on algebraic spaces.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-finite-locally-free-fppf-descent: the existing theorem descends finite locally free morphisms of schemes (finite covers), not rank-one quasi-coherent modules on algebraic spaces.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-fppf-face-heart-descent: the existing statement concerns Effective quasi-coherent module descent with face maps; it does not state that arbitrary fppf space pullbacks detecting rank-one freeness make a given quasi-coherent module invertible.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-regular-space-divisor-line-dictionary: the existing theorem compares Cartier/Weil divisors and line modules on regular Noetherian spaces; the new statement detects invertibility for arbitrary fppf space covers without those regularity hypotheses.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-rigidified-space-picard: locality of invertibility of a given quasi-coherent module does not state any Picard representation, normalization, rigidification, or universal family.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-finite-fppf-descent: the existing theorem detects finite morphisms of spaces, not invertible quasi-coherent modules.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-flat-proper-fp-locality: the existing theorem is locality and base-change permanence of flatness, properness and finite presentation of space morphisms; the new result detects invertibility of modules.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-four-property-fppf-descent: the existing theorem descends properties of space morphisms, not invertibility of modules.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-fppf-finite-affine-refinement: the existing theorem refines fppf coverings by affine scheme tests; it does not conclude that a module is locally free.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-fppf-qcoh-descent: the existing theorem gives an equivalence of quasi-coherent modules with descent data and descent of morphisms; it does not assert that an object with locally rank-one pullbacks is invertible. The proof reuses that equivalence and takes only this remaining local-freeness assertion from the new node.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-lft-smooth-fpqc-locality: the existing theorem detects locally finite type and smooth morphisms; the new result concerns local rank-one module freeness.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-quasi-compact-immersion-locality: the existing theorem detects a space immersion property; it does not assert rank-one freeness of modules.

lem-sfb-space-fppf-invertible-locality vs lem-sfb-space-quasicompact-fppf-local: the existing theorem detects quasi-compactness of morphisms, not rank-one freeness of modules.

lem-sfb-space-fppf-invertible-locality vs lem-trf-algebraic-space-invertible-descent: the existing theorem constructs line modules from data on etale scheme atlases; the new statement detects invertibility of a given quasi-coherent module after arbitrary fppf algebraic-space covers.

lem-sfb-space-fppf-invertible-locality vs lem-trf-ample-scheme-test-line-preparation: the existing theorem prepares scheme tests of etale-local ampleness; it assumes the line module and does not detect invertibility of a quasi-coherent module.

lem-sfb-space-fppf-invertible-locality vs lem-trf-etale-scheme-line-morphism-gluing: the existing theorem glues morphisms of scheme families with specified line-module homomorphisms over etale scheme covers; it does not detect freeness after fppf space covers.

lem-sfb-space-fppf-invertible-locality vs lem-trf-polarized-fine-log-etale-descent: the existing theorem descends polarized fine log schemes over etale scheme covers; it does not give invertibility reflection on fppf space covers.

lem-sfb-space-fppf-invertible-locality vs lem-trf-polarized-scheme-etale-descent: the existing theorem descends polarized scheme families over etale scheme covers; the new result detects invertibility on arbitrary fppf space covers.

lem-sfb-space-fppf-invertible-locality vs lem-trf-scheme-descent-cocycle-etale-relation: the existing theorem constructs an etale relation from scheme descent cocycles, not a local-freeness test.

lem-sfb-space-fppf-invertible-locality vs lem-trf-scheme-descent-quotient-chart-isomorphism: the existing theorem identifies quotient charts of descended schemes; it has no module local-freeness conclusion.

lem-sfb-space-fppf-invertible-locality vs sk-thm-picard-descent: the blueprint statement concerns quasi-coherent modules on schemes and scheme covers; the new statement detects rank-one freeness on fppf algebraic-space covers.

## Review by Q141

I read delivery-errors B–E with the node statements and Stacks source open. The original item has no statement discrepancy: proper flat finite presentation and geometric integrality supply 0E0S, a section supplies normalization in 0D28, the scalar calculation is 0D2B, 0D2C supplies an unpointed space, 0DNI its quasi-compact diagonal and local finite presentation, and 0DNJ proves separation. The extra universal-family clause really needs algebraic-space descent; it is not obtained by applying scheme Yoneda directly to P.

For the five new statements I read respectively spaces-perfect.tex `lemma-proper-flat-geom-red-connected` (0E0S); quot.tex `situation-pic` (0D25), `proposition-pic-functor` (0D2C), and moduli.tex `lemma-pic-functor-qs-lfp` (0DNI); spaces-descent.tex `lemma-finite-locally-free-descends` (060X), rank-one case, and spaces-topologies.tex `lemma-zariski-etale-smooth-syntomic-fppf-fpqc` (0DFQ); the actual last two paragraphs of moduli.tex `lemma-pic-functor-uniqueness-part` (0DNJ); and spaces-morphisms.tex `lemma-valuative-criterion-separatedness` (03KV). I checked that 0DNJ's extracted line-module proof uses a proper flat finitely presented space with integral geometric fibres and a generically trivial L, and not a pre-existing Picard space or a section. It uses both L and its dual to obtain nonzero special-fibre sections, then a rank-one H0 complex over the valuation ring. This is genuine mathematical content left in a smaller statement node, not the item's separatedness clause moved elsewhere. The unpointed representability node also has genuinely different hypotheses and an object needing identification before it proves the item.

Step 1 uses exactly the new geometric-H0 and unpointed-representability statements, and the existing `lem-sfb-space-flat-proper-fp-locality` for the property conventions and base-change permanence. Geometric integrality implies nonempty reduced connected fibres, so all H0 hypotheses hold. The canonical H0 map is exactly the assumption of the unpointed theorem. No cited scheme-only theorem is applied to a space.

Step 2 uses the H0 statement and the two existing definitions of a space line module and a scheme invertible module. Its only calculations are local scalar endomorphisms, gluing those scalar functions, and the evaluation trivialization of M tensor the inverse pullback of e*M. On overlaps a change of frame conjugates a scalar by a unit and does not alter it. The section recovers the base scalar, proving triviality of rigidified automorphisms. This is elementary relative to those statements and definitions; no separate generic automorphism theorem is hidden in it.

Step 3 now uses the full statement of the existing `lem-sfb-space-fppf-qcoh-descent`, and the existing `lem-sfb-space-fppf-covering-calculus` for its pullback cover. The line modules are quasi-coherent directly from their local rank-one presentations, using `def-trf-space-quasi-coherent-module`. The new `lem-sfb-space-fppf-invertible-locality` is applied only after effective descent has supplied a quasi-coherent object. Thus no rank-one property is silently inferred from an equivalence that only states quasi-coherent descent. The cocycle follows from uniqueness established in Step 2, not from an arbitrary unnormalized choice of overlap isomorphisms. Descent of r and its inverse uses full faithfulness on the base T as well. Normalizing a base twist kills it by evaluation; a base line module is locally trivial, so its image is zero in the sheafification. This proves both composites of the normalization/forgetful maps are identity. The group and zero assertions are checked on actual tensor products and the trivial rigidified module. The existing space definition supplies the fppf sheaf meaning, not representability by itself.

Step 4 uses the new valuation-line statement and the new space valuative criterion. It explicitly applies the already-read property-locality statement to the valuation-ring base change, and geometric fibres remain integral there. No restriction to DVRs or Noetherian valuation rings occurs. The generic equality gives triviality of the tensor difference; an unrigidified trivialization is corrected by its base unit at the section. The criterion has precisely the quasi-compact diagonal furnished in Step 1. Therefore each hypothesis taken from a cited node is literally in that node's statement.

Step 5 uses the existing quasi-coherent descent equivalence, the new invertibility-locality statement, the existing fppf covering calculus, the quasi-coherence and space definitions, and `lem-trf-space-fibre-products-etale-covers`. The latter supplies an actual space fibre product and stability of a surjective etale atlas under arbitrary pullback; the space definition makes the atlas overlaps schemes. One cannot cite the older etale-by-schemes line-descent node here for X_U to X_T, since X_U can remain a space, which is why the existing fppf quasi-coherent descent theorem is used, followed by the new invertibility-locality theorem. Maps into P glue because its underlying functor is an fppf, hence etale, sheaf. Applying the constructed inverse classification to id_P gives the universal module, and both the rigidification and its uniqueness descend. There is no assumption that P or X is a scheme.

Step 6 is elementary reuse of the proved natural classification: an S_1-scheme has the same X-fibre product, section and rigidification whether viewed over S or S_1. Its Hom functor is therefore represented by the base change of P. The universal class is id on each side; the rigidified isomorphism is unique. This also proves identity and composition compatibilities and the geometric-fibre clause. The proof never re-applies a locally-Noetherian-only theorem over an arbitrary non-Noetherian base.

Small cases checked: S empty gives empty total and parameter spaces and the unique empty family. For X=S the normalized functor is the one-element functor, so P=S and all scalar corrections have the right sign. For projective space over a field the full Picard space has components indexed by degree; the proof asserts local finite presentation and separatedness, not quasi-compactness or properness of the entire Picard space. Reduced disconnected fibres would give extra functions and are correctly excluded from H0. I checked topology.tex `definition-connected-components`: Stacks explicitly excludes the empty space from connected spaces; the H0 node now says this to avoid an empty-fibre ambiguity. A field is permitted as a valuation ring in both new valuative statements, and then the generic-triviality premise is already the conclusion. High-rank valuation rings are allowed. The reused covering calculus permits empty covers only over the empty base; invertibility locality on that base is vacuous and valid. The space separatedness criterion retains quasi-separatedness; no conclusion is drawn from valuative uniqueness alone without it.

Corrections made during this reading: replaced an informal topological-image description of fpqc covering with Stacks' affine-test refinement definition, included the explicit covering stability facts needed to use descent, and added the existing base-change and fibre-product citations instead of leaving those steps implicit. Added the existing canonical module-functor definition to statement dependencies. The item's statement is untouched. Every new node has an independent statement with no proof sketch or proof dependencies, inline explanations of its space-level properties, and sources by tag and TeX label. The source and blueprint searches above rule out duplicates and scheme-only specializations. No new node merely states the rigidified classification, universal family, scalar calculation or base-change clause: these are proved in the six steps. All six steps are below 2,000 characters. The literal quotes in citations.json were regenerated after all corrections and checked against the actual cited statement strings. The first dry run then located the newer `lem-sfb-space-fppf-qcoh-descent` (04W8). I opened it, removed the broad effective-line-descent draft, reused that equivalence and its fppf covering calculus, and retained only the genuinely absent rank-one reflection lemma as a new node. I ran fresh searches for that narrower statement; all earlier queries remain logged. The new statements still have no proofs. The new invertibility statement requires quasi-coherence explicitly, exactly as 060X does, and the proof establishes that hypothesis by local free presentations before applying it.

## Unfinished work

No part of this stage-1 split is left unfinished. The five deliberately unsplit prerequisite nodes are the next stage-1 items; none is represented as already proved or as a Mathlib leaf. The first server review_split passed. The first delivery dry run stopped at the duplicate gate and pushed nothing; that diagnostic has been repaired as described above. The final required dry run and push follow this report.
