# Stage-1 worker report: lem-weil-pbc-realization-scalar-functor

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-realization-scalar-functor.json: existing statement node split in six steps; no Mathlib match for the whole statement.
- citations.json: 16 step/node entries containing verbatim statement excerpts.
- searches.jsonl: six actual searches recorded by msearch.py; their exact queries and returned summaries are appended to the item's existing search history. The earlier N9 searches were retained unchanged.

There are zero new nodes and zero new Mathlib leaves. The source extract and preparation script are sandbox-only working files.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and the scalar-functor, realization, integralScalarExtension and continuous-coefficient terminology found no declaration giving this whole statement. The field-to-field scalar extensions in SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean are a different coefficient change; neither those nor their partial constructibility results attach this integral-to-field statement. No compiler was run.

## WANTED

None. The sources used below are present in literature/.

## What was wrong and what changed

The imported item was a statement-only obligation, correctly distinguishing the raw integral rationalization from the archived continuous coefficient category. Its statement is unchanged, including the explicitly fixed canonical ring map, all scheme and coefficient hypotheses, the ambient adjunction and unit normalization, and the absence of full-faithfulness or essential-surjectivity claims. No statement dispute was found.

The earlier N9 helper argument suggested proving exactness by a filtered-colimit calculation and using the lfp-to-locally-free bridge. The live DAG now contains lem-weil-pbc-scalar-localization-sheaf-exact, which supplies the former directly. The existing bounded-constructible-exact-scalar-extension node supplies preservation in the archived lfp sense. Thus neither a new telescope lemma nor any local-freeness theorem is needed here. I used the integral characterization's condition (iii), not an identification with a constant-coefficient or merely mod-varpi category. I supplied the fraction relation calculation explicitly, including eventual varpi-torsion in Hom modules, and used the normalized general sheaf-ring adjunction to fix the actual unit.

The chapter and unit records were read, including the three steps of sk-thm-properbasechange. This is a coefficient-support obligation beneath thm-weil-pbc-finite-extension, not the unit's key node: no unit record is changed. The current main-20261015 finite-extension proof says to choose an integral lattice and rationalize; these six steps supply the actual scalar functor used in that passage and do not replace the geometric proper-base-change route.

## Searches and reuse

I searched the whole DAG for scalar localization, exact restriction/extension and derived adjunction, and the whole imported blueprint using tools/blueprint_refs.py (ancestor and searches for pbc realization scalar functor, scalar extension, restriction scalars, localization, scalar localization sheaf, sheaf ring derived coefficient adjunction and integral stratified perfect). The nearest ancestor is thm-weil-pbc-finite-extension; its existing from.place and via fields were already precise and were retained. No blueprint node states this exact combined functor-construction obligation, so same_as remains empty.

Mathlib searches used only the prescribed msearch.py command. LeanFinder and LeanSearch returned generic derived linearity, ordinary module adjunctions/localizations, profinite cohomology and condensed abelian-category infrastructure, not the specified constructible comparison. Loogle's two actual queries were '"Localization", "linear"' and '"Functor.IsLocalization", "linear"'; the former returned ordinary localized-module linear maps, the latter no hits. The source grep for boundedConstructible, integralScalarExtension and continuous-coefficient localization returned no hits. I read the ModuleCat.ChangeOfRings source to check the ordinary module adjunction candidate: it has rings and ordinary modules, not pro-etale ring sheaves, integral constructibility and the specified raw fraction functor. The second LeanFinder phrasing returned generic DerivedCategory linearity and localCohomology. Those are ingredients, not an exact or one-line specialization of this item. The full returned summaries are preserved in the search log and node.

No new node was created before a search or in place of a reusable node. The existing lem-weil-pbc-bounded-constructible-exact-scalar-extension, lem-sfb-extend-scalars-bounded-constructible and thm-sfb-extend-scalars-localization were opened and compared. The first is used precisely for its preservation assertion; the latter two do not replace the raw-category construction and normalized unit.

## Not duplicates

No new nodes. Every support fact is an existing citation. In particular, the elementary verification of the fraction functor is a proof step, not a new node restating a clause of this item.

## Review by Q51

I read Bhatt--Scholze, the local PDF text of Definition 6.8.1 and Lemma 6.8.2, Definition 6.8.10 and Proposition 6.8.11(3), and Proposition 6.8.14(2) with its proof. The last proposition concerns an equivalence for the source's constructible categories; I take only its scalar-extension/rationalization route, and cite the DAG's explicit integral characterization and internal-module encoding for our actual categories. I also read Stacks sites-modules.tex, label lemma-flatness-sheafification (03ET), the tensor/restriction adjunction label lemma-adjointness-tensor-restrict (03CZ), module abelianness and limits/colimits (03DA and 03DB), derived.tex label lemma-right-derived-exact-functor (015F) and proposition-construct-localization (05R6), and sites-cohomology.tex label lemma-adjoint (07A6). These supply the generic tools; there is no SGA reference. No new statement requires a separate source audit.

Step 1 cites continuous-coefficients-immersion-restriction for both A_T = lim (A/varpi^n)_T and A_T[1/varpi] = E_T, including immersion restrictions; this is in its statement. Continuous-coefficient-realizations explicitly says its comparisons intertwine a continuous ring map and that the integral-to-field square commutes. Module-encoding explicitly sends regular modules and finite sums to the indicated free sheaves. Encoding-scalar-extension explicitly compares actual internal scalar extension with sheafified sectionwise extension without freeness assumptions. I checked these four statements rather than taking a map identification from their proofs. This prevents a field automorphism from changing the intended coefficient inclusion.

Step 2 cites scalar-localization-sheaf-exact with the small site, commutative sheaf R=A_T and global section varpi; that node explicitly asserts additivity and finite-limit/colimit preservation for actual sheafified scalar localization, including a naturally isomorphic functor. Its hypotheses need neither enough points nor sectionwise surjectivity. Exact-functor-derived-factorization explicitly provides the termwise unbounded factorization and triangulated shift comparison. Exact-functor-derived-functor explicitly identifies that factorization with the total left derived functor. The cohomology formula is then the kernel/cokernel formula for an exact functor. No unjustified exactness of sections was substituted for exactness of sheaves.

Step 3 cites sheaf-ring-derived-coefficient-adjunction, whose statement explicitly permits an arbitrary small site and arbitrary commutative ring map with unbounded complexes. It states exactness of restriction, the derived Hom bijection, and the normalized unit x -> x tensor 1 on K-flat representatives. I checked the tensor symmetry changes this to 1 tensor x with E_T as first factor. Naturality along P -> K gives the asserted termwise unit for arbitrary representatives because both functors here are exact. This is an ambient adjunction: its right adjoint need not land in the integral constructible category, and no such claim is made. The off-unit citation is a generic normalized change-of-rings tool and is declared in split_report.tool_uses.

Step 4 uses exactly condition (iii) and the hypotheses of integral-stratified-perfect-characterization: T is Noetherian, finite dimensional, and ell is invertible, all explicitly present in the item. The condition gives bounded cohomology and finite stratified local A_T tensor N models with N finitely presented over A. A finite presentation of N tensored with A_Z is a finite free presentation by the tensor universal property; no flatness of N is presumed. Immersion-restriction supplies the coefficient rings on strata. The encoding's regular/free-module clause and equivalence transfer the cokernel presentation, a universal-property argument. Thus the hypotheses of bounded-constructible-exact-scalar-extension are met in the internal category: its statement asks for finite-limit preservation and uses exactly the archived stratified local-finite-presentation definition. Step 2 supplies finite-limit preservation. This citation does not quietly replace the definition with lisse sheaves or add a completeness condition to the E-side.

Step 5 cites the raw category and linear scalar-localization definitions for the Hom modules, composition and identities. Everything else is the displayed algebra calculation. In particular, equality of fractions allows multiplication by a further varpi power before the numerators agree; I included that power, so torsion in Hom modules is allowed. Varpi acts invertibly in E_T, hence its cancellation is legitimate even if the source has torsion. The balancing equality supplies A-linearity of tensoring and then E-linearity on localized Hom modules. This step is marked elementary and does not hide a lemma.

Step 6 uses the integral characterization's explicit shift/cone closure and the triangulated scalar-localization node's explicit description of distinguished triangles as images of integral triangles up to isomorphism. Thus exactness is tested on triangles whose images are known from steps 2 and 4. Naturality of the shift comparison extends to fractions by the same scalar formula of step 5. The generic raw-localization theorem is declared as a tool use, with no assumption of a Karoubi envelope or categorical equivalence.

I checked every citation's statement with its step open and generated the 16 citations.json entries from those actual statements. I checked dependency closure for every nontrivial supporting theorem: none reaches this item, so no citation creates a cycle. Every proof step is below 2000 characters (971, 874, 876, 1411, 923 and 798 characters). The statement and its definition dependencies were retained. There are no unsplit helper proofs hidden in a new node, no new undefined objects, no fictitious Mathlib search, and no declaration attached on the strength of a sorry.

The small cases checked are the empty scheme and zero complex (all images, presentations and units are zero); a complex killed by varpi (scalar image is zero and every eventual-torsion fraction relation maps to zero); the regular coefficient complex A_T in degree zero (its image is E_T and its unit is the specified coefficient inclusion); an arbitrary shift (the comparison is the termwise one); and finite free rank zero presentations. Ramification does not require changing from ell to varpi: the item uses varpi throughout and the coefficient-localization lemma states exactly A_T[1/varpi] = E_T. None of the proof uses properness, an algebraically closed or finite base field, or excluded negative cohomological degrees.

## What could not be finished

Nothing remains for this one-level split. Existing cited nodes retain their own proof status and are not newly split or claimed proved by this delivery.

## Validation

The server review_split check passed with zero new nodes before packaging. Full dry run and delivery follow using the prescribed deliver.py command.
