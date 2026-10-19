# def-trf-projective-bundle-morphism

## Files written

- `dag/nodes/sec-trace-formula/def-trf-projective-bundle-morphism.json`: definition; split with existing notions, no Mathlib match, no new nodes.
- `citations.json`: empty list, because this definition has no proof steps.
- `report.md`: this report. The search command maintains `searches.jsonl`.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item tag, projective-bundle/projective-morphism terminology and `IsProjective`. The only relevant comment, `Blowup/Affine/Projective.lean:49`, explicitly says scheme projectivity has not been formalized there. Its affine blowup embedding declarations do not define this predicate for arbitrary schemes. The master source was read only as reference material.

## WANTED

None. All necessary sources are present.

## Findings and changes

The definition agrees with Stacks 01W8(1); there is no statement dispute. Preserved its projective-bundle convention, including finite-type quasi-coherence without a local-freeness assumption. Added the statement dependency `def-kun-projective` that the unchanged concluding convention comparison already cited. Made the existing scheme citation explicit and supplied the projective-bundle source tag 01OB. Filled the blueprint place with its precise role in the alteration branch below local-term locality, retaining the ancestor and via list. No chapter or unit record changed.

The item has no Lean audit field and no exact project declaration was found. Mathlib searches were run through the prescribed command, and their actual results are appended after all inherited search records. Both semantic phrasings were tried; LeanFinder and Loogle return absolute graded-ring Proj, LeanSearch returns closed immersions, and the scoped source search returns no projective-bundle predicate. Reading `ProjectiveSpectrum/Scheme.lean:855`, `Morphisms/Proper.lean:42` and `Morphisms/ClosedImmersion.lean:45` confirms these are respectively absolute Proj, properness and closed immersions, not this relative projectivity predicate. LinearAlgebra.Projectivization hits concern vector-space lines, not schemes or quasi-coherent modules.

## Not duplicates

No new nodes. The existing item is not identified with `def-kun-projective` or `def-pc-projective-morphism`: their statements require a closed immersion into one finite projective space over the base, whereas this item permits an arbitrary finite-type quasi-coherent module. The vector-bundle projectivizations in `lem-pur-projective-bundle-tautological-geometry` and `lem-amb-vector-projective-completion` have local-freeness hypotheses and assert additional geometry; neither defines the predicate here. Searched the whole DAG for projective-bundle terminology, 01W8 and 01OB and ran blueprint_refs search for both `projective bundle` and `projective`. There is no same-statement blueprint node, so same_as is empty.

## Review by ND

I read Stacks morphisms.tex, Definition 01W8 (morphisms-definition-projective), clauses (1) and (2), and constructions.tex, Definition 01OB (constructions-definition-projective-bundle) with its preceding paragraph. Clause (1) requires exactly a closed subscheme over S of P(E) for a quasi-coherent finite-type module. Definition 01OB makes P(E) the relative Proj of Sym(E), and its footnote explicitly declines to impose finite local freeness. Thus no Noetherian, quasi-compact-base, locally-free or constant-rank hypothesis is imported. The words “over S” retain the compatibility with the prescribed structure morphism f.

This is a definition, so there are no proof steps, elementary judgments, proof-step quotations, off-unit theorem applications or long steps to audit. Instead I opened every statement dependency and checked its defining content. `def-pc-scheme` supplies schemes and their morphisms. `def-weil-closed-immersion` supplies closed immersions/closed subschemes. `pqf-def-coherent` explicitly supplies both quasi-coherence and finite type (its first two clauses); it does not force coherence. `lem-weil-pbc-quasi-coherent-symmetric-algebra` gives the symmetric algebra sheaf, its quasi-coherence, its universal property and its affine sections. `lem-weil-pbc-symmetric-algebra-graded` supplies the grading by symmetric degree on those affine algebras. `def-nagata-relative-proj` supplies the relative construction and its structural map for a quasi-coherent graded algebra. Finally `def-kun-projective` defines exactly the finite-projective-space convention referenced only for comparison. Reading Modules 01CF, 01CG and 01CL also confirms the sheaf symmetric algebra and its degree grading and quasi-coherence used in the source's preceding paragraph. No theorem asserting a comparison between the two projectivity conventions is silently used.

I checked the small cases directly: E=0 gives the empty relative Proj and permits the empty scheme over S; E=O_S gives P(E)=S and includes closed immersions; E locally free of rank n+1 recovers the usual projective-space examples. Non-locally-free finite-type modules are still allowed, as required by 01OB. On an empty base the only source scheme is empty, so the predicate has no exceptional undefined case. No claim that finite-type modules have a globally fixed number of generators is made, and no equality with the H-projective convention is asserted. These checks found only the missing dependency and imprecise source place corrected above; no helper statement, proof or hypothesis needed repair. The B--E checklist produces no new-node issues, omitted proof citations, relabelling, circular proof, or statement error.

## Unfinished work

None for this one-level definition split. Its existing dependencies retain their own independent stage status.
