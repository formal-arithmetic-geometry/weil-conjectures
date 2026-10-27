# Stage-1 report: lem-trf-resolution-colimit-quasi-isos

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-resolution-colimit-quasi-isos.json`: item split in five steps; not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation per step/node citation.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. Existing results suffice, so no auxiliary statement-only node is needed.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` for the exact blueprint id and for resolving/resolution-colimit terminology. No project declaration states the whole item. `HomologicalComplex.instPreservesColimitsOfShapeHomologyFunctorOfHasExactColimitsOfShape_weilConjectures` in `WeilConjectures/CategoryTheory/DerivedCategory/DegreewiseLimits.lean` belongs to the existing `src-weil-homology-preserves-exact-colimits`; it supplies just the cohomology-colimit interchange, not this item. The existing roof-comparison node also supplies only one ingredient.

## WANTED

None. All sources used are available locally.

## What needed work

The item was statement-only, with no earlier sandbox split or report. Its statement is unchanged. In particular, no right-exactness assumption was added, and exactness of sequential colimits is required only in the target category. Although the surrounding Stacks proposition assumes more, its cone-and-comparison claim uses only the hypotheses retained in this item.

The source diagram in Tag 0794 reverses the arrow relative to its preceding declaration of alpha. The existing bounded-stage comparison statement already has the consistent direction X to Y. The present proof follows that statement and explicitly checks both comparison identities. This is a correction of a source display in the proof, not a statement dispute or a change to this item's statement.

The crucial missing argument would have been to treat alpha as a map of towers. Step 3 instead uses the existing roof comparison, whose statement explicitly allows arbitrary alpha and gives both stage naturality and compatibility with the augmentations. Step 5 writes down the inverse after passage to colimits, ensuring that the resulting isomorphism is H^i(F(alpha)) itself.

## Sources and searches

Read `literature/stacks-project/derived.tex`, Tag 0794 (`proposition-left-derived-exists`), including the first-paragraph cone argument, the claim, the common-roof comparison and the last cohomology-colimit calculation. Read Tag 05RT (`lemma-acyclic`) for the cone criterion. Read the cone formula and cohomology functoriality in `def-weil-abstract-derived-category`, and the colimit universal property in `def-weil-pbc-category-colimit`. Read `lean/WeilConjectures/CategoryTheory/DerivedCategory/DegreewiseLimits.lean:76-89,142-144`, which implements the existing exact-colimit homology input.

Read the chapter and unit records, SETUP's three levels, and the latest blueprint's `sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md`. This is a generic homological supporting input along the existing ancestry; the geometric route is not replaced. The item retains its supplied precise blueprint.from.place. Whole-blueprint searches with `tools/blueprint_refs.py search 'resolution colimit quasi-isomorphism'` and `search 0794` returned zero matches. The ancestor command returns `lem-trf-local-term-locality`. Whole-DAG searches for 0794, cone-acyclic, resolving/colimit and the item id found the existing helpers used here and the parent criterion, which is not cited (avoiding a cycle).

Five actual msearch commands were run for this item: leanfinder with the original resolving-tower statement and with a second Spaltenstein/arbitrary-map phrasing, loogle with `"QuasiIso", "PreservesColimitsOfShape"`, grep with `quasiIso.*colimit|colimit.*quasiIso|map.*quasiIso` under `Algebra/Homology`, and leansearch with the direct-limit/truncation-resolution phrasing. All services answered; Loogle had no matches, the other tools returned the homology-preserving-functor family. The exact queries and returned summaries are preserved in `searches.jsonl` and appended to the item's existing searches, without altering its earlier records. Read `Mathlib/Algebra/Homology/QuasiIso.lean:247-285` and `Localization.lean:337-355`: their F.PreservesHomology hypothesis is stronger than the assumptions here. The exact-functor candidate also requires finite limits and finite colimits. No candidate is an exact match or a one-line specialization.

## Not duplicates

No new nodes. Reused `lem-pur-quasi-iso-cone-acyclic`, `lem-trf-bounded-stage-roof-comparison`, and `src-weil-homology-preserves-exact-colimits`; did not create specialized copies. The parent unbounded-left-derived criterion is neither a replacement for the present item nor an input to its proof.

## Review by Q30

I checked the five steps against the sources and the full statements of their cited nodes. For step 1, `def-weil-abstract-derived-category` states functoriality of cohomology and the complex equations. Conjugating each differential by the chosen degreewise isomorphisms gives an actual complex isomorphism, so acyclicity transfers. Choosing zero above the bound keeps bounded-aboveness even if the original class is not closed under isomorphisms. Finite biproduct closure of the isomorphism closure follows from the biproduct of two isomorphisms; the cover condition is inherited because P is contained in its closure. These are written calculations, not a new lemma or a disguised clause of the item.

For step 2, `lem-pur-quasi-iso-cone-acyclic` states exactly both implications used. `def-weil-abstract-derived-category` gives the two-term biproduct cone formula. I checked the degree shift, boundedness, zero entries and negative sign. Additivity preserves the matrix entries under the canonical biproduct identification; it needs no exactness of F. Thus the acyclic-complex assumption, rather than a hidden assumption that F preserves all quasi-isomorphisms, proves the hypothesis needed in step 3.

For step 3, I opened `lem-trf-bounded-stage-roof-comparison` and checked each hypothesis: abelian categories and the universe convention, zero and finite sums and isomorphism closure, epimorphic covers, bounded-above terms, preservation of bounded-stage quasi-isomorphisms, transition/augmentation equations, vanishing for j>n and augmentation isomorphisms for j<=n. Its statement gives exactly theta_{n+1} H(Fu_n)=H(Fv_n) theta_n and H(Fg_n) theta_n=H(Falpha) H(Fe_n). No tower morphism or colimit assumption is present in that helper. I used its statement, not any unexported construction inside its proof.

For step 4, `src-weil-homology-preserves-exact-colimits` explicitly applies to every index category and every complex shape when the category has those colimits and they are exact. I specialize it to the small positive-integer chain and to integer cochain complexes in B. F preserves the specified termwise colimit cocones; the universal-property calculation verifies they are also colimits of complexes. The resulting cohomology cocones have the actual augmentation maps as legs. A is not silently assumed to have exact colimits. `def-weil-pbc-category-colimit` supplies both the universal maps and their uniqueness.

For step 5, I checked the domains and order of composition of the inverse theta maps. Transition compatibility gives a cocone with apex H^i(FX), hence beta_i. Precomposing each of the two proposed inverse equations with every corresponding colimit leg proves it by the augmentation identity. Uniqueness in the cited colimit definition then proves both inverse equations. The cited derived-category definition says that invertibility of all cohomology maps is precisely quasi-isomorphism. This avoids assuming an unnamed cohomology comparison theorem or merely asserting that colimits preserve isomorphisms.

I checked delivery-errors B through E point by point: the statement remains self-contained and TeX is singly escaped; there are no new unsplit nodes, elementary helper nodes, duplicates, clause replacements, or unsearched nodes; every non-elementary input is a cited statement and is quoted verbatim in citations.json; proof_deps is the exact union of uses; no dependency points back through the parent; two off-unit generic tools are declared in split_report.tool_uses; no SGA source is used. All steps are shorter than 800 characters, so no step crosses the 2000-character long-step threshold.

Small cases checked: the zero functor; identity functor with alpha the identity; zero towers and P={0}; complexes concentrated in a negative degree or a degree above the first stage; bounded stages having acyclic terms above n; and tensoring abelian groups with Z/2 as a functor that need not preserve arbitrary quasi-isomorphisms. In the last case one must restrict to a class satisfying the bounded-acyclic assumption: the proof never asserts global exactness. Empty-index pitfalls do not occur because the positive integers form a nonempty small chain. No new statement or dispute needed correction.

## Unfinished work

No mathematical work remains in this split. Independent maintainer review and later formalization remain the project's subsequent work.
