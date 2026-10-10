# Stage 1 report: lem-sc-finite-surjective-dimension

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sc-finite-surjective-dimension.json`: statement, Mathlib leaf.
- `citations.json`: empty, because the item has no natural-language proof steps after the Mathlib match.

## Attachments

No existing project declaration carries the blueprint tag or the exact full statement.

## WANTED

None.

## What was checked

The target node and its source route were read in full. The source statement is unchanged. The slopmaster2 source has no declaration tagged `(blueprint: lem-sc-finite-surjective-dimension)`, but its project Mathlib extensions contain `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_surjective` (in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`, lines 63--68), which proves equality for universally closed, locally quasi-finite, surjective morphisms. A finite morphism has the first two properties, so this applies to the given finite surjective `f`. The same source contains `AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace` (in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`, lines 193--195); finite type over a field makes each nonempty scheme quasi-compact and hence compact, giving finite dimensions for both `X` and `Y`.

I checked the declarations and hypotheses directly, searched the existing DAG and blueprint references for duplicate nodes, and ran the mandated LeanSearch, LeanFinder, Loogle, and grep searches. LeanSearch was unavailable; Loogle did not recognize the project extension name; the Mathlib-package grep had no hit because the declarations are in the project's `WeilConjectures/Mathlib` extension. These outcomes are recorded verbatim enough in `mathlib_searches`. Since the item is a Mathlib leaf, there are no proof steps or cited-node quotes to audit, so `citations.json` is empty. Small cases checked: `X = Y = Spec k` and a finite closed subscheme map; both satisfy the stated finite equality conclusion.

## Review by G1

I verified that the finite hypothesis supplies the universally closed and locally quasi-finite instances required by the equality theorem, and that finite type over the field supplies the compactness and locally finite type hypotheses required by the finite-dimension theorem. I verified that nonemptiness is sufficient for the finite-type compactness argument and that the conclusion is exactly the original conjunction of finite dimensions and equality. I also checked that no existing DAG node states this same scheme-theoretic result and that no source declaration with the blueprint tag is an attachment. The only correction to the imported node was its classification: it is a Mathlib leaf, with the two declarations and their source lines recorded in `mathlib_match`; no statement, dependency, or blueprint field was changed.

## Second reading by G1

- Item statement: checked against Stacks Algebra tags 00OK (lemma-integral-sub-dim-equal) and 00OY (lemma-Noether-normalization), and against the project declarations; hypotheses and the finite-equal-finite-dimensional conclusion agree.
- Proof steps: none; the node is a Mathlib leaf, so there are no uncited natural-language steps to audit.
- New node `lem-sc-finite-surjective-dimension`: checked B1-B7; statement is self-contained with definition dependencies, TeX formatting, blueprint ancestry, and source tags/labels. The declaration match was checked at `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean:63-68` and `FiniteType.lean:193-195`.
- Existing-node and blueprint searches: `blueprint_refs.py search` found no duplicate blueprint node; DAG search found no existing statement of this scheme result. The recorded semantic and source searches were rerun with `msearch.py` and their outcomes remain in `searches.jsonl`.
- Small cases: `X=Y=Spec(k)`, a finite closed subscheme map, and dimensions zero and one all satisfy the statement; nonemptiness excludes the empty-scheme edge case as stated.

Changes made: corrected the `mathlib_match.file` paths to include the project `WeilConjectures/Mathlib` prefix and made `how` name the exact instances, declarations, and source lines used. No mathematical statement or dependency was changed.
