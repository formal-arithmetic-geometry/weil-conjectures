# Stage-1 report: lem-trf-geometric-reducedness-algebraic-closure-test

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-algebraic-closure-test.json: split item; no exact project declaration found.
- dag/nodes/sec-trace-formula/lem-trf-affine-geometric-reducedness-criterion.json: Mathlib leaf, exact match Algebra.isGeometricallyReduced_iff.
- dag/nodes/sec-trace-formula/lem-trf-reduced-scheme-open-cover.json: Mathlib leaf, exact match AlgebraicGeometry.IsReduced.iff_of_openCover.
- dag/nodes/sec-trace-formula/lem-trf-reducedness-tensor-chosen-algebraic-closure.json: statement-only supporting node; no exact Mathlib match.
- citations.json: verbatim citations for every non-elementary item step.

## Attachments

No attachments. A grep of the project source found no declaration tagged (blueprint: lem-trf-geometric-reducedness-algebraic-closure-test) and no declaration stating the item exactly.

## WANTED

None.

## Not duplicates

- lem-trf-affine-geometric-reducedness-criterion vs lem-trf-geometric-reducedness-finite-inseparable-test: the new node uses Mathlib’s canonical algebraic closure criterion for arbitrary algebras; the existing node uses finite purely inseparable extensions and is a Stacks theorem.
- lem-trf-reducedness-tensor-chosen-algebraic-closure vs lem-pc-algebraic-closure-exists-unique: the existing node states existence and uniqueness of algebraic closures; the new node states invariance of reducedness of a tensor product under replacing one closure by another.
- lem-trf-reduced-scheme-open-cover vs def-pc-reduced-scheme: the definition gives the local-ring/section characterization of reducedness; the new Mathlib leaf gives the iff for an arbitrary open cover.

## What was checked

I read the item, its chapter and unit records, the imported Stacks source literature/stacks-project/varieties.tex, and the relevant Mathlib files. The statement matches Tag 035X’s all-field-extension and algebraic-closure clauses, with no finite-type or nonemptiness assumptions; the empty scheme remains included.

Step 1 is the direct specialization of the all-field-extension condition to the chosen algebraic closure. Step 2 uses the canonical affine open cover, base change of opens, the existing affine fibre-product spectrum theorem, the existing affine reducedness criterion, and the new open-cover Mathlib leaf; each cited statement supplies exactly those facts. Step 3 first uses the chosen-versus-canonical algebraic-closure tensor node, whose proof is the tensor transport induced by the algebraic-closure isomorphism from Tag 09GV, and then applies the exact Mathlib criterion Algebra.isGeometricallyReduced_iff. Step 4 applies the same chart argument to an arbitrary field extension and glues reduced affine charts using the open-cover leaf. I checked hypotheses at each use: the chart rings are commutative algebras over the field, every field extension is allowed, and no finite generation or nonemptiness is introduced.

I tested the edge cases conceptually: the empty scheme has an empty affine cover and is reduced after every base change; a reduced affine scheme over a perfect field satisfies the criterion; and an imperfect-field example such as k[u]/(u^p-a) with a not a pth power fails exactly when its algebraic-closure base change is nonreduced. The Mathlib searches were rerun with each new node’s own id and recorded in the node files and searches.jsonl.

## Review by Q20

I compared every step with the cited source and opened each cited node. Step 2’s open-cover, affine-spectrum, and affine-reducedness citations state precisely the cover reduction, tensor-product chart, and ring/scheme reducedness equivalence used. Step 3’s chosen-closure node states exactly the closure-independence assertion needed before invoking the Mathlib affine criterion; its only dependency, lem-pc-algebraic-closure-exists-unique, supplies uniqueness over the base field. Step 4 repeats the same three chart facts for arbitrary L/k. I corrected the imported item’s unspecified blueprint location, added the complete proof and dependency union, and fixed a missing closing math delimiter in Step 3. No statement hypotheses were added or removed.

- lem-trf-affine-geometric-reducedness-criterion vs lem-trf-geometric-reducedness-algebraic-closure-test: the new node is the affine commutative-algebra criterion over Mathlib's canonical closure; the existing node is the scheme-level arbitrary chosen-closure statement.
- lem-trf-affine-geometric-reducedness-criterion vs lem-trf-geometric-reduced-fibre-locus-base-change: the new node concerns one algebra and all field extensions; the existing node concerns equality of geometric-fibre loci under arbitrary base change.
- lem-trf-affine-geometric-reducedness-criterion vs lem-trf-geometric-reduced-fibre-locus-constructible: the new node is an affine tensor criterion with no morphism hypotheses; the existing node is constructibility for quasi-compact locally finitely presented morphisms.
- lem-trf-reduced-scheme-open-cover vs lem-coef-infinity-blunt-join-comparison: the shared Stacks tag text is only a tag-number collision; the new node is the scheme reducedness open-cover criterion, while the existing node is a simplicial blunt-join categorical-equivalence statement.
