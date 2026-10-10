Files written:

- `dag/nodes/sec-picard-framework/cor-pd-pic0-base-change.json`: item split; no new nodes.
- `citations.json`: verbatim quotes for the four cited statements in step 1.

Attachments: none. The matching slopmaster2 declaration `AlgebraicGeometry.nonempty_picardFunctorDegree_iso_of_isPullback` is not an attachment because its proof contains `sorry` and its conclusion is weaker than the item.

WANTED: none.

The imported item had a complete one-paragraph proof sketch but status `imported`; I changed it to `split`, filled `same_as` with the empty search result, and recorded the blueprint proof paragraph realized by the step. No new lemma node is needed: restriction preserving kernels is the elementary pointwise kernel calculation for sheaves. The imported statement and its hypotheses were retained.

## Review by G1

I read the item node and its blueprint proof paragraph, then read the source declaration and docstring at `WeilConjectures/AlgebraicGeometry/Picard/Jacobian.lean:1060-1070`. That declaration is explicitly tagged with this blueprint id, but still has `sorry`; moreover it states only existence of an isomorphism for a degree component, whereas the item states the canonical degree-zero identification, so I did not attach it. I checked the item hypotheses against the stated smooth projective geometrically integral curve and field extension.

Step 1 uses `lem-pd-picard-base-change` for restriction of the Picard functor to the field-extension slice, and that node states exactly the restricted functor is the Picard functor of the base-changed scheme. It uses `def-pc-base-change` to identify the slice base change with the displayed fibre product. It uses `def-pd-degree-morphism`, whose statement defines `Pic^0` as the kernel of the degree morphism. Finally, it uses clause (3) of `lem-pd-degree-locally-constant`, which states that fibrewise degree pulls back by composition, giving compatibility of the degree morphism with restriction. The remaining assertion that the kernel of a sheaf morphism restricts to the kernel of the restricted morphism is elementary: kernels are computed objectwise, and the slice has the same objects and arrows over the extension field. This yields the displayed isomorphism. The quotes in `citations.json` were copied verbatim from the four node statements.

I also checked the source and DAG for an existing node about restriction preserving kernels or this exact corollary; none was needed or found. No statement, dependency, or source hypothesis was changed, and no new node was created.

## Second reading by G1

- Item statement: checked against the blueprint corollary `cor-pd-pic0-base-change` and the corresponding Picard base-change context; the hypotheses (field, smooth projective geometrically integral curve, field extension) and the displayed degree-zero base-change isomorphism agree, including the zero-degree kernel interpretation.
- Step 1: checked `[lem-pd-picard-base-change]` for equality of the restricted Picard functor, `[def-pc-base-change]` for the fibre-product meaning of base change, `[def-pd-degree-morphism]` for `Pic^0` as the degree kernel, and clause (3) of `[lem-pd-degree-locally-constant]` for pointwise degree compatibility. The remaining kernel restriction claim is elementary from objectwise sheaf kernels on the slice. No unsupported use of a cited proof was found.
- New nodes: none; therefore B1-B7, duplicate checks, source tags, and Mathlib-leaf searches are vacuous. The cited existing nodes were searched in the DAG and their statements match the uses verbatim in `citations.json`.
- Edge cases: the zero sheaf/kernel gives the zero degree component; for `k'=k` the restriction is the identity; for a field extension the slice objects and fibrewise degree pullback are defined, so no empty-scheme or dimension assumption is introduced.
- Changes: none to statements or dependencies. Added this second-reading section only; the dry run of `deliver.py --no-push` passed.
