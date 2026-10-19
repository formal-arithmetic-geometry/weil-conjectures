1. Files written:
- `dag/nodes/sec-trace-formula/lem-trf-relative-flatness-source-cover.json` — item, split; no Mathlib exact match.
- `dag/nodes/sec-trace-formula/lem-trf-flatness-faithfully-flat-extension.json` — new statement-only helper; no Mathlib exact match (same-base tensor criteria are only general ingredients).
- `citations.json` and this report.

2. Attachments:
- `AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_stalk_iso` belongs to `lem-weil-pbc-module-stalk-pullback`.

3. WANTED:

4. What I checked and corrected:
The imported item is the Stacks Project Morphisms Tag 02JZ lemma-flat-permanence, including its pointwise and jointly-surjective-family clauses. I read the complete source proof in `literature/stacks-project/morphisms.tex` and the blueprint ancestor `lem-trf-local-term-locality`. The source's local-ring argument requires that a flat local stalk map be faithfully flat and that the pullback stalk be the tensor product of the original stalk with the target local ring. Those are supplied by `lem-pc-local-flat-faithful-flat-reflects-surjective` and `lem-weil-pbc-module-stalk-pullback`; I read both statements in full and checked the local and flat hypotheses. The remaining algebra is isolated as `lem-trf-flatness-faithfully-flat-extension`: for A→B→C with C faithfully flat over B, A-flatness of a B-module is equivalent to A-flatness after C⊗_B−. This is exactly the kernel/tensor argument in Tag 02JZ and is not a duplicate in the DAG. Step 2 uses its exact statement and transports along the cited stalk isomorphism. Step 3 uses joint surjectivity pointwise in both directions and then the existing `lem-pc-relative-flat-of-stalks` criterion to pass between all stalks and affine-local relative flatness. I checked empty schemes, the identity/empty family cases, zero modules, and identity or faithfully flat field extensions. I ran the required Mathlib searches for both the item and the new helper; Mathlib provides only same-base faithfully-flat tensor criteria, so neither is a Mathlib leaf.

## Review by Q91

I checked the source and dependency statements as described above. In Step 1, `lem-pc-local-flat-faithful-flat-reflects-surjective` supplies faithful flatness from the flat local stalk map, and `lem-weil-pbc-module-stalk-pullback` supplies the exact tensor stalk identification; I verified both hypotheses and the composite structure-map action. Step 2 uses the new helper verbatim and the same stalk identification. Step 3 uses joint surjectivity to choose preimages pointwise and `lem-pc-relative-flat-of-stalks` for the all-stalks/global equivalence; its quasi-coherence hypothesis is the item hypothesis. I checked the identity, empty-family, zero-module, and field-extension edge cases. The helper is intentionally statement-only because the intermediate-ring tensor descent argument is a separate non-elementary lemma for a later stage.

## Not duplicates
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-pc-relative-flat-of-stalks`: the new node is a ring-theoretic intermediate faithfully-flat tensor equivalence; the existing node is a scheme-level stalkwise-to-affine-sections criterion.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-pc-relative-flat-module-stalk`: the new node concerns descent along C faithfully flat over B; the existing node derives stalk flatness from affine section flatness.
- `lem-trf-relative-flatness-source-cover` vs `lem-pc-relatively-flat-module-pullback`: the item is pointwise detection under source-cover maps for one module on Y; the existing node is base change of relative flatness along an arbitrary square.

- `lem-trf-flatness-faithfully-flat-extension` vs `lem-trf-relative-flatness-source-cover`: the helper is a ring-level tensor descent lemma used in the pointwise proof; the item is the scheme-level source-cover equivalence.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-pc-field-extension-flat`: the existing node treats only flatness of a field-extension structure morphism; the helper compares module flatness over an intermediate ring.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-pc-field-extension-fpqc-cover`: the existing node is the geometric fpqc cover from a field extension; the helper is module flatness descent along an arbitrary faithfully flat intermediate algebra.
- `lem-trf-flatness-faithfully-flat-extension` vs `def-weil-pbc-faithfully-flat-ring-map`: the existing node is a definition of faithful flatness; the helper is a derived equivalence for module flatness.
- `lem-trf-flatness-faithfully-flat-extension` vs `def-weil-pbc-flat-ring-map`: the existing node defines flatness; the helper proves a three-ring tensor criterion.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-weil-pbc-field-extension-base-change-faithfully-flat`: the existing node covers faithfully flat field scalar base change; the helper allows arbitrary A→B→C and a B-module.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-weil-pbc-finite-product-flat-modules`: the existing node proves finite products preserve flatness; the helper detects flatness after faithful tensor extension.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-weil-pbc-flat-tensor-exact`: the existing node is preservation of exactness by a flat tensor; the helper is an iff reflecting flatness through faithful flatness.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-weil-cohomology-commutes-scalar-extension`: the existing node concerns cohomology of complexes over field extensions; the helper concerns ordinary module flatness over a base ring.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-weil-pbc-finite-projective-descends-flat-local`: the existing node descends finite projectivity for finitely generated modules over local rings; the helper has no finiteness or projectivity assumptions and compares flatness over A.
- `lem-trf-flatness-faithfully-flat-extension` vs `lem-weil-pbc-flat-local-hom-faithfully-flat`: the existing node proves a flat local homomorphism is faithfully flat; the helper assumes faithful flatness and derives the module flatness equivalence.

5. What I could not finish:
No Lean proof was written or compiled, as required for stage 1. The helper remains statement-only for a later splitter.
