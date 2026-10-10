Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-integral-univclosed.json`: statement, Mathlib searches, exact Mathlib match; no new nodes.

Attachments:

- `AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom` is the exact Mathlib declaration for this item.

WANTED:

- None.

What was wrong or changed:

- The imported node was unsplit and carried an incomplete blueprint proof, including an expressly un-decomposed converse. The pinned Mathlib source already states the complete equivalence, so I converted the item to a Mathlib leaf and removed its proof dependencies.
- No project declaration in `WeilConjectures/` carries the blueprint tag or states this equivalence.

What could not be finished:

- Nothing.

## Review by M1

I read the item node, the `sk-prop-av-pqf-finite` unit, the `sec-abelian-varieties` chapter record, and the imported blueprint proof. I checked the source declaration in `Mathlib/AlgebraicGeometry/Morphisms/Integral.lean`: line 135 states `IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f`, exactly the integral iff affine and universally closed assertion after expanding the project conventions. The declaration has no additional hypotheses beyond a scheme morphism. Since this is a direct Mathlib match, there are no proof steps, cited DAG statements, or citation quotes to validate, and no new node requires duplicate or small-case review. I also searched the project source for the blueprint tag and relevant `IsIntegralHom` names; no project declaration states the item. LeanFinder and Loogle returned the exact declaration; LeanSearch was unavailable and the required grep invocation returned no hit, both recorded verbatim in `mathlib_searches`.

## Second reading by M1

- Item statement: checked against Stacks Morphisms, Lemma 29.45.7, Tag 01WM; all hypotheses are exactly a scheme morphism, and the two conclusions are integral iff affine and universally closed.
- Proof steps: none; the Mathlib leaf declaration supplies the complete equivalence, so there are no uncited dependencies or elementary-step claims.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous for this leaf.
- Mathlib leaf: checked `/home/ubuntu/weil-src-slopmaster2/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Integral.lean:135`; `IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f` is the exact statement up to conjunction order and terminology.
- Edge cases: the statement is uniform for the zero/empty schemes, fields, and identity morphisms; no extra nonemptiness, finiteness, or presentation hypothesis is present.

Changes made: filled `blueprint.from` with the item statement place and retained the complete Mathlib-leaf conversion; no mathematical statement or proof content needed repair.
