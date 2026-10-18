## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.PurityVectorBundle.zeroSection_spec` with a complete Lean proof.
The proof follows the existing docstring: derive the Noetherian instance from finite
type over the fixed field, apply `VectorBundleZeroSection.zero_spec`, and transport
its section identity and closed immersion along `V.phi.inv`. For each affine open,
choose `VectorBundleZeroSection.zeroRestricted`; its inclusion equation is
`Scheme.Hom.resLE_comp_ι` after cancelling `phi.inv ≫ phi.hom`, and its chart equation
is exactly `VectorBundleZeroSection.affineChart_spec`.

No signatures, definitions, visibility, imports, or other modules changed. The
existing definition node has no numbered proof plan; this implements the route
already stated in the theorem's docstring, with no new node or route change.
The unit's realized statement and step lists are empty, and its route is preserved.

Validation: `lcompile.py` compiled the module cleanly in 4.6 seconds. Searches with
LeanFinder, Loogle, the launcher's Mathlib grep, and `rg` in both project roots
confirmed that the canonical bundle lemmas already provide the needed conclusions.
Loogle and grep located `Scheme.Hom.resLE_comp_ι`; LeanFinder returned closed-immersion
infrastructure rather than an alternative vector-bundle theorem.
The proof works uniformly in rank zero, on empty schemes, and for empty affine opens:
it introduces no nonemptiness or positive-rank hypothesis.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.PurityVectorBundle.zeroSection_spec`
(node `def-pur-vector-bundle-zero-section`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The existing canonical bundle lemmas remain dependencies, with their existing holes
unchanged; this is a proof from their declared interfaces, not an axiom-free proof
of those dependencies.

## No longer needed

None. All existing imports support the file's statements or definitions, and no
proof-only imports were added. The symmetric-algebra construction, relative-Spec
interface, and affine closed-immersion argument are reused through the already
imported canonical vector bundle rather than imported or duplicated separately.
No DAG dependency, node, or module is pruned; the existing construction route stays.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The node is a definition with empty `proof` and
`proof_deps`; its Lean theorem docstring already explicitly names the shorter
canonical-bundle transport proof used here. The current blueprint source is under
`main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/`, while the node's
historical source path and chapter metadata still name `sec-smooth-purity`.
The current definition agrees with the delivered signatures and proof.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
