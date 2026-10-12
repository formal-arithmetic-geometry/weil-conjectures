## What changed

Proved both existing declarations of
`lean/Sheaf/AlgebraicGeometry/ZariskiExtensionByZeroExact.lean`, with their signatures,
visibility, instance attribute and public imports unchanged.

`AlgebraicGeometry.zariski_extensionByZero_additive` follows from componentwise additivity
of restriction and Mathlib's `sheafAdjunctionContinuous.left_adjoint_additive`.

`AlgebraicGeometry.zariski_extensionByZero_exact` specializes the already proved
`CategoryTheory.site_extensionByZero_exact` to the precoverage associated to the Zariski
Grothendieck topology. A direct proof that generating this precoverage recovers the topology
allows rewriting the general theorem to exactly the required functor. Monomorphism
preservation follows by applying short-exactness preservation to `cokernelSequence f`.

Added proof imports of `Mathlib.CategoryTheory.Adjunction.Additive` and
`Mathlib.CategoryTheory.Sites.Abelian` (needed for the cokernel sequence) and
`Sheaf.CategoryTheory.SiteExtensionByZeroExact`. Updated the existing node's proof,
proof_deps and proof_origin to this argument. No new statements, definitions or nodes.

The general site exactness result, node `lem-weil-pbc-site-extension-by-zero-exact` in
unit `sk-prop-cd`, is used as a generic tool. It is the same source Lemma 03DJ for arbitrary
localized sites, already proved, and its specialization replaces no unit-level step of
`sk-thm-p1`. This item's node is not a realized statement or step of that unit.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.zariski_extensionByZero_additive`
  (node `lem-weil-pbc-zariski-extension-by-zero-exact`).
- `AlgebraicGeometry.zariski_extensionByZero_exact`
  (the same node).

No `sorry` remains in the item; no holes were added or split off. The imported general
site exactness theorem and its explicit presheaf-adjunction proof are already proved.
This is a proof, not a decomposition into new holed statements.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction`
and the direct proof dependency `lem-weil-pbc-zariski-extension-by-zero-adjunction`.
Its existential topological-subspace formulation is unnecessary for the specified
localized-site functor: Mathlib directly supplies that functor's adjunction.

The following original DAG proof dependencies are also no longer direct dependencies
of this item's proof:

- `def-weil-pbc-sites-and-cohomology`;
- `def-weil-pbc-sheafification`;
- `lem-weil-pbc-sheafification-exact`;
- `lem-weil-pbc-abelian-presheaves-evaluation-exact`;
- `def-weil-pbc-exact-sequence`;
- `def-weil-pbc-category-colimit`;
- `lem-weil-pbc-left-adjoint-preserves-colimits`.

Their Mathlib content, where needed, is encapsulated by the general site theorem or
used for elaborating the unchanged statement. This does not claim these shared nodes
or Mathlib modules are globally unreachable. Kept
`lem-weil-pbc-abelian-exact-epi-cokernel` for its cokernel-sequence clause and added the
single general site exactness node. No other existing proof import was present to remove.

## Where the brief, the DAG or earlier work was wrong

The original plan did not use the already proved general localized-site exactness
result. Its named Zariski adjunction dependency supplies an existential functor on
sheaves over the topological subspace, whereas the item specifies the concrete
left-Kan-extension/sheafification functor on the slice site. Using Mathlib's adjunction
for that concrete functor and the general site theorem avoids an unnecessary comparison.
No statement was changed or disputed. The argument applies also to the empty open and
the entire space; no nonemptiness or proper-open hypothesis is introduced.

## Second reading by B2

1. Compared the delivered module with the repository version. Existing declaration
signatures, visibility, and attributes are unchanged; only proof imports and proof bodies
changed. Verdict: pass.

2. Compiled the module with `lcompile.py`; it is error-free and contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proofs use only the
allowed imported declarations. Verdict: pass.

3. Checked the two existing statements against the node and source, and searched the
library and Mathlib for duplicate results. No statement was split off and no statement
was weakened. Verdict: pass.

4. Read the proof top-down. It uses the general site extension-by-zero exactness theorem,
the continuous sheaf adjunction for additivity, and the cokernel short-complex argument;
the removed imports and proof dependencies are listed above. Verdict: pass.

5. Compared the node's proof, proof dependencies, and origin with the Lean proof and
verified that the unit route remains intact; the specialized theorem is below the unit
level. Verdict: pass.

Changed during second reading: added this review record only; no Lean declarations or
statements required repair.
