## What changed

Proved `integralClosure_finiteFibrePart_localization` in
`lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean` without changing its signature,
universes, public imports, or existing docstring. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.IsIso` and the proved private helper
`exists_isIso_neighborhood_of_awayMap_bijective`.

The helper glues the principal localization isomorphisms using
`SpecMapRestrictBasicOpenIso`, `isIso_SpecMap_iff`, `Opens.iSupOpenCover`, and the
Zariski-local-at-target criterion. The main proof uses all four planned Sheaf declarations.
It equips the clopen product factors with their quotient base algebra structures, upgrades
the factor maps to algebra homomorphisms, verifies the first factor lies in the chosen open,
and applies the existing choose-g statement. The two factor-preservation clauses and the
unique first-factor preimage are proved by coordinate calculations through the product
ring equivalence. The node's proof steps now describe this glue; its dependencies are unchanged.

Read the official Stacks [Tag 09XH](https://stacks.math.columbia.edu/tag/09XH) statement and
proof. The five-step route is retained, and no unit statement or realized step is bypassed.
Local compilation passes without warnings (about five seconds).

## Proved and sorry left

Proved `integralClosure_finiteFibrePart_localization`
(node `lem-weil-pbc-integral-closure-finite-fibre-part-localization`): one of one original
sorries removed. The private neighbourhood helper is also fully proved. No sorry remains
in the item's module, and this delivery adds no sorry and no new public declaration.

The proof intentionally depends on the existing, still-sorry declarations
`Algebra.isQuasiFiniteAtPrime_of_finite_quotient_component`,
`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`,
`AlgebraicGeometry.integralClosure_finiteFibre_image_clopen`, and
`AlgebraicGeometry.integralClosure_finite_fibre_choose_g`. These are unchanged dependencies,
with their existing nodes, sources, and proof plans; this is a stage-3 reduction to them.

## No longer needed

None. Every planned proof import and each of the four planned dependency nodes is used.
The new Mathlib proof import supplies the scheme isomorphism criterion and locality.
No new modules or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. Two pieces of glue were implicit in the plan: passing
from pointwise bijective localization maps to an isomorphism over their union, and
constructing the quotient algebra structures on the product factors returned by the
image-clopen lemma. Both are now proved in Lean, without assuming an extra hypothesis.

## Second reading by T1

1. Compared the delivered module and node with the repository versions. The theorem
   signature and all existing declarations are unchanged; only the proof, a proof-only
   import, and the node's proof prose changed.
2. Compiled the module locally. It is warning-free and contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`; the helper is private and fully
   proved. The existing imported sorry declarations are the four planned dependencies.
   A scratch copy with `#print axioms` confirms that the helper uses only `propext`,
   `Classical.choice`, and `Quot.sound`; the main theorem additionally uses `sorryAx`
   through the existing open dependencies, as reported above.
3. Checked the helper and factor interface against the stated mathematics and searched
   the library/Mathlib for duplicate declarations. No new public statement was added,
   and the private helper is a genuine glue lemma rather than a restatement.
4. Checked the proof from the target downward: the four planned Sheaf dependencies are
   used, the Mathlib import is proof-only, and no old dependency or import can be pruned.
   The unit route and all five proof steps remain intact.
5. Checked the node's proof text, dependencies, and origin against the Lean proof; the
   added implementation details accurately describe the isomorphism gluing and product
   calculations.

Restored the existing docstring's spelling of `Spec C₁` (the first worker had changed
it unnecessarily) and added this review report. No mathematical repair was needed.
