## What changed

Filled the proof of `AlgebraicGeometry.Scheme.adicFiniteCompletion_bounds` in
`Sheaf.Paper.AdicFiniteCompletionBounds`, preserving its public signature and its
original public import. Added private proof imports for the two new statements,
pro-etale exact products, derived countable products, exact-functor cohomology,
and independent-coefficient K-flat resolutions.

Three proved private helpers supply the glue: `tor_cohomology_bounds` tests Tor
amplitude against the tensor unit; `underlying_cohomology_bounds` transports that
vanishing through exact scalar restriction; `model_exact_products` transports
exact products from the actual pro-etale site to its coefficient-sized model via
the equivalence of module-sheaf categories.

The main proof obtains a triangle for quotient completion, uses finite generation
of the ideal and the existing `koszul_quotient_reflector` unit criterion to
transport it to the complete object, and applies the cohomology long exact
sequence. It treats degree `b + 1` separately by cancelling the epic degree-b
Roos map. The other degrees follow from vanishing on both adjacent products.
All choices are of isomorphisms or distinguished triangles for already defined
objects; no new definition or arbitrary data witness is introduced.

Updated only the item's own node proof, proof dependencies and proof origin.
Added two new Lean modules and their nodes. No existing shared interface, target,
source-library declaration, or other existing module was changed.

## Proved and sorry left

Closed the one original proof hole in
`AlgebraicGeometry.Scheme.adicFiniteCompletion_bounds`; its module now has zero
`sorry`s. Its proof and all three private helpers compile. This delivery is a
decomposition: one original hole closed and two strictly smaller holes added,
not an axiom-free proof of the full result.

The complete list of remaining holes introduced by this delivery is:

- `AlgebraicGeometry.Scheme.adicFiniteCompletion_tower`, in
  `Sheaf.Paper.AdicFiniteCompletionTower`, node
  `lem-sfb-adic-finite-completion-tower`: one `sorry`. This identifies the actual
  normalized tower with the already constructed quotient-tower completion. It
  has no completeness, Noetherian or Tor hypotheses and proves no cohomology
  bound. The item still has to use the completion-unit criterion and explicitly
  transport its triangle to obtain its first conclusion.
- `AlgebraicGeometry.Scheme.adicFiniteTop_roos_epi`, in
  `Sheaf.Paper.AdicFiniteTopRoosEpi`, node
  `lem-sfb-adic-finite-top-roos-epi`: one `sorry`. This proves epimorphy of one
  cohomology map on a product, using only the residue reduction's Tor bound. It
  has no completeness hypothesis and proves neither a derived-limit comparison
  nor a bound on the original object. The item proves the long-exact-sequence
  argument combining this with its independently proved product vanishing.

All three delivered Lean modules compiled together without errors or warnings:
8.4 s for the tower statement, 9.3 s for the endpoint statement and 11.6 s for the
main proof. After removing an unnecessary exploratory tensor import and making
the K-flat-resolution import explicit, the final main module compiled in 5.5 s.
The delivery preflight performs the final compilation and declaration checks.

## No longer needed

No modules or nodes are withdrawn or claimed pruned. The item's original sole
public import `Sheaf.Paper.AdicFiniteReductionData` remains necessary.
The exploratory proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` was removed;
the tensor-unit comparison is already public through the existing coefficient
construction, and the proof now explicitly imports the K-flat resolution it uses.

The item's proof no longer directly needs the full Milnor short exact sequence
`det-pe-milnor-sequence` or the completion adjunction
`lem-sp-completed-pullback-adjunction`: the existing completion-unit criterion
and the triangle long exact sequence suffice. These nodes are not globally
pruned, since existing coefficient and epimorphic-tower modules still use them.

The original direct proof dependencies `lem-pur-derived-change-of-rings`,
`lem-pur-kflat-change-of-rings`, `lem-pur-resolving-class-derived-adjunction`,
`def-pc-flat-sheaf-modules`,
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-strict-roos-comparison`, and `det-pe-milnor-epimorphic` are now used in
the genuinely smaller normalized-tower or endpoint arguments, with that use
recorded in the new nodes. They remain necessary below those statements.

## Where the brief, the DAG or earlier work was wrong

No statement was weakened and no mathematical claim was marked disputed.
The old plan correctly points to K-flat scalar normalization and the endpoint
argument, but its recorded dependency interfaces do not directly identify
`adicFiniteTransition` with the strict quotient-presentation transitions.
The completion adjunction alone does not provide that identification. The first
new lemma isolates precisely this comparison, including existence of the product.

The existing general strict-tower and epimorphic-tower results are reusable tools,
but their stated interfaces still require the normalized scalar comparisons and
the residue quotient-kernel calculation. The second new lemma isolates that
endpoint calculation and its consequence for the Roos map, without restating
the item's cohomology-bound conclusion.

The source passages read were Stacks `proetale.tex`,
`lemma-naive-completion` (099M), `lemma-describe-constructible-complexes` (09C2),
and `sites-cohomology.tex`, `section-derived-limits` (0940) and
`proposition-enough-weakly-contractibles` (0947). The latest blueprint's
`sk-lem-integral-models-stacks.proof.md` and the unit's realized route are
preserved. The two new nodes specialize genuine steps of that argument; neither
replaces a blueprint unit. Their statements were checked for the zero ideal,
unit ideal, zero complex and empty scheme. The tower statement uses only the
quotient-tower model of completion; its comparison does not need the Noetherian
hypothesis used by the reflector theorem.

Mathlib searches were run through `msearch.py` using LeanSearch, LeanFinder and
grep and are recorded, with their actual queries and outcomes, in each new node.
Local searches found no existing theorem with either normalized statement.
The existing bounded strict-tower theorem is formulated for an already chosen
strict complex tower; using it would still leave the comparison obligations
isolated here. The final proof instead handles the elementary triangle argument
directly. No dependency path from the cited existing nodes returns to the item.

## New nodes

`lem-sfb-adic-finite-completion-tower`:
`dag/nodes/sec-six-functors-basics/lem-sfb-adic-finite-completion-tower.json` and
`lean/Sheaf/Paper/AdicFiniteCompletionTower.lean`. This is the normalized strict
quotient-tower comparison with the existing completion functor. Its proof in
words records the pure-tensor scalar-unit calculation and the strict Roos
comparison. It imposes no Tor or completeness condition.

`lem-sfb-adic-finite-top-roos-epi`:
`dag/nodes/sec-six-functors-basics/lem-sfb-adic-finite-top-roos-epi.json` and
`lean/Sheaf/Paper/AdicFiniteTopRoosEpi.lean`. This is the endpoint surjectivity
step: tensor the successive-quotient short exact sequence with a flat K-flat
representative, use the residue Tor test in degree `b + 1`, and apply the
pro-etale epimorphic-tower theorem after the product comparison.

There are no change records, since no existing statement, definition, public
import, attribute or instance was changed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
