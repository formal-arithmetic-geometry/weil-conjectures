## What changed

Proved `AlgebraicGeometry.Scheme.boundedComplex_tensor_proper_support_bound` with its
signature and public imports unchanged. Added proof imports of
`ClosedSubsetProperOverBaseUnionPreimage`, `DerivedTensorOpenRestrictionUniverses`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and Mathlib
`Algebra.Category.Grp.Zero`, `Topology.Sheaves.Abelian`, `Data.Int.Interval`.
Four proved private helpers handle zero stalks, zero open restriction, tensor with zero,
and support containment. The bounding closed subset is constructed as a finite supremum;
closed supports chosen from the hypothesis are uniquely determined by their support equality.
Updated the item's DAG proof and dependencies to match this route.

## Proved and sorry left

Closed the only hole: `AlgebraicGeometry.Scheme.boundedComplex_tensor_proper_support_bound`
(node `lem-pc-bounded-complex-tensor-proper-support-bound`). No holes added or left in
this delivery; no decomposition. Compilation checks the full unchanged statement, including
empty intervals, empty support, arbitrary unbounded E, and independent localization universes.
Existing imported declarations are used as library results; no new statement or definition.

## No longer needed

No existing imports removed: both public imports are required by the signature.
The direct dependencies `lem-weil-pbc-surjective-universally-closed-separated` and
`lem-weil-pbc-image-universally-closed` are replaced at this node by the existing finite-union
result `lem-weil-pbc-closed-subset-proper-over-base-union-preimage`. Thus no direct imports of
`Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed` or the Mathlib descent
module are needed here. These results may remain transitive dependencies of the finite-union
result and are not claimed globally pruned. The explicit direct dependency
`def-weil-finite-type-morphism` is not used as a separate proof lemma (its instance remains
in the unchanged signature). The old direct dependency `def-pc-derived-category` is also no longer used separately:
its definitions remain available through `DerivedTensorStructure`; no separate proof import
is required. These four nodes are removed only from this node's direct `proof_deps`,
not asserted to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan did not name the existing finite-union theorem or the existing
independent-universe derived tensor restriction comparison. Both fit without extra hypotheses.
The unit record `sk-thm-picard-semicon` has empty realized arrays; this is a support-tool
refinement below its route, and no unit statement or step is bypassed.
No false statement, signature correction, forced adaptation, or tool workaround was needed.
LeanFinder was unavailable; Loogle and Mathlib grep found no direct theorem. Library rg
located the two reusable results above. Stacks 0CYR, 08DX and 0DJQ were read online.


## Second reading by Y2

1. Compared the entire delivered Lean module and node with the repository baselines.
   The existing theorem signature is byte-for-byte identical. Public imports, visibility,
   and all existing definitions are unchanged. The only node fields changed are `proof`,
   `proof_deps`, and `proof_origin`. No change record or forced adaptation is needed. Pass.
2. Compiled the module with `lcompile.py`: no errors or warnings. Compiled a scratch copy
   with `#print axioms` for the target and all four private helpers: each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. There is no `sorry`,
   axiom, unsafe declaration, opaque declaration, extern, or implemented_by in the file.
   The finite support union is constructed explicitly. The chosen closed supports are
   uniquely determined by their equality to the nonzero-stalk locus (Closeds.ext), so
   the choice meets the data-construction rule. Pass.
3. There are no split-off statements or new nodes. Read each helper and the signatures
   of the finite-union theorem, open-restriction tensor comparison, and exact-functor
   homology comparison. Checked the empty integer interval, zero terms, empty support,
   empty open complement, arbitrary unbounded E, and independent derived-category
   universes: none requires an extra hypothesis. Library searches for tensor/support
   variants found no shorter public result; the related zero-stalk helper is private.
   A new Loogle search for sheaf zero-object results returned no hits. Pass.
4. The proof follows the finite support union and zero restriction argument directly,
   without adding holes. Import-removal experiments confirm that Grp.Zero provides the
   subsingleton lemma, Int.Interval provides LocallyFiniteOrder on integers, and
   Topology.Sheaves.Abelian provides the presheaf zero-morphism instance used here.
   The other proof imports provide the three explicitly applied comparison/union results;
   the two public imports supply the unchanged signature. Checked the unit record
   `sk-thm-picard-semicon`: its realized arrays are empty, and this support refinement
   bypasses no realized unit statement or step. Corrected the pruning report to name
   all four removed old direct proof dependencies. No module is claimed globally pruned.
5. Read the node's four proof steps against the Lean code and checked that their `uses`
   union equals `proof_deps`. The exact-functor node records precisely the upstream
   `mapDerivedCategoryHomologyFunctorIso` used by this proof. The finite-union and
   independent-universe restriction nodes match the applied declarations. The node's
   statement, source, statement dependencies and Lean signature are unchanged. Checked
   [Stacks 0CYR](https://stacks.math.columbia.edu/tag/0CYR),
   [08DX](https://stacks.math.columbia.edu/tag/08DX), and
   [0DJQ](https://stacks.math.columbia.edu/tag/0DJQ) against the described route: 08DX is
   contextual for locality, while the general restriction comparison is supplied by its
   existing proved Lean declaration. Pass.

Second reading changed only the report: added the missing removed-dependency entry
`def-pc-derived-category` and this independent review. The proof and DAG needed no repair.
