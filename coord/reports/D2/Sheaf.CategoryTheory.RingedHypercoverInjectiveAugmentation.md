## What changed

Proved `CategoryTheory.ringedHypercover_injective_augmentation_exact` with its original
signature, universes, hypotheses and public imports unchanged. The proof constructs the free
represented module presheaves explicitly in the required module universe, proves the additive
Yoneda and sheafification comparisons, proves local exactness, passes through kernels under
sheafification, and applies injective extension to the resulting exact short complexes.
All construction and algebra helpers in the original module are private and proved.

Added `Sheaf.CategoryTheory.RingedHypercoverFiniteCones`. Its main theorem
`CategoryTheory.RingedHypercover.finite_local_cones` is fully proved by finite-face induction.
`HasLocalLifts` writes the original matching hypothesis verbatim; the proved `local_edge`
specialization is also used for degree-zero kernel exactness. Other helpers are private and
proved. In particular, compatible codimension-one tuples are converted to full matching
families by factoring through a missing vertex and proving independence of the choice.

Updated the original DAG proof and added the finite-cone node. No existing definition or
statement changed, and no forced adaptations are needed. The conservative interface check
requires a change record for the namespace and variable scopes of the private proof helpers;
that record documents their lack of effect on existing public signatures.

Validation: both delivered modules compile without warnings through `lcompile.py --all`.
`#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound` for both the original
target and `finite_local_cones`. The original target signature was compared verbatim against
the repository copy and is unchanged. The new finite-family theorem requires nonempty support;
the cycle proof handles zero support separately. Degree-zero empty fibres, zero coefficients,
and covering sieves with no arrows introduce no extra hypotheses. The cone functions retain
original labels, so the proof also handles distinct labels that coincide after restriction.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ringedHypercover_injective_augmentation_exact`
(node `lem-weil-pbc-ringed-hypercover-injective-augmentation`).

Added zero holes. The new theorem `CategoryTheory.RingedHypercover.finite_local_cones`
(node `lem-weil-pbc-ringed-hypercover-finite-local-cones`) is fully proved.
There are no remaining `sorry`s in either delivered module. This is a proof, not a decomposition.

## No longer needed

Removed these direct proof imports from the original module:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (the API is already available
  through the original public module-sheaf import).
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator` (explicit free construction handles
  unequal ring and module universes).
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.Paper.SiteSheafificationSectionsLocal`.

The proof no longer needs these original proof-dependency nodes:

- `def-weil-abstract-derived-category`: the target has an explicit function-exact formulation.
- `def-weil-pbc-sites-and-cohomology` as a direct dependency of the target proof: its covering
  axioms are used inside the new finite-cone node instead.
- `lem-pc-sites-sheafification-underlying-sets`.
- `lem-weil-pbc-free-yoneda-presheaf-module`: the required universe-general Yoneda equivalence
  is proved explicitly in the target module.
- `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`: use preservation of kernels and
  the epi-kernel-lift exactness criterion directly.
- `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`: the statement already gives local lifts.
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`: construct the full matching family directly.
- `lem-weil-pbc-site-sheafification-sections-local`: local lifts and sheaf separatedness prove
  the sheafified map epi through its adjunction, without local representability of new sections.

Thus `Sheaf.Paper.SiteSheafificationSectionsLocal` is pruned from this proof's import route.
Other parents may still need it. Original public imports are retained to preserve the module's
existing public interface; the DAG proof dependencies record actual proof use.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Mathlib's represented free module API uses the same universe for
ring values and module values, while this target allows the module universe to be larger.
The explicit ULift/Finsupp construction resolves that mismatch without changing a signature.

The planned sheafification-sections argument is unnecessary: a locally surjective kernel lift
becomes epi after sheafification by the adjunction and separatedness. For the finite-cone
lemma itself, the finite original family already supplies a vertex in each relevant augmentation
fibre, so its base case can choose these vertices before taking covers; degree-zero local
lifting is still used to prove the augmentation of free sheaves epi.

LeanSearch was tried for the new node and returned an internal-server error. LeanFinder,
Loogle, and source grep completed; their actual queries and results are in the node. Blueprint
searches for finite cones and Tag 01GE found no existing blueprint node with this statement.
The unit's route is unchanged.

## New nodes

`lem-weil-pbc-ringed-hypercover-finite-local-cones`, in
`dag/nodes/sec-proper-base-change/`, is a fully proved geometric part of the original
finite-support argument, attached to `Sheaf.CategoryTheory.RingedHypercoverFiniteCones`.
It asserts two adjacent local cone functions on a nonempty finite original label family,
independently of coefficients, sheafification, or injectivity. Its proof follows the actual
finite-face induction in Lean. No new obligation remains.

Change record: `coord/changes/ringedHypercover_injective_augmentation_exact-proof-scope.md`
documents the added private-helper scopes and lists downstream users; no existing statement
or public definition changes.

## Second reading by D2

1. **Interface and accidental changes.** Compared the delivered target module with the repository version. The target declaration, including all binders, universes, hypotheses and conclusions, is byte-for-byte unchanged. The added finite-cone module is new and its public declarations are recorded by the new DAG node; no existing declaration was weakened or given extra hypotheses.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`. There are no `sorry`s, hollow definitions, forbidden declarations, or warnings. A scratch module printing axioms reports only `propext`, `Classical.choice`, and `Quot.sound` for both public theorems.

3. **Statements and nodes.** Checked `HasLocalLifts`, `local_edge`, and `finite_local_cones` against the finite-support construction and the target's matching hypothesis. The finite-cone statement is true for nonempty finite support, is strictly auxiliary to the target, and has a matching node with source, proof steps, dependencies, and search record. No duplicate library statement was found.

4. **Pruning and route.** The target proof uses the finite-cone theorem and retains the unit's hypercover route. The removed proof-only imports and no-longer-needed nodes listed above are not referenced by the delivered proof; original public imports remain unchanged.

5. **Edge cases and metadata.** Checked zero cycles, degree zero, empty fibres, coefficient restriction, repeated labels after restriction, and finite-family nonemptiness. The DAG `proof` and `proof_deps` entries agree with the declarations actually used. The only repair made in this second reading was adding this required review section and removing a temporary scratch print module from the delivery set.
