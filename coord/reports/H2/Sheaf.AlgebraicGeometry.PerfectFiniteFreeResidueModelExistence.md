## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.finiteFreeModel_of_fiberData` with a complete
Lean reduction following the original local-minimal-model and spreading route. Its signature,
universes, visibility, definitions and conclusion are unchanged.

The proof chooses a complex representing E via the actual localization functor, takes its
termwise stalk complex, applies the existing `DerivedCategory.exists_unique_minimalFreeModel`,
and proves boundedness using the two supplied Betti bounds. For a rank-zero term the displayed
module `ULift (Fin 0 → R)` is subsingleton; `ModuleCat.isZero_of_subsingleton` and `IsZero.of_iso`
prove that the term is zero. This is a real step between the two remaining interfaces.
The local module derived category uses `HasDerivedCategory.standard`, so no extra assumption
is added to the original theorem. The representative is chosen inside a proof, not installed
as a definition depending on an unproved existence statement.

Added two separate statement modules, `Sheaf.AlgebraicGeometry.StrictPerfectStalkFiberData`
and `Sheaf.AlgebraicGeometry.BoundedFreeStalkModelSpread`, with public named theorems, sources,
complete proof plans and new DAG nodes. The first proves facts only about the stalk and residue
cohomology and constructs no neighbourhood model. The second spreads an already supplied bounded
free stalk complex of arbitrary prescribed ranks and neither computes residue dimensions nor
constructs a minimal model. The main proof supplies the missing minimal-model construction and
boundedness by applying the existing ring theorem and the explicit zero-term argument.

Updated the original node's proof, proof_deps and proof_origin to match the Lean argument.
All added proof imports are non-public. No existing public import or interface changes.

The three delivered modules compile together, in import order, through lcompile.py. Searches:
LeanFinder returned local rank and ordinary spreading tools but no match; Loogle returned no
hits for `CochainComplex, IsLocalRing, Module.Finite`; Mathlib and both project roots were searched
with rg. LeanSearch reported Internal Server Error, which is recorded without a search verdict.
The Stacks source files are absent on this clone; the official pages for Tags 0BCD, 08EB, 0BC7,
09RE and 06YB were read instead.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.finiteFreeModel_of_fiberData`
(node `lem-sc-perfect-finite-free-residue-model-existence`). No sorry remains in the item module.

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.strictPerfect_stalk_fiberData`
  (node `lem-sc-strict-perfect-stalk-fiber-data`), in `StrictPerfectStalkFiberData.lean`.
- `AlgebraicGeometry.Scheme.spread_boundedFree_stalkModel`
  (node `lem-sc-bounded-free-stalk-model-spread`), in `BoundedFreeStalkModelSpread.lean`.

This is a decomposition: one original hole closed and two strictly separate lower holes added,
not a claim that the full theorem is independent of sorry. The existing ring theorem used in
its proof, `DerivedCategory.exists_unique_minimalFreeModel`, still has its existing sorry;
it is not changed or added by this delivery. The existing descent statements are also left to
their own items.

## No longer needed

Removed three direct proof imports from the original module:
`Sheaf.Algebra.Homology.AffinePerfectColimitDescent`,
`Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`, and
`Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`.
Their corresponding nodes `lem-pc-affine-perfect-colimit-descent`,
`lem-pc-affine-perfect-hom-colimit` and `lem-weil-pbc-finite-projective-standard-free-cover`
are now dependencies of the spreading node and remain imported by its module.
They are not pruned from the targets' import closure. No original planned mathematical
lemma, node or module is globally pruned; all remain needed for the same source route.
`def-pc-perfect-complex` remains a statement dependency through its public import.

The single-degree `FiniteFreeStalkHomotopySpread` and unit-cancellation modules found in the
search are not imported: their statements concern a single-degree normal form in scheme
module categories, not an arbitrary bounded local-ring complex. They were not dependencies
of the original plan, so no pruning credit is claimed for them.

## Where the brief, the DAG or earlier work was wrong

The original proof is a valid mathematical plan, but its imported declarations are ring-level
interfaces. They do not give either the equality of derived fibre dimensions with stalk
residue-tensor dimensions, or a scheme neighbourhood model from a given stalk complex.
Those interfaces are now separate, named items. No statement was found false or weakened.

Edge cases checked before stating the new lemmas: the zero object and the identically zero
rank sequence give zero models; a stalk point forces a nonzero local ring, as needed for
invariant basis number; arbitrary or reversed bounds are harmless because the hypotheses
then force the indicated terms to vanish; arbitrary unbounded G is allowed because taking
stalks is exact and its derived object has a locally strictly perfect comparison.
No separatedness hypothesis is used: the spreading proof works inside one affine open and
intersects principal opens of that affine, rather than intersecting arbitrary affine opens.
The residue field in the first new theorem is the residue field of O_X,x, which is exactly
X.residueField x. The chosen hK is a proof determining its representative up to derived
isomorphism, and that is precisely the equality used for the residue cohomology calculation.

The unit `sk-prop-av-cube` was read; no realized unit statement or step is bypassed or modified.
Existing exact-stalk, K-flatness, affine correspondence, localization-colimit and Hom-descent
nodes from other units are used as generic tools for the original Tag 0BCD route. Their unit
records are not changed and no tool_uses field is written by this worker.

## New nodes

`lem-sc-strict-perfect-stalk-fiber-data`, in
`dag/nodes/sec-abelian-varieties/lem-sc-strict-perfect-stalk-fiber-data.json`, states the
pseudo-coherence and residue calculation needed to apply the already existing local minimal
free model theorem. Its Lean module is `Sheaf.AlgebraicGeometry.StrictPerfectStalkFiberData`.
It requires no rank bound and constructs no local free neighbourhood model.

`lem-sc-bounded-free-stalk-model-spread`, in
`dag/nodes/sec-abelian-varieties/lem-sc-bounded-free-stalk-model-spread.json`, states spreading
for a supplied bounded free stalk model and its derived comparison. Its Lean module is
`Sheaf.AlgebraicGeometry.BoundedFreeStalkModelSpread`. It accepts arbitrary ranks; the original
proof supplies its model, boundedness and the Betti rank sequence separately.

No change record or forced adaptation is needed: no existing signature or definition changed.


## Second reading by H2

1. **Interface unchanged: pass.** Read the diff of the delivered item against the repository.
   Extracted the entire existing theorem signature through its conclusion and checked it
   byte for byte. It is identical. Both existing public imports remain public and unchanged;
   added imports in the item are proof-only. There are no changed definitions, extra
   hypotheses, weakened conclusions, target edits, adaptations or change records.
2. **Proof and axioms: pass as a decomposition.** Compiled all three delivered modules
   locally in import order. A scratch copy with `#print axioms` for all three declarations
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Inspected the whole proof: the representative is supplied by the actual localization
   functor, the local-ring derived category uses its standard instance, the ring minimal
   model receives both residue hypotheses and the upper rank bound, and the termwise
   isomorphism to a rank-zero module proves the lower and upper zero-term bounds.
   Exactly the two reported public named lower theorems have whole proofs `by sorry`.
   There are no definitions in the delivery, forbidden declarations, or hidden holes.
   Choice occurs within propositions; no data definition selects an arbitrary witness
   from an unproved mere-existence theorem.
3. **Split statements: pass.** Read both statements, docstrings, matching node statements,
   and their planned dependencies. The stalk lemma provides pseudo-coherence and residue
   dimensions for an arbitrary representative; it constructs no neighbourhood model.
   The spreading lemma accepts an already supplied bounded free stalk complex with arbitrary
   ranks; it computes no Betti numbers and constructs no minimal model. Thus neither merely
   renames the item. Checked zero objects, zero ranks, reversed bounds, arbitrary unbounded G,
   and non-separated schemes. A point's stalk is nonzero, so invariant basis number justifies
   the zero ranks outside the spreading model's bounds. The colimit descent theorem gives
   an isomorphism of complexes, not just of derived objects, retaining the ranks at the stalk.
   The residue comparison applies to any bounded-above finite-free representative by
   K-flatness and its derived isomorphism, including the one chosen from hK.
   Independent searches with different words used LeanFinder, Loogle and msearch grep,
   plus rg through both project roots. Found only ordinary localization/K-projective tools,
   a closed-pushforward stalk model, and single-degree stalk homotopy spreading; none supplies
   either new statement. Recorded these searches in the new nodes. Neither remaining lemma
   can be closed by a short application of an existing theorem.
4. **Route and pruning: pass.** The actual reduction uses the existing local minimal-model
   theorem and proves boundedness before spreading. All original mathematical dependencies
   stay on that same local-model/descent route. The report names the three direct imports
   moved into the spreading module and their nodes; it also accounts for perfect-complex
   data as a retained statement dependency. No module is globally pruned. Public imports
   in the new modules support their signatures; non-public imports describe the remaining
   proof plans. Read `dag/units/sk-prop-av-cube.json`: neither the statement nor its step or
   realized record is changed or bypassed.
5. **DAG agrees: pass.** The original node changes only proof, proof_deps and proof_origin.
   Its four proof steps match the actual Lean reduction, and proof_deps is their uses union.
   Both new nodes have the required source, complete proof steps, dependency union, searches,
   split status, created record, blueprint ancestry, chapter/unit and verbatim Lean signature.
   Checked the original and both new statement records against the Lean declarations.

Second reading changed only the residue-comparison explanation in the stalk lemma docstring
and its node proof: replace the appeal to proof irrelevance by K-flatness and invariance under
its derived comparison. Added independent search evidence and this review. No Lean proof,
statement, definition, import or hole count changed during second reading.

Source checks used the official [Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD),
[Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7),
[Tag 08EB](https://stacks.math.columbia.edu/tag/08EB),
[Tag 06YB](https://stacks.math.columbia.edu/tag/06YB), and
[Tag 09RE](https://stacks.math.columbia.edu/tag/09RE) pages. Their local-model, complex descent,
affine equivalence, stalk K-flatness and Hom descent arguments support the stated proof plans.
The outcome remains one hole closed and two added (net minus one), with no pruning credit.
