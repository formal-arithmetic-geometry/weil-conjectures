## What changed

Completed the duplicate-construction repair requested by upstream review #1424.
`HomologicalComplex₂.tensorBicomplex` already abbreviates the object of Mathlib's
`Functor.mapBifunctorHomologicalComplex (curriedTensor _) _ _` and is unchanged.
`HomologicalComplex₂.tensorBicomplexMap` now abbreviates the existing map of
`Functor.uncurry.obj` of this bifunctor instead of writing its composition again.
Its return type is inferred from this canonical map. The elaborated type is
definitionally the original type; no hypothesis, conclusion, universe or binder
changes. The compatibility abbreviations follow brief-stage3 §4's instruction
to retain the old name as an abbreviation of the existing construction.

Normalize only `Functor.uncurry` during elaboration using `dsimp% only` so that
the existing caller simplification API works without adaptations. Added the
public import `Mathlib.CategoryTheory.Functor.Currying` for this public data alias
and ordinary import `Mathlib.Tactic.DSimpPercent` for elaboration. Restored
`chainTensorMap` verbatim from the repository; the earlier attempt's unrelated
local-let refactor is discarded. No consumer module is changed.

Updated the existing node's proof route to name Mathlib's uncurried map and this
normalization. Change record: `coord/changes/tensor-bicomplex-uncurried-map.md`.

Validation: the item compiles cleanly, as do all four direct users unchanged:
`Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso`,
`Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso`,
`Sheaf.Algebra.Category.ModuleCat.TorSymmetry`, and
`Sheaf.Algebra.Homology.FlatResolutionTorComparison`.
Scratch Lean checks establish by `rfl` equality with the old composition and
check the original type. The component formula `a.f p ⊗ₘ b.f q` holds for arbitrary
p,q, including zero degrees and zero maps. The item's three constants use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

This is a repair of an already sorry-free module, not a new proof or decomposition.
Holes closed: none (0 of 0). Holes added: none. No sorry remains in the item.
No new theorem, definition node, or axiom was added. The already complete
`tensorBicomplex`, `tensorBicomplexMap`, and `chainTensorMap` remain complete.

## No longer needed

No import, node, or module is pruned. The handwritten first-variable/second-variable
map composition is replaced by Mathlib's existing uncurried map. The object's
canonical abbreviation, the node's proof dependencies, and the unit route stay.
No consumer adaptation is needed: all four direct users compile unchanged.

## Where the brief, the DAG or earlier work was wrong

The general proving brief's premise of remaining sorry declarations does not
apply to this repair item. The repository already landed N2's object repair;
the earlier P2 attempt only refactored unrelated `chainTensorMap` data and
failed the delivery gate. This attempt addresses the remaining map alias
instead of adding an unrelated proof or hole. The return type annotation is
replaced by Mathlib's inferred map type; its equality to the old signature is
checked in Lean. This is an interface repair, not net sorry progress.

An initial direct unnormalized alias required adding `Functor.uncurry_obj_map`
to the row and column naturality simp lists. The delivery tool's baseline check
then failed because the shared compiled snapshot still had the older homMk-based
map, while the repository's current row/column proofs already used the repaired
canonical map. Instead of depending on a snapshot refresh or changing the tool,
normalize the Mathlib map at elaboration: all original consumer proofs compile
against this final alias, so no forced adaptation is delivered.

The new map is definitionally equal to the previous map, so the reopened definition
review has a Lean equality witness and no target changes mathematical meaning.
The item's node is not itself a realized unit statement or step; the unit's
existing realized declarations and route are retained.

## Second reading by P2

1. Compared the entire delivered Lean file with the repository using `diff -u`.
   Only the two imports and `tensorBicomplexMap` change. The other two declarations,
   their signatures and bodies, and all docstrings are byte-for-byte unchanged.
   The map's omitted return annotation is explicitly recorded in
   `coord/changes/tensor-bicomplex-uncurried-map.md`, with verbatim old and new code.
   The scratch type check accepts the original return type and the equality to
   the entire old map body is proved by `rfl`. Verdict: no mathematical interface
   change, no altered hypotheses or universes, and no target weakening.
2. Compiled the delivered module locally through `lcompile.py`, then compiled a
   scratch set containing that exact module, the existing component/type/equality
   checks, and all four direct importers. Compared the four importer copies with
   the repository: all are identical. All six files compile without warnings.
   `#print axioms` for `tensorBicomplex`, `tensorBicomplexMap`, and `chainTensorMap`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`. Scanned the delivered
   Lean for forbidden declarations and `sorry`: none. Verdict: complete concrete
   data constructions, no hollow definition or arbitrary unproved witness.
3. No statements or nodes are split off, so there are no new lemma claims to
   search or test. Read Mathlib's `Functor.uncurry` in
   `CategoryTheory/Functor/Currying.lean`: its map is exactly the original
   first-variable map followed by the second-variable map. Read
   `mapBifunctorHomologicalComplexObj` and `mapBifunctorHomologicalComplex` in
   `Algebra/Homology/Bifunctor.lean`: their object differentials and map components
   match this node. The compiled component check proves the map formula for all
   natural degrees and all chain maps, including zero degrees and zero maps.
   Verdict: existing Mathlib construction reused, with no relabelled open goal.
4. Read the source [Stacks Tag 00M3](https://stacks.math.columbia.edu/tag/00M3),
   its double-complex construction and functoriality paragraph. The tensor terms,
   unsigned differentials, and pair-of-maps formula agree. The repair takes the
   existing Mathlib map directly; `dsimp% only [Functor.uncurry]` preserves the
   original callers' simplification behavior. The public Currying import supplies
   the map construction, while DSimpPercent is an ordinary elaboration import.
   The existing Additive import supplies the retained `chainTensorMap` API.
   No old proof dependency or import is removed; `No longer needed` is complete.
   Read `dag/units/sk-thm-p1.json`: this node is not a realized statement or step,
   and no realized route changes. Verdict: no bypass or unreported pruning.
5. Compared the delivered node with its repository version: only `proof` and
   `proof_origin` change. The new step names precisely the canonical bicomplex,
   uncurried map, elaboration normalization, and retained `chainTensorMap` used
   in Lean. Read both dependency nodes: their module tensor product and termwise
   chain tensor constructions are exactly the data this implementation uses.
   `proof_deps` remains their union, and no new node fields are needed.
   Verdict: metadata agrees with the implementation.

Second reading changed only this report, adding the independent review. No Lean,
node, or change-record repair was necessary. Independently repeated the caller,
component, definitional equality, original type, and axiom checks described above.
