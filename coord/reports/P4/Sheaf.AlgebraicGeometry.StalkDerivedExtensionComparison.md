## What changed

The original theorem signature and docstring are unchanged. Its proof now constructs
scalar extension using `ModuleCat.exists_baseDerivedExtension_linear` for the actual
composite stalk ring map. The K-flat stalk criterion and the existing universal
scalar-extension counit theorem independently prove counit invertibility at each stalk.

Added `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso`, containing only
the comparison before homology. Its statement assumes a universal scalar-extension
pair and asserts the natural comparison and its representative equation; it does not
repeat the existence or stalk-counit invertibility clauses of the assigned theorem.
A fully proved private `homology_comparison` in the assigned module obtains the final
homology formula by functoriality, cancellation of inverse isomorphisms and naturality
of `homologyFunctorFactors.inv`. No homology equation is left as a new hole.

The existing DAG node now records these three actual proof steps. The new node records
the remaining K-flat localization argument, its dependencies, and the searches run.
Proof-only `import all Mathlib.Algebra.Homology.Localization` exposes the definitions
needed for the final Q/Qh object calculation; public imports and existing signatures
remain unchanged. Only the assigned module and the new module are delivered.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparison`.
The private `homology_comparison` is fully proved with no new hole.

Added one hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonIso`
in `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso`, node
`lem-pc-stalk-derived-extension-comparison-intermediate`.
Its proof is exactly `by sorry`; its docstring gives the full K-flat representative,
roof-refinement, inverse and counit computation argument.

This is a decomposition: one upper hole closed and one strictly lower hole added,
so the net number of holes closed by this delivery is zero. Scalar-extension existence,
stalk counit invertibility, and passage from derived-category compatibility to the
specified homology equation are completed from existing declarations.
Both delivered modules compile without warnings via `lcompile.py --all`.

## No longer needed

The original planned direct proof dependency
`lem-pc-derived-tensor-second-factor-functor` /
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor` is replaced by the existing
scalar-extension existence theorem. It was never an explicit import of this module,
so there is no import line to remove. It may remain in other transitive import paths;
this delivery makes no claim that it becomes globally unreachable.

No original public import is removed: both are required by the unchanged signature.
The new comparison module needs only the public source-transport import and does not
import `BaseDerivedTensorLocalizedNaturality`. The old direct dependencies `def-pc-derived-pullback` /
`Sheaf.AlgebraicGeometry.DerivedPullback` and
`def-pc-single-complex-base-change-stalk-condition` /
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` are no longer direct
proof dependencies of the assigned theorem: the comparison step now belongs to the
intermediate node. They remain needed transitively by that node and by the unchanged
signature. The stalk criterion, scalar-extension counit and source-transport node
remain direct dependencies. No module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The source-library fixed-second-factor
functor is more general than the scalar-extension existence needed in step 1.
The original proof plan's descent of the natural comparison is not yet supplied by a
matching declaration, so that exact step is isolated before homology rather than
repeating the complete target theorem.

The new comparison was checked on zero complexes, identity morphisms, and zero stalk
rings: all factors are the same localization and tensor identifications, with no
nonzero-ring, flatness, boundedness, or base-derived-comparison-isomorphism assumption.
The unit's realized route is unchanged; no unit-level result is bypassed.

## New nodes

`lem-pc-stalk-derived-extension-comparison-intermediate` is the comparison and its
formula in the derived category, for an already given universal scalar-extension
pair. It contains neither existence of that pair, counit invertibility, nor homology.
Its module is `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso`.
No existing statement or definition changed and no forced adaptation is needed.

## Second reading by P4

1. Compared both delivered modules with the repository. The existing module changes
   only its proof, adds one private proved helper and proof-only imports, and locally
   suppresses the unused-variable linter. The declaration parser reports no changed
   existing signature; the existing theorem docstring is also unchanged. The comparison
   module is new. There is no statement or definition change requiring a change record.
2. Read the complete proofs and scanned both modules for forbidden declarations and
   holes. The assigned theorem and `homology_comparison` contain no holes. The only
   delivered hole is the named public comparison theorem listed above; there is no
   definition in either delivery choosing arbitrary data from an unproved existence
   theorem. Scalar-extension witnesses are used within a proof of existence, rather
   than installed as new definitions. Local compilation and the axiom checks are
   recorded below.
3. The new statement is the derived-category comparison step, for a supplied universal
   pair, rather than the original existence/counit/homology assertion under another
   name. Checked the orientation and order of its localization, counit, tensor-stalk,
   and inverse pullback-counit factors. The specified degreewise tensorStalkIso agrees
   with the natural pullback-stalk identification by exists_tensorStalkIso's component
   equation. K-flat resolutions and exact stalks justify the descent and inverse.
   Zero complexes and zero stalk rings require no nonzero or flatness hypotheses;
   identity pullback gives the same counit-compatible identification. Its sourced
   docstring and node describe the argument. Fresh leanfinder search for an exact-stalk
   composite left derived functor found only ordinary presheaf stalk maps. Loogle
   found no direct characterization under the queried name; grep found general
   leftDerivedLift, leftDerivedNatIso and uniqueness tools. The upstream K-flat
   characterization and our resolving-class construction do not by themselves supply
   the composite comparison or its formula. No duplicate or quick closure was found.
4. The actual reduction constructs the universal scalar extension, proves stalk
   counit invertibility independently, and performs the homology calculation. Both
   existing public imports are used by the signature; all added imports are private
   to this proof. The new module's only public import provides its signature. The
   No longer needed section now explicitly accounts for every old direct dependency
   removed from the assigned node. The derived pullback and tensor-stalk steps remain
   in the new comparison node, so no unit route is bypassed. Inspected
   dag/units/sk-thm-picard-semicon.json: its realized fields are unchanged (already
   empty in the baseline); this delivery introduces no change at unit level.
5. The assigned node's three steps and dependency union agree with the Lean reduction.
   The new node has source, full proof steps, the union of their dependencies, searches,
   split status, creation/blueprint/unit/chapter records and its Lean declaration.
   Replaced its flattened lean.statement field with the literal multiline signature
   from the delivered module, as the brief requires.

Second reading changed only report completeness and the new node's verbatim Lean
signature record; the Lean proofs and existing interfaces needed no repair. The result
remains a decomposition: one original hole closed, one strictly lower hole added,
net zero, and no claim of global module pruning.

Verification: `lcompile.py --all` compiled both delivered modules without warnings
(43.4 seconds and 10.5 seconds). A scratch copy compiled with `#print axioms`:
`exists_stalkDerivedExtensionComparison` uses only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` from open dependencies;
`homology_comparison` uses only `propext`, `Classical.choice`, and `Quot.sound`.
The scratch copy uses a separate snapshot of the sandbox compiled modules and is
outside the delivered lean/ tree.
