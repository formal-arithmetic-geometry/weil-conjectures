## What changed

The original existence theorem is reduced to the coefficient-linear level comparison.
The scalar-extension tower and the extension of strict systems are constructed by
complete Lean proofs, using the existing normalized scalar and localized adjunctions.
Transition identity, composition and naturality are proved on the normalized units
or original extension summands. Additivity uses the additive evaluation functors.

The main module assembles the forward level maps into strict-system morphisms,
uses componentwise invertibility to construct the natural isomorphism, proves the
inverse generator equation by cancellation, proves the augmentation square by
localized adjunction extensionality on original summands, and lifts the natural
isomorphism degreewise to arbitrary unbounded complexes.

The pre-existing definitions and result structures are relocated unchanged to
SemilinearSliceScalarGeneratorsBasic and publicly reexported by the item. This
avoids an import cycle between data and construction proofs. The result theorem's
signature and all original data types, fields and definition bodies are unchanged.
All five Lean modules compile within 60 seconds each. The four supporting
modules took 16.6--23.3 seconds in the final batch, and the completed main theorem
compiled cleanly in 9.2 seconds. No debugging or profiler options remain.

No existing module other than the assigned item is edited. There are no current
direct Lean importers to adapt. DAG parents and the blueprint unit route remain.

## Proved and sorry left

Original holes closed: SheafOfModules.exists_semilinearSliceScalarGenerators (one).
It is proved from the strictly smaller level-comparison theorem, so this is a
decomposition, not a net proof of the original mathematical result.

New proved construction theorems:

- SheafOfModules.exists_sliceScalarTowerPresentation.
- SheafOfModules.exists_sliceSystemExtensionPresentation.

New holes added: SheafOfModules.exists_sliceScalarLevelComparison (one), in
Sheaf.CategoryTheory.SliceScalarLevelComparison, node
lem-sf-slice-scalar-level-comparison. This asserts the coefficient-linear component
isomorphisms and scalar identifications, normalized on generators, with the
forward level transition and naturality equations. It does not construct the
scalar towers or extension functor, a strict-system inverse, augmentation, or a
complex lift. The argument for all of those omitted parts is implemented here.
The new theorem has its source and complete proof in words in its docstring.

The delivery contains exactly one sorry, in that named public theorem. The item
has zero remaining sorries. Holes closed: 1; holes added: 1; net: 0. All definitions
are explicit constructions or unchanged original structures; none contains sorry.
The existing scalar-model theorem is used only through its stated normalized
model, not through an arbitrary uncharacterized choice of data.

## No longer needed

No mathematical node or module is claimed pruned. The coefficient-linear
comparison still needs the original ordinary tensor-generator result and the
sheafification local-section argument in its proof plan.

The original direct public imports of RingedSliceTensorGenerators,
SystemLevelLeftExtensionBasic and Mathlib.Algebra.Homology.Additive are carried
by the new Basic module and remain publicly available through it. The original
private imports Mathlib.CategoryTheory.Sites.PreservesSheafification and
WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal are removed:
the completed assembly and construction proofs use adjunction extensionality
instead. Their facts remain proof dependencies of the split level comparison,
so their modules are not withdrawn or claimed unnecessary in the full argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false, and no hypothesis or conclusion is
changed. The existing result structure is substantially larger than a single
levelwise tensor isomorphism. Two construction parts and the strict-system,
augmentation and complex assembly are now implemented separately.

Strict-system addition is supplied by the unique normalized abelian structure;
its componentwise formula must be used through additive evaluation, rather than
by definitional reduction. Likewise, scalar model objects are identified with
actual scalar extensions by the model's recorded equality, which must be
transported explicitly in generator formulas.

The scalar-model, scalar-coherence and scalar-generator nodes from
sk-def-sf-operations are reused as tools for the tower construction. They supply
the normalized actual scalar adjunction and its unit-tensor extensionality;
the present unit has no alternative declaration of that general interface.
The already-used localized module adjunction supplies the extension construction
and augmentation extensionality. No maintainer tool approval is edited here.

The new statements were checked on zero modules, zero coefficient rings,
identity and non-flat algebra maps, repeated levels, sites with multiple or no
arrows to U, and arbitrary complex degrees. The constructions use neither
flatness nor a globally generated-section assertion. The dependency graph of
the overlaid packet has no cycle and no missing node in its 255-node closure.

## New nodes

`def-sf-semilinear-slice-scalar-data` owns the unchanged data declarations moved
to the new Basic module. It asserts no existence theorem. The original node now
cites this definition as a statement dependency.

`lem-sf-slice-scalar-tower-construction` records the proved construction of the
scalar-extension tower from the normalized ordinary scalar adjunctions, including
all transitions, units, actual object identifications and additivity.

`lem-sf-slice-system-extension-construction` records the proved construction of
termwise localized extension as an additive functor on strict semilinear systems.

`lem-sf-slice-scalar-level-comparison` is the remaining coefficient-linear level
comparison. Its proof plan is original steps 1--6 after removing the extension
functor construction, which is now proved in its own module. It deliberately
omits the augmentation and all strict inverse and complex assembly.

Change record: coord/changes/semilinear-slice-scalar-data-relocation.md.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
