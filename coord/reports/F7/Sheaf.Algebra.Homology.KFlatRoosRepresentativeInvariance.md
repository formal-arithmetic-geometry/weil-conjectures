## What changed

Filled six existing proof holes in
`Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance` without changing any
public declaration type, definition, or import. The underlying algebra map is
constructed sectionwise as an R-linear map; uniqueness follows by extensionality.
The tensor unit is constructed by the presheaf map p ↦ p tensor 1 followed by the
module sheafification unit, with naturality obtained from that adjunction's unit.
Tower structure compatibility is naturality of the given algebra structure.
The Roos differential-square equation follows by the two biproduct projections,
the chain-map equation for 1-s, and naturality of equality transports. The
augmentation law follows from tensor-unit compatibility with the algebra
transitions: sectionwise these preserve 1, so the product unit is killed by 1-s.
The Roos map equation follows from tensor transition naturality and a private, proved
product-map compatibility calculation. Scoped unused-section-variable linter
settings preserve the original public instance binders rather than removing them.

## Proved and sorry left

Closed six of the seven original holes, all under namespace
`SheafOfModules.KFlatRoos`:

- `algebraModuleMap_existsUnique`.
- `tensorUnit_existsUnique`.
- `structure_compatible`.
- `roosD_sq`.
- `augmentation_comm`.
- `roosMap_comm`.

One original hole remains unchanged, on node
`lem-pe-kflat-roos-representative-invariance`:

- `SheafOfModules.KFlatRoos.representativeInvariance`: still needs the levelwise
  K-flat scalar-extension comparison, the exact-product/cone quasi-isomorphism
  comparison, and the common K-flat roof argument described in its docstring.

Added zero holes and zero split-off statements. The private helpers
`tensorSecondMap_tmul`, `tensorUnit_levelMap`, `unitProduct_oneSubShift`, and
`productMap_oneSubShift` are proved. Server compilation passed without errors or warnings; the current-source
validation in this session completed in 20.0 seconds. This is a partial proof
delivery, not a claim that the representative-invariance theorem itself is proved.

## No longer needed

None. No imports, nodes, or modules are pruned: the unchanged remaining
statement still needs their existing dependencies and proof route. The new
private helpers are elementary naturality glue within the existing node.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The directly imported change-of-rings
dependency uses coincident site/coefficient universes, whereas this module allows
independent universes. The current library also provides
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients`; using it for the
remaining main theorem requires identifying its extension functor, after restriction
of scalars, with the recorded site tensor and then comparing the Roos maps. No
statement was changed to bypass that interface work. The module's original seven holes include construction laws as well
as the final representative-invariance theorem; this delivery closes six of
those construction laws. All existing docstrings and the unit route are retained.

The resumed dry run initially classified scoped `omit` commands around private
helpers as an interface change. These commands were replaced by scoped
unused-section-variable linter settings; the interface checker now reports no
changes, and the resulting file compiles cleanly.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
