## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.etaleOriginScalarProjectionSquare`
by a counit-transpose argument. The theorem's signature is unchanged. It imports the
new proof module `Sheaf.Paper.EtaleOriginScalarPullbackSquare`.

`Sheaf.Paper.EtaleOriginScalarPullbackData` constructs the ambient site/direct-image comparison and its inverse
mate from the existing specified maps. `originMate_app` identifies its bounded-below
components with `properOriginMateIso`, using the proved fixed-coefficient inclusion
formula in `ProjectionComparisonEtaleProEtale`. `originMate_counit` proves the counit
identity. It also packages the existing tensor comparison as the natural isomorphism
`originTensorComparison` and proves its component formula.

In the item, `scalar_restriction_counit` specializes the ring-sheaf change adjunction
to the B-geometric counit. `scalar_counit` composes it with the scalar-extension mate
counit identity. `etale_projection_counit` computes the transpose of the actual
projection arrow, including the canonical constant-coefficient pullback map.
After transposing the claimed equation, the local pullback/tensor square and the two
naturality equations identify both composites. The bounds are used only to identify
the two included direct-image mates, with no bound imposed on scalar extension of
the target direct image.

Verification: all five delivery modules compiled through `lcompile.py`. The final
item compiled without warnings or errors in 19.6 seconds. The temporary data
profiler check completed in 14.1 seconds, with no slow declaration; that probe
and the separate counit-helper probe were removed. The original theorem signature
was checked verbatim against the shared source. All node attachment signatures
match their Lean files, and all lines have at most 100 characters.

## Proved and sorry left

Closed the item's one hole, `AlgebraicGeometry.ProEtale.etaleOriginScalarProjectionSquare`
(node `lem-fix-etale-origin-scalar-projection-square`), from a strictly local
left-adjoint normalization statement and the existing adjunction identities.

Proved `AlgebraicGeometry.ProEtale.etaleOriginScalarPullbackSquare` by expanding
the published tensor comparison and applying two tensor-free coherence cubes.
Its etale tensor face is the already proved `scalar_tensor_pullback_square`.

Added two holes, each in its own module:

- `AlgebraicGeometry.ProEtale.etaleOriginRestrictionPullbackCube`
  (`lem-fix-etale-origin-restriction-pullback-cube`): realization and scalar
  restriction commute with geometric pullback; there is no extension or tensor.
- `AlgebraicGeometry.ProEtale.etaleOriginExtensionPullbackCube`
  (`lem-fix-etale-origin-extension-pullback-cube`): realization and scalar
  extension commute with geometric pullback; there is no restriction or tensor.

These are separate faces of Step 4 of the original plan, on arbitrary unbounded
base inputs and arbitrary morphisms. Neither is the projection square under a new
name or merely its transpose. Their docstrings provide the ordinary coefficient
comparison, representative calculation and descent argument.

This delivery is a decomposition: one upper hole closed and two lower holes added,
net one added hole. The item has zero holes left; the delivery has two holes total.
All other new theorems and all private helpers are proved; definitions contain no
holes and select no arbitrary data from unproved mere existence.

## No longer needed

The item no longer directly imports `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale`.
The new data module still imports it with `import all` to reuse its proved private
fixed-coefficient inclusion formula, so the module itself is retained and no module
is claimed pruned.

The final argument does not specialize `projection_comparison_etale_proetale` and
does not call `proEtaleScalarMateNormalization`: it proves the requisite counit
identities directly from the ring-sheaf change adjunction and the defining projection
formula. The scalar-normalization theorem node is removed from the item's proof dependencies.
The generic projection-comparison node remains a dependency of the new data node
because its module supplies the proved inclusion helper; it is not claimed pruned.
The local normalization proof reuses the existing etale scalar/tensor pullback
identity rather than introducing another tensor normalization obligation.
The geometric inverse-image constant-module and general tensor-pullback inputs
are not direct dependencies of the final assembly. The unit's `realized` lists are empty and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan's passage from the generic fixed-coefficient projection square
to the intrinsic scalar comparison requires a substantive local tensor/pullback
normalization. Neither the generic projection comparison nor the scalar-mate
normalization alone identifies these intrinsic realization maps. This step is now
separated into two tensor-free realization cubes and a proved formal assembly.

The rework row was read before copying the current item. The current item exists
and is retained with its declaration and attachment. No quarantined module is
withdrawn and no source-library declaration is modified.

The local normalization is checked on zero rings, identity morphisms, the zero
complex and empty schemes: the balanced tensor/unit identities still apply; the
statement adds no nontriviality, flatness or boundedness hypothesis.

## New nodes

`def-fix-etale-origin-scalar-pullback-data`: real ambient mate and inverse-mate
constructions, scalar and tensor pullback composites, and the natural tensor
comparison. The bounded-below component, counit and tensor-component formulas
are proved. No data are chosen from mere existence.

`lem-fix-etale-origin-restriction-pullback-cube`: the restriction-only face of
intrinsic realization and geometric pullback, with inverse realization/restriction
maps at the endpoints. Its source is the sectionwise restriction/direct-image
comparison and geometric adjunction conjugation (Stacks 03EL, 0D6D, 07A6, 0E48).

`lem-fix-etale-origin-extension-pullback-cube`: the extension-only face, with
inverse site/scalar maps at its endpoints. Its source is the ordinary balanced
tensor comparison descended on flat-term K-flat representatives (Stacks 06YY,
0D6D, 07A6, 0E48).

`lem-fix-etale-origin-scalar-pullback-square`: proved combination of the two
cubes with the existing etale scalar/tensor square. The two inverse scalar/tensor
comparisons are canceled using their isomorphism identities.

Lean Finder, Loogle and Mathlib grep searches are recorded for the new nodes.
The underived pullback composition and free-module pullback results found by
Lean Finder do not identify these specified derived realization maps. The
etale/pro-etale scalar cube and intrinsic realization/restriction direct-image
cube were read and compared before stating the missing combined faces.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
