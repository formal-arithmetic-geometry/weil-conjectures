## What changed

Proved `AlgebraicGeometry.Scheme.finiteExtensionReductionConeBound` in
`lean/Sheaf/Paper/FiniteExtensionReductionConeBound.lean`, preserving its full statement,
public imports, and completed coefficient category. All added declarations are private and
proved; the existing abelian instance is unchanged.

The proof reuses the coefficient resolution and tensor formulas already proved in
`AdicReductionCohomologySequence` and `AdicReductionTriangle` through proof-only `import all`.
It identifies their multiplication map with the specified scalar action, constructs a
functorial termwise-flat K-flat resolution using the existing independent-coefficient flat
cover, and descends the natural SES connecting map through quasi-isomorphism localization.
The normalized derived adjunction unit is the second arrow. Exactness in degrees q and q+1
then gives the interval [a-1,b]. The DAG proof and dependencies now describe this route.

No existing definition, public declaration signature, source-library file, consumer, or unit statement
is changed. No new public interface or split-off lemma is introduced.

`coord/changes/E9-finite-extension-cone-proof-attributes.md` records the proof-local
irreducibility and zero-object notation commands requested by the preflight scanner.
They have no exported effect. The explicit `CoefficientExtensionFinite` import is kept
to preserve the unit route; its public reexport also remains unchanged.

Validation: the final complete module compiled through `lcompile.py` in 21.5 seconds.
The original theorem signature was compared verbatim modulo whitespace, with no change.
There are zero `sorry` tokens and no lines longer than 100 characters.
The theorem's axiom print lists `propext`, `Classical.choice`, `Quot.sound`, and the
pre-existing `sorryAx` inherited from imported declarations; the delivery adds no hole.
The large coefficient datum and constant-module comparison are locally irreducible, with
all comparisons made through their proved formulas. The homology-sequence index equality
is supplied explicitly as `rfl`. The flat-resolution and acyclic-tensor arguments
are proved generically before specialization. Scalar-section comparisons use typed maps
and direct equality chains, avoiding searches through the tensor construction.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteExtensionReductionConeBound`
(node `lem-cbc-finite-extension-reduction-cone-bound`).
Added 0 holes. Remaining holes in the delivered module: none.
This is a proof from existing declarations, not a decomposition.

## No longer needed

Removed the following proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Paper.SfCommonStageWeilCohomology`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The node no longer directly depends on
`lem-weil-pbc-constant-module-section-properties`, `lem-pur-quasi-iso-cone-acyclic`,
`def-pc-kflat-complex`, `lem-pc-tensor-mapping-cone-iso`,
`lem-pur-derived-change-of-rings`, `def-pc-sheaf-restrict-scalars`,
`def-pc-tensor-complex-sheaves`, or `def-weil-derived-cohomology-sheaves`.
The reused coefficient, tensor, and derived-adjunction constructions retain the needed
transitive dependencies. The explicit augmentation-cone criterion and tensor-cone
isomorphism route is replaced by the short exact sequence of flat complexes and Mathlib's
natural SES triangle. Removed the corresponding two obsolete top-level `tool_uses`
approvals (`lem-pur-quasi-iso-cone-acyclic`, `lem-pc-tensor-mapping-cone-iso`).

No module is withdrawn, and no adopted source-library declaration is removed. This report
claims pruning of the item's direct imports and proof dependencies, not disappearance of
those modules from every other target's import closure.

## Where the brief, the DAG or earlier work was wrong

The statement and its uniformizer-resolution route are correct. The plan need not repeat
the tensor-cone argument: the library now already proves the needed completed coefficient
resolution and tensor short exactness. The remaining naturality assertion requires a
functorial flat resolution and localization of the connecting natural transformation;
objectwise choices of distinguished triangles alone would not provide the stated natural
transformation. The proof handles this explicitly.

Edge cases checked in the argument: n=1 uses (n-1)+1=n from n>=1; the zero complex and a=b
need no extra assumption; the boundary q=a-1 is correctly allowed to have nonzero cohomology.
No false statement or definition repair was found. The preflight command scanner
requires a change record even for the proof-local attributes; that record is included.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
