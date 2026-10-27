## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_residue_module_tensor_homology` in
`Sheaf.Paper.ProEtaleResidueModuleTensorHomology`, preserving its statement verbatim.
The private construction gives the annihilated module an actual quotient-ring action,
extends that action along the constant-ring sheafification unit on the same additive
sheaf, and proves that scalar restriction recovers the original module. No data is
chosen from an unproved existence statement.

The proof forms additive scalar extension, uses the proved natural scalar-tensor
cancellation comparison, reflects exactness through faithful exact scalar restriction,
and tensors over the constant residue field using its proved module-flatness theorem.
It works on `P.sc i`, so needs no boundedness, K-flatness, or sectionwise homology
vanishing. The only new declarations are proved private helpers in the item module.
Updated the existing node's proof, proof dependencies and proof origin to this route.
No public definition or statement changed; no consumer adaptations or change records
are needed. The unit's realized route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtale_residue_module_tensor_homology`
(node `lem-sf-proetale-residue-module-tensor-homology`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
Split-off statements: 0. This is a proof, not a decomposition.

Validation: the remote compiler accepted the proof in 24.8 seconds;
`#print axioms AlgebraicGeometry.Scheme.proEtale_residue_module_tensor_homology`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. Every proof import
was checked for an import cycle with `tools/import_direction.py may`. The public
statement was compared with the repository text and is identical.

## No longer needed

Removed these proof imports and their direct planned dependencies:

- `Sheaf.Paper.ProEtaleSheafificationTensorComparison`
  (`lem-sf-proetale-sheafification-tensor-comparison`): the existing natural
  scalar-tensor cancellation theorem supplies the required intrinsic comparison.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology`
  (`lem-exc-constant-field-sheaf-tensor-cohomology`): flatness and exactness of the
  three-term complex suffice, so a cohomology isomorphism is unnecessary.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: neither derived direct
  image nor its six-functor coefficient machinery is used in this ordinary tensor proof.

The original module-sheafification interface and sheaf tensor dependencies are still
used. The construction also uses the scalar-unit interface from
`ProEtaleConstantModuleEncoding`; flatness comes directly from `ConstantFieldFlat`.
No module is withdrawn, and no source-library declaration is removed or weakened.
The removals concern this item's proof route; other consumers may still need those modules.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid but asked for more comparison machinery
than needed. The proved scalar cancellation and constant-field flatness interfaces
already give a shorter exactness argument. In particular, a section ring of the
constant field sheaf need not be a field; the proof uses the existing local flatness
result rather than making that claim. The current blueprint residue-test converse
uses exactly this flatness argument. Empty schemes and zero modules remain covered;
maximality is used only to provide the quotient field structure.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
