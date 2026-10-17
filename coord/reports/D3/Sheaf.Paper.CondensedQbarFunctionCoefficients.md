## What changed

Proved the remaining hole in `Sheaf.Paper.CondensedQbarFunctionCoefficients`, the private
`AlgebraicGeometry.ProEtale.sheafScalar_surjective` helper. All public statements and
constructed data are unchanged.

The new bounded-unit proof glues continuous functions on a finite coproduct and bounds
them by the finite compositum of the summand bounds. It then applies the proved general
`unit_iso_of_refinement` helper from
`Sheaf.Paper.ProEtaleSheafificationWcontractibleSections`. This helper accepts the finite
restriction-product comparison; its statement was read in full, including the affine and
weak-contractibility hypotheses and the concrete-category requirements. `import all`
makes this existing private proof helper available only to this proof.

For scalar surjectivity, lift the image of one at the terminal object through that unit.
`Mod.bijective_one_comp_hom` reduces equality of regular-module maps to equality after the
ring unit. The monoidal sheafification adjunction, naturality, integer linearity and
`toSheafify_naturality` give the required equality. The argument uses five proved private helpers,
including the completed scalar-surjectivity and restored bounded-unit helpers; none
introduces data.
Updated the node proof and dependency list to match this argument. Added proof imports
for finite-coproduct evaluation and `WeilConjectures.CategoryTheory.Sites.MonObj`.

The shorter-route searches used LeanFinder (regular-module maps and global sections),
Loogle (`"regular", "hom"`), the logged Mathlib grep, and local `rg`. They found the
ordinary sheaf-module unit equivalence but no replacement for this internal-module
statement. The library already supplies the needed internal-module image-of-one theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.sheafScalar_surjective`
(node `lem-weil-pbc-condensed-qbar-function-coefficients`).

Added 0 holes. There are no remaining `sorry` declarations in the delivered module and
no split-off modules. The existing public
`condensedQbar_canonical_coefficient_properties` and
`exists_condensedQbar_function_coefficients` now use the completed scalar-surjectivity
proof. Dependencies elsewhere may still contain holes; this is a local closure of the
assigned hole, not a claim that the whole target has no `sorry` dependencies.

Validation: the complete module compiles with `lcompile.py` (about 7 seconds). All new
imports were checked with `tools/import_direction.py may`. The proof covers empty
coproducts and empty schemes: the field supremum is the base field and the pointwise bound
has no points to check. No definitions, signatures, visibility, target statements or
consumer modules were changed; no change record or forced adaptation is required.

## No longer needed

Removed direct proof imports:
- `import all Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`;
- `import Sheaf.Paper.GeometricFieldProEtaleEvaluation`.

Removed these direct proof-dependency edges from the item's node:
- `lem-weil-pbc-point-lan-affine-evaluation`;
- `lem-weil-pbc-condensed-field-continuous-realization`;
- `lem-weil-pbc-geometric-field-proetale-evaluation`.

The scalar-surjectivity proof no longer needs `canonicalComponentArrow`,
`canonicalComponentArrow_terminal`, `pointComponentsEquiv_apply`,
`globalCoefficientIso_test` or `boundedComponentsIso`. The last two constructions remain
available in the construction module; the unchanged coefficient and geometric-fiber
construction still has its own dependencies. These are direct-edge/import removals; no
whole library module is claimed to leave the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The assigned file's earlier bounded-unit proof was disabled after the upstream sync and
referred to private component-map helpers also disabled in current source files. Merely
uncommenting it compiled against an older published artifact, but that would keep the
stale source dependency. This delivery replaces that proof completely. No disabled
helper is used.

The old DAG route through a point-Kan comparison is unnecessary here. The generic
sheafification helper already proves the needed unit isomorphism from finite-product
behavior, which bounded functions satisfy directly by taking finite composita. The
unit's own statement and proof steps in `dag/units/sk-thm-properbasechange.json` are
unchanged. No mathematical statement was disputed or weakened.

## Second reading by D3

1. Compared the delivered module with the repository version. Existing public declarations and target statements are unchanged byte for byte; only proof code, proof imports, explanatory comments, and the node proof/dependency metadata changed. Verdict: pass.

2. Compiled the complete module with `lcompile.py`, searched for forbidden constructs and `sorry`, and checked the three public declarations with `#print axioms`. The module compiles cleanly, contains no `sorry`, and the public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. Reviewed the finite-coproduct gluing and image-of-one arguments, including the empty-family case, and searched for duplicate library statements with `msearch.py` and local `rg`. The private intermediate lemmas are true, needed, and strictly smaller than the target; no new split-off statement or node is introduced. Verdict: pass.

4. Checked the proof from the target downward. The route uses the existing `unit_iso_of_refinement` helper and the finite-coproduct evaluation theorem, then the shortest available regular-module image-of-one argument. The unit route is preserved, and the removed old point-Kan/component imports and dependencies are listed above. Verdict: pass.

5. Compared the node proof and `proof_deps` with the Lean proof and confirmed the unit record remains unchanged. The node metadata follows the implemented route and retains the existing scalar-pullback, field-fiber, and sheafification dependencies. Verdict: pass.

Changed during second reading: added this review section only; no Lean code, declarations, or DAG statements were changed.
