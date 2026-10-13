## What changed
The original theorem `AlgebraicGeometry.exists_generic_fibre_birational_hypersurface_model`
keeps its exact original signature and is reduced to two strictly separate arguments.
The new proof-only imports are
`Sheaf.AlgebraicGeometry.GenericFibreHypersurfaceFunctionFieldModel` and
`Sheaf.AlgebraicGeometry.AffineBirationalOfFractionRingEquiv`.
The first constructs the polynomial and a compatible fraction-ring isomorphism, without
asserting birationality or common opens. The second is the general affine fraction-ring
criterion, without constructing an equation or asserting geometric integrality.
The original node's proof, proof_deps and proof_origin now record this reduction.
No existing definition, statement, signature or public import was changed.

## Proved and sorry left
Hole closed (one): `AlgebraicGeometry.exists_generic_fibre_birational_hypersurface_model`.
Its proof combines the two intermediate results; it is not axiom-free yet.
Holes added (two):

- `AlgebraicGeometry.exists_generic_fibre_hypersurface_function_field_model`, node
  `lem-sbc-generic-fibre-hypersurface-function-field-model`.
- `AlgebraicGeometry.birationalOver_of_fractionRing_equiv`, node
  `lem-sbc-affine-birational-fraction-ring-equiv`.

This is a decomposition, not a completed proof: one upper hole replaced by two lower
holes, net -1 in the target import closure before any global pruning calculation.
No other holes are left in the delivered modules. Each new hole is a named public theorem
with a complete natural-language proof and source in its docstring and matching node.
No data is selected from an unproved existence theorem inside a definition.

## No longer needed
None: the original node had no proof_deps and none of the original five public imports
can be removed without affecting the interface. No old node or module is pruned.
The rejected first-worker helpers and their two unlanded nodes were removed, rather than
counted as pruning of the library.

## Where the brief, the DAG or earlier work was wrong
The first worker's `generic_fibre_hypersurface_birational_of_equation` was false. Take
S = Spec Q, X = Spec Q with identity structure map, n = 1 and P = 0. The candidate
hypersurface is the affine line; both fibres are geometrically integral, but their
fraction fields are Q and Q(t), so they cannot have isomorphic nonempty dense opens.
The helper had no hypothesis linking its equation to the given source's function field.
Its claimed natural-language argument therefore could not prove its actual statement.
The equation-only helper by itself supplied no such link. Both helpers also lacked
required docstrings, complete signatures in their nodes, statement dependencies,
proof steps and search records. The item's original node was not updated.
The original node's proof step was marked non-elementary, contrary to the first report.

## New nodes
`dag/nodes/sec-smooth-base-change/lem-sbc-generic-fibre-hypersurface-function-field-model.json`
records the field-generator/polynomial construction from Tag 0559, with a compatible
fraction-ring isomorphism. The corresponding new module is
`Sheaf.AlgebraicGeometry.GenericFibreHypersurfaceFunctionFieldModel`.

`dag/nodes/sec-smooth-base-change/lem-sbc-affine-birational-fraction-ring-equiv.json`
records the general affine fraction-field criterion from Tag 0552. The corresponding
new module is `Sheaf.AlgebraicGeometry.AffineBirationalOfFractionRingEquiv`.
No change record is needed: no existing interface changed.

## Second reading by R3
1. Compared every delivered file to the repository. The original theorem's signature
   is byte-for-byte identical; only its proof and two plain imports changed. The two
   new statements are in their own modules. No existing data or public import changed.
2. Compiled all three modules with lcompile.py and checked the three declarations with
   #print axioms in a scratch copy. Only propext, Classical.choice, Quot.sound and sorryAx
   occur; sorryAx is accounted for by the two listed open intermediate theorems.
   There are no forbidden declarations or attributes, no definitions with sorry, and
   no unlisted holes. After replacing letI with have and installing local finite type
   of the source fibre by base change, the item compiles without warnings.
3. Rejected the false first-worker lemma using the point/affine-line counterexample.
   Read Stacks Tags 0559 and 0552 online. The replacement construction handles zero
   transcendence degree using equation T; clearing denominators uses a nonzero scalar
   of the integral base, so the generic quotient is unchanged. The replacement
   criterion needs integrality, finite type and base-compatible fraction-ring
   isomorphism; the point/line counterexample no longer satisfies its hypotheses.
   Its denominator argument works over an arbitrary affine base, even when its maps
   into the common field have kernels. Both replacements are true and strictly parts
   of the original argument. LeanFinder, Loogle and Mathlib grep searches were repeated
   with function-field, dense-open and primitive-polynomial terminology. LeanSearch
   was also attempted for both replacement statements and recorded as unavailable
   (Internal Server Error); repository
   searches and reading related field-basis, hypersurface-prime-criterion and curve
   modules found no existing declaration of either replacement statement. Neither
   remaining subproof can be closed in a few minutes using the available interfaces.
4. Checked the route from the target downward. The old proof_deps were empty, so the
   No longer needed list is complete. dag/units/sk-prop-normal-form.json has empty
   realized statement and step lists; the two replacements stay below the unit and
   preserve the same field-generator and common-open argument. Public imports occur
   only where used in statements; the item's new imports are proof-only.
5. Updated the original node to the actual two-step proof and two dependencies. Both
   new nodes have self-contained statements, sources, statement dependencies, proof
   steps, proof_origin, all three search kinds, creation and blueprint records, matching
   verbatim Lean signatures and the original chapter/unit. Verdict: valid decomposition,
   with two open subproofs and no claim of net proof progress.

Second reading changed: removed the false unlinked birationality helper and the vacuous
unlinked equation helper; replaced them with the compatible fraction-field construction
and general affine fraction-field criterion; restored original signature whitespace;
completed docstrings/node metadata/reporting and the actual original-node dependency list.
