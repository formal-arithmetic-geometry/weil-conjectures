## What changed

Proved `CategoryTheory.perfectRingHom_tensorDual_degree_map_exists` with its exact original
signature and docstring. The construction evaluates the actual dual projection, forms the
signed rank-one map on the unique object's sections, and descends the bilinear family
through `SheafOfModules.tensor_bilinear_universal`. The specified Hom product and the total
tensor coproduct then assemble the map. Their factorization equations prove off-diagonal
vanishing and the exact diagonal formula, including its degree transport.

All construction helpers are private and fully proved in the assigned module.
The returned delivery's duplicate `ringHomComplex_isLimit` and `slice_unique`
declarations are removed. The assembly calls `homComplex_isLimit` directly.
The linearity proofs eliminate the slice object and its unique arrow directly;
there is no separate slice-uniqueness theorem or imported private declaration.
The unused `homPointLift_eval` helper is also removed.
`Sheaf.Algebra.Homology.HomComplex` additionally exposes its already-proved selected-product
property as `CategoryTheory.homComplex_isLimit`. No existing definition, signature, proof,
or import of that module changes. Its node records the additional API declaration.
The item node's proof, proof dependencies, and proof origin describe the construction.
Change record: `coord/changes/hom-complex-product-property-api.md`.

The point-site restrictions are constructed explicitly. The dual evaluation is packaged behind a small private interface;
the new generic API and scoped transparency settings keep the selected Hom-complex
witness folded during the assembly. No compile limit was changed and the proof remains in one module.

Searches: LeanFinder returned generic tensor-complex constructors; Loogle returned
`TensorProduct.lift`; grep returned `HomologicalComplex.mapBifunctorDesc` and its inclusion
formula. Reading the existing sheaf tensor bilinear universal property supplied the
required descent step. No new mathematical obligation or split-off theorem is needed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.perfectRingHom_tensorDual_degree_map_exists`
(node `lem-pc-perfect-ring-hom-tensor-degree-map`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered Lean module: 0.
There are no split-offs. The construction works for arbitrary complexes, including zero
objects and the zero ring, without finite generation, boundedness, or projectivity.

Validation: the complete proof compiled through `lcompile.py`. A direct `#print axioms`
reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the proved theorem.
The delivery tool performs the final single-file compilation, axiom probe, and preflight.

## No longer needed

Removed two redundant direct proof imports:
`Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`, and
`Sheaf.Algebra.Homology.PerfectRingDualTermFlat`.
`Sheaf.Algebra.Homology.HomComplex` remains a proof import for its new generic product API.
The removed imports' required definitions remain visible through the unchanged public import of
`Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition`.

The direct proof dependency `def-pc-perfect-rhom-base-change-map` is replaced by the
existing `def-pc-ring-hom-extension-shared-definitions`: the proof uses the shared category,
projection, and evaluation, not derived scalar-extension data. The dual object definition
attached to `lem-pc-perfect-ring-dual-term-flat` is still needed, but its flatness theorem
is not used. No mathematical node or module is claimed to become globally unreachable.
No dependency from a realized unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned construction is valid as stated. The sheaf tensor universal property already
has a proved declaration in
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`; there is no need
to split that step again. It is used as a proved generic tool and is now named in the
node's proof dependencies. The unit route and all existing mathematical statements are unchanged.
The original full proof passed a direct compile and axiom check, but the delivery probe
exposed a slow specialization of the selected product property. The generic API addresses
that conversion at the definition's source rather than introducing any new proof hole.

The return at `f980e9ff2` correctly identified duplicate private declarations in
the submitted module. Those declarations are now absent. The generic public
`homComplex_isLimit` API is used directly rather than through another ring-site
specialization, and the two linearity proofs use structural elimination rather
than reintroducing the existing private slice theorem. The existing duplicate
helpers in other library modules are unchanged. The unused local
`homPointLift_eval` declaration is removed as well. Both delivered modules
compile against the current published build through `lcompile.py --all`.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
