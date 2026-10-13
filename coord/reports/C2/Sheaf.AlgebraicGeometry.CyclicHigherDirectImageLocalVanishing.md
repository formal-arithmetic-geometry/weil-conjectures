## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.CyclicHigherDirectImageLocalVanishing` with a complete Lean
proof from the proved abelian higher-direct-image/sheafification comparison and the
new cyclic derived-Hom/cohomology comparison. The original theorem signature,
visibility, and public imports are unchanged.

The proof constructs a covering zero-equalizer sieve by refining each etale object
with its affine cover and then the covers supplied by the original hypothesis.
It makes the zero presheaf endomorphism locally surjective, transfers this to its
sheafification, and uses the locally-surjective/epi criterion and `IsZero.of_epi_zero`.
Finally it transports zero across the existing higher-direct-image comparison.

Added one module `Sheaf.AlgebraicGeometry.CyclicDerivedHomCohomologyComparison`.
Its theorem concerns only comparison of geometric cohomology and free-representable
derived Hom, including reflection of zero under an etale restriction. It does not
assume local annihilation and does not conclude anything about higher direct images.
All new statement data are genuine expressions in the existing library; no new
definition or data chosen from an unproved existence theorem was introduced.

The two modules compile cleanly using lcompile.py. The original proof completes
without any internal sorry. The DAG copies describe the actual argument.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.isZero_cyclicHigherDirectImage_of_locally_zero`
(node `lem-sbc-cyclic-higher-direct-image-local-vanishing`).

Added one hole, the whole proof of the new public theorem:
`AlgebraicGeometry.Etale.exists_cyclicDerivedHom_cohomology_comparison`
(node `lem-sbc-cyclic-derived-hom-cohomology-comparison`).

This is a decomposition: one original hole closed and one strictly smaller
comparison hole added, for net zero holes before pruning. All affine refinement,
local vanishing, sheafification, and zero-object transport steps are proved.
There are no sorries left in the assigned module.

The remaining comparison is true also for e=0 (integer coefficients), e=1 (zero
coefficients), q=0, empty schemes, identity structure morphisms, and identity
restriction arrows. Extension by zero along an etale map is exact without qcqs
hypotheses; the projection from a fibre product is etale even for arbitrary h.
The cohomologyMap in the remaining statement lands in pulled-back coefficients,
exactly as in H; the canonical coefficient isomorphism preserves and reflects zero.

## No longer needed

Removed the proof import `Sheaf.Paper.SiteSheafificationSectionsLocal` and the
proof-dependency node `lem-weil-pbc-site-sheafification-sections-local` from this
item. Neither its local representatives nor its local-injectivity clause is used:
Mathlib's local-surjectivity criterion after abelian sheafification gives the
required consequence directly. This only prunes this item's dependency edge;
other targets may still use that module.

Retained `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` and its node
`sbc-lem-higher-direct-image-presheaf`: the proof explicitly uses its single-sheaf
comparison. Retained the affine-basis step and the etale-site definitions. Added
proof imports of the cyclic comparison and Mathlib Sites.LocallyBijective and
Sites.EpiMono. No other planned nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The existing abelian presheaf comparison is stated using derived Hom from a free
representable, whereas H uses geometric Sheaf.H on fibre products. The node's
first step silently treats the identification and its restriction compatibility
as already present in that declaration. They are not in its public signature.
The new node states precisely this missing bridge, separately from the actual
vanishing argument.

Read the module-coefficient analogue in the source FreeSheaf.lean: it computes
shifted Hom on a fibre product, but cannot serve directly for abelian coefficients;
it also imports the source module that depends on this item, so importing it here
would be circular. The existing RawRestrictedCohomologyNaturalIso concerns derived
sections and naturality in the structure morphism h with a fixed etale object U.
It does not state the geometric Sheaf.H comparison with restriction in U needed
here. The new lemma therefore is not a duplicate application of that theorem.

Mathlib SheafCohomology.Basic explicitly lists comparison with cohomology of a
restricted sheaf as a TODO. Semantic and type searches found no applicable
arbitrary-degree restriction comparison. LeanSearch returned Internal Server
Error and was recorded as unavailable. LeanFinder, Loogle, and grep searches ran
through msearch.py. Blueprint searches for cohomology presheaf, free abelian, and
restricted cohomology found no standalone comparison node; the new node refines
the existing higher-direct-image blueprint's first identification step.

Checked the source [Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8) and its
proof reference [Stacks 072W](https://stacks.math.columbia.edu/tag/072W). The former
states the geometric restricted-cohomology presheaf, while the latter computes it
with sections of an injective resolution. The free-representable interpretation
and exact etale restriction give the bridge's stated argument. The unit route
remains intact: the sbc higher-direct-image comparison is explicitly used.

## Earlier second reading (a previous round; superseded)

C2 reread the item node, the new comparison node, and both Lean modules. The original theorem statement is unchanged: arbitrary scheme morphism, natural numbers e and q, affine etale U, jointly surjective etale families, and the exact IsZero derived homology conclusion. The proof uses the existing higher-direct-image sheafification comparison, refines arbitrary etale objects by affine opens, and applies the hypothesis only to affine objects. The new theorem is strictly smaller: it supplies only an additive derived-Hom/cohomology equivalence and zero-reflection under restriction, without any local-vanishing or higher-direct-image conclusion. The unit route through the higher-direct-image presheaf comparison is retained. The unresolved comparison theorem is the sole named sorry and has its own node. The visible-interface change is recorded in `coord/changes/cyclic-higher-direct-image-local-vanishing-proof.md`.

## New nodes

`lem-sbc-cyclic-derived-hom-cohomology-comparison`, in
`dag/nodes/sec-smooth-base-change/`, states the additive geometric comparison and
its zero-reflecting restriction compatibility. Its Lean declaration is
`AlgebraicGeometry.Etale.exists_cyclicDerivedHom_cohomology_comparison` in the new
module `Sheaf.AlgebraicGeometry.CyclicDerivedHomCohomologyComparison`. It has a
source, complete proof in words in the docstring and node, actual search records,
and the same chapter/unit as the item. It is strictly the comparison part of the
argument. No interface change or forced adaptation is needed.

## Second reading by C2

1. **Repository comparison.** Compared the assigned module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof, proof-only imports, and namespace opening differ. The added comparison module and node are new delivery files, and the import change is recorded in the change record.

2. **Compilation and proof audit.** Compiled both sandbox modules with `lcompile.py --all`; both compile without errors. The assigned theorem has no `sorry`, and the only remaining `sorry` is the named comparison theorem in its own module. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC` declarations occur.

3. **Statements and split.** Checked the assigned theorem against its repository signature and checked the comparison theorem's edge cases and type. The comparison theorem is a strictly smaller bridge about derived Hom, cohomology, and restriction; it does not restate the local-vanishing target. Its docstring and DAG node give the source and proof plan, and no existing declaration duplicates it.

4. **Route and pruning.** The proof keeps the unit route through the abelian higher-direct-image/sheafification comparison. It uses affine refinement, local-surjectivity of the zero presheaf map, sheafification, and the epi/zero criterion. The obsolete site-sheafification-sections-local import and dependency edge are removed; the remaining imports are used.

5. **DAG agreement.** The item node's proof, dependencies, and origin match the Lean proof, and the new comparison node records its statement, source, proof steps, searches, and Lean declaration. The unit's realized route is unchanged.

Changed only the report during this second reading; no Lean proof repair was needed.
