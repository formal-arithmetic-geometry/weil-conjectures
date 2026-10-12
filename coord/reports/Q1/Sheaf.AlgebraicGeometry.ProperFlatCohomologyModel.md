## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_proper_flat_cohomology_model` by a
complete compiling proof from two strictly smaller components. Its existing signature
and docstring are unchanged. Both new modules are proof-only imports of the item.

`ProperFlatCohomologyData` constructs a bounded flat quasi-coherent model, with all
cartesian base-change comparisons, for any quasi-compact separated morphism and any
quasi-coherent relatively flat module. It needs neither properness nor finite presentation,
and makes no pseudo-coherence claim.

`ProperFlatCohomologyProperties` replaces a supplied universal model by a pseudo-coherent
model on the same affine open with the same degree bounds. It compares pullback homology
with the supplied complex, rather than asserting higher-direct-image comparisons itself.
The item's proof composes these isomorphisms with the first component's comparisons.
The existing node's proof and proof dependencies now record precisely that composition.

All three modules compile via lcompile.py. The dry run passes; nothing was pushed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_proper_flat_cohomology_model`
(node `lem-pc-proper-flat-cohomology-model`).

Added two holes, each in its own module, with source and complete proof in words:
- `AlgebraicGeometry.Scheme.Modules.exists_proper_flat_cohomology_model_data`
  (node `lem-pc-proper-flat-cohomology-model-data`).
- `AlgebraicGeometry.Scheme.Modules.proper_flat_cohomology_model_properties`
  (node `lem-pc-proper-flat-cohomology-model-properties`).

This is a decomposition, not a sorry-free geometric proof: one hole closed, two added,
net minus one. No sorry remains in the item itself. The new theorems are stronger, distinct
parts of the construction and approximation argument, not renamed copies of the item.

## No longer needed

No original public import was removed: each supports the existing statement. The proof
imports only the two new component modules.

The item's former direct proof dependencies are now replaced:
`pqf-lem-proper-basic`, `lem-pc-affine-sections-flat-over-base`,
`lem-pc-cohomology-sections-affine-base`, `lem-pc-affine-vanishing`,
`lem-pc-flat-bounded-complex-descent`, and `lem-pc-coherent-hi`.
The affine and descent ingredients are still relevant within the new components' proofs,
so they are not claimed globally pruned. `Sheaf.AlgebraicGeometry.ProperBasic` is not needed
as an import: properness supplies separatedness through Mathlib instances. The source
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` cannot be
imported here: it imports ProperFlatCechModel, which imports this item. No library-wide
module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not directly give a bounded sheaf complex on an affine base:
the missing glue includes the finite alternating section complex, arbitrary-base
comparison, and the passage from Noetherian approximation to a model with prescribed
bounds. Each existing dependency's statement was inspected; the affine flatness statement
is a Mathlib composite rather than a geometric model-construction theorem.

The proposed proper-coherence dependency is in FiniteFreeComplex, an importer of this
item, so using its module would be circular. Likewise import_direction.py rejects importing
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`: that module already reaches this
item. The approximation part must ultimately avoid that source-library circularity.

A draft claim that every bounded flat quasi-coherent complex computes proper cohomology
was discarded. The delivered replacement theorem requires the universal comparison and
may replace the complex; it does not assume unrelated complexes have the same cohomology.
The empty source and d=0 cases were checked against both proof sketches. For d=0 the
universal vanishing gives Tor amplitude [0,0], so the replacement is finite projective in
degree zero; the empty-source case permits the zero complex. No claim depends on a
positive fibre dimension or a nonempty inverse image.

The unit route is retained: finite affine Cech construction, followed by the Noetherian
approximation argument. Source pages checked:
[0A1D](https://stacks.math.columbia.edu/tag/0A1D),
[0A1H](https://stacks.math.columbia.edu/tag/0A1H),
[0B91](https://stacks.math.columbia.edu/tag/0B91), and
[068V](https://stacks.math.columbia.edu/tag/068V).
Lean Finder, Loogle and grep found no direct replacement; LeanSearch returned a service
error, recorded as unavailable.

## New nodes

`lem-pc-proper-flat-cohomology-model-data`: the general qc-separated construction without
properness, finite presentation or pseudo-coherence. Its module is
`Sheaf.AlgebraicGeometry.ProperFlatCohomologyData`.

`lem-pc-proper-flat-cohomology-model-properties`: the approximation/replacement step for
an already supplied universal model; its conclusion compares D and C after each pullback.
Its module is `Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties`.

No definitions or existing statements were changed, and no forced adaptations or change
records were needed.

## Second reading by Q1

1. **Interface: PASS.** Compared the item with the repository by `diff -u`, and
   independently compared the entire existing theorem signature byte for byte: identical.
   The existing docstring is also identical. Only two plain proof imports and the proof
   body changed. The other two modules are new; no existing definitions, instances,
   statements, visibility, or file-level options changed. No change record is needed.
2. **Kernel checks: PASS with the declared holes.** Independently compiled all three
   modules with `lcompile.py --all`: no errors or warnings. A scratch module importing
   all three ran `#print axioms` on all three declarations: exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The only delivered sorries are the
   whole proofs of the two named component theorems listed above. No definitions or
   forbidden trust mechanisms occur. The item's proof uses the supplied isomorphisms
   in the correct direction and composes them to the unchanged conclusion.
3. **Split statements: PASS as decomposition, not completed geometry.** Read both
   signatures, docstrings, nodes, and their ingredients. The first isolates the finite
   alternating affine-cover construction and drops the approximation claim and its
   properness/finite-presentation assumptions. The second assumes that construction's
   universal comparison and isolates pseudo-coherent replacement on the same U and
   in the same bounds. Neither is a renamed copy of the item. The zero sheaf, empty
   inverse image, d=0, identity base change, and arbitrary nonflat affine base change
   fit the arguments. For the replacement, vanishing above d follows from hcomp;
   vanishing in negative degrees follows separately from the connectivity of the
   derived direct image of a sheaf. Thus the supplied comparison only at natural
   degrees suffices. Standard fibre products have injective resolutions because
   scheme module categories are Grothendieck; this is a mathematical fact, even where
   the library requires an explicit instance. Finite projectives on the affine U
   suffice: pseudo-coherence asks for a bounded-above finite-free representative,
   not that D itself be globally finite free.

   Checked the source claims against Stacks [0A1D](https://stacks.math.columbia.edu/tag/0A1D),
   [0A1H](https://stacks.math.columbia.edu/tag/0A1H),
   [0B91](https://stacks.math.columbia.edu/tag/0B91), and
   [068V](https://stacks.math.columbia.edu/tag/068V). Independently searched with Lean
   Finder for `finite affine cover alternating Cech flat modules universal cohomology
   base change`, Loogle for `DerivedCategory, Module.Projective` (zero hits), and grep
   for Tor-amplitude/perfect direct-image terminology, then read the closest Sheaf
   and upstream declarations. No direct usable replacement or quick closure of either
   component was found.
4. **Route and pruning: PASS.** Read `dag/units/sk-thm-picard-coherence.json`: the
   finite affine Cech construction followed by Noetherian approximation is retained;
   the unit's `realized` arrays are empty and this delivery does not change them.
   All original public imports serve the signature; both added imports serve only
   the proof and are plain imports. The report lists all six old direct proof
   dependencies as replaced, while making no unsupported global pruning claim.
   Independently traced the actual import graph: both PerfectDirectImageBaseChange
   and upstream FiniteFreeComplex reach this item, so importing either would be
   circular. The component nodes record the mathematical ingredients still needed
   for future proofs; they are not claimed to have already been formally applied.
5. **DAG agreement: PASS.** The item's two proof dependencies are precisely the two
   component theorems called by the Lean proof. Its proof and proof_origin describe
   construction, replacement, and composition. Both new nodes have matching Lean
   statements, source, proof steps, dependency union, searches, creation record,
   chapter, unit, blueprint provenance, and module/declaration records. No statement
   fields of an existing node are changed.

Second reading changed only this report: added the independent checks, edge-case
reasoning, and explicit import-cycle verification. No Lean or node repair was needed.
The accounting remains one original hole closed and two holes added (net minus one);
this delivery is a reviewed decomposition, not a sorry-free proof of proper cohomology.
