## What changed
The original target signature and docstring are unchanged. Its proof explicitly supplies
`canonicalResolutionDerivedIso F I`, then proves its conjunction from two canonical
transport obligations. This is a decomposition, not a completed proof of the mathematics.

Added modules:
- `Sheaf.CategoryTheory.CanonicalResolutionDerivedIso`: explicit augmentation, derived-unit,
  and map/extension constructions, with no proof holes in data.
- `Sheaf.CategoryTheory.CanonicalResolutionHomologyComparison`: the ordinary homology identity
  for this canonical comparison, with a complete natural-language proof.
- `Sheaf.CategoryTheory.CanonicalResolutionCompositeUnitComparison`: the composite unit identity
  for this canonical comparison, with a complete natural-language proof. Retains the original
  worker's kernel-checked private `resolutionDerivedIso_comp` calculation.

The target imports the two new theorem modules with plain `import`. New modules publicly
import only the declarations their signatures and definitions need. The composite comparison
also imports the ordinary comparison as its stated proof dependency.

## Proved and sorry left
Original hole closed: `CategoryTheory.exists_grothendieck_resolution_unit_comparison`.
New holes added:
- `CategoryTheory.resolution_homology_transport`, node
  `lem-pc-canonical-resolution-homology-comparison`.
- `CategoryTheory.resolution_composite_unit_transport`, node
  `lem-pc-canonical-resolution-composite-unit-comparison`.

No other holes remain in the delivered files. In particular, the unused
`resolutionDerivedIso_comparison`, `resolutionDerivedIso_homology`, and
`mapExtendIso_comp_hom` holes from the first worker were removed.

One of one original theorem bodies is closed, with two strictly smaller transport theorems
split off: net holes closed minus added = -1. This is a decomposition and is not reported as
net proof progress. The explicit constructions and private `resolutionDerivedIso_comp` have
only standard axioms. The two new transport obligations and the target depend on `sorryAx`,
which is explicitly allowed for the remaining named obligations.

## No longer needed
Removed direct proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle` and
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`: both remain accessible through
`GrothendieckComposablePair`, which the target's statement needs. These removals therefore
prune no modules from the target import closure.

All five old direct proof dependencies are replaced by the explicit construction and the two
transport nodes: `def-sp-composite-acyclicity`, `def-sp-injective-resolutions`,
`lem-sp-derived-functor-single-identification`, `lem-sp-derived-well-defined`, and
`lem-sp-grothendieck-edge-maps`. They are still used below the new nodes, as appropriate;
none is claimed globally unnecessary. No unit step or chapter route was pruned.

## Where the brief, the DAG or earlier work was wrong
The received report claimed closure while adding five undocumented private holes and no nodes.
The two key transport lemmas quantified over any isomorphism e, although their equations hold
for the canonical comparison. For the identity functors on rational vector spaces, X a nonzero
injective vector space, and n=0, replacing the canonical comparison by its negative changes
the right hand side of the ordinary homology identity by a sign, while leaving its left hand
side unchanged. Thus the arbitrary-e assertion is false. The same sign change invalidates the
arbitrary-e composite identity when G is the identity. This repair removes those false statements
and substitutes the explicitly constructed comparison, without changing any existing statement.

The unit `sk-thm-picard-rr` has empty realized fields in the repository. This item is below that
unit's route; those inherited fields and every existing unit/chapter record are unchanged.

## New nodes
`def-pc-canonical-resolution-derived-iso` records the explicit augmentation/unit/map-extension
construction in `CanonicalResolutionDerivedIso.lean`; its auxiliary definitions implement its
successive factors. It chooses no data from an unproved existence theorem.

`lem-pc-canonical-resolution-homology-comparison` states only the ordinary homology component
for the fixed canonical comparison. Its proof follows comparison of injective resolutions,
naturality of the unit and quotient homology, and cancellation of extension comparisons.

`lem-pc-canonical-resolution-composite-unit-comparison` states only the composite component
for that comparison. It reduces to the ordinary component for GF, the proved unit calculation,
and degreewise map/extension compatibility. No new statement repeats the paired existential
target. Each new theorem lives in its own new module and has its source and full proof in words.

New searches used different wording from the first worker: LeanFinder, Loogle, source grep,
and LeanSearch (unavailable). Source-library `PlusSingle` and `Grothendieck` were read, and
whole-library searches found no existing version of these prescribed-resolution identities.
Stacks Tags 015M and 015N were read online; derived.tex was downloaded into the item scratchpad.
No change record is required: no existing declaration, definition, visibility or public import
was altered.

## Second reading by F3
1. Compared the delivered target with the repository using diff: its existing declaration
   signature is byte for byte unchanged. Only its proof and plain proof imports change.
2. Compiled all four files through lcompile.py in import order, without errors or warnings.
   Checked every delivered file for forbidden declarations and hollow definitions. Axiom probes
   show only propext, Classical.choice, Quot.sound and the two explicitly reported sorryAx holes.
3. Rejected the arbitrary-e statements using the degree-zero sign counterexample above. The
   replacement obligations fix the canonical e and are true by their documented naturality
   arguments. Checked n=0, zero objects, and identity functors; there is no positive-degree
   hypothesis or division. The original worker's three unused holes were removed. Searched
   Mathlib and the source/library using new wording before creating the replacement nodes.
4. The target now opens its existential, constructs the witness from existing proved tools,
   and reduces each conjunct separately. Every old direct proof dependency and removed import
   is accounted for above. This keeps the resolution/unit route of the node and changes no
   unit realized field or chapter route. No claim of net proof progress is made.
5. Read the new node statements against the Lean signatures, and set the parent proof and
   proof_deps to its actual construction-and-two-identities proof. New nodes include source,
   complete proof steps, search records, creation/blueprint fields and exact Lean statements.

Second reading changed: removed five private undocumented holes including two false universal
transport statements; retained the real explicit construction and proved composition-unit
calculation; introduced two correctly restricted public obligations and three documented nodes;
removed redundant imports; corrected the report's progress claim and added this review.
