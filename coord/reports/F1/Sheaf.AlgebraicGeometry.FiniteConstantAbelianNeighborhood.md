## What changed

Proved `AlgebraicGeometry.Scheme.finite_constant_abelian_neighborhood` with its original
signature unchanged. Its sole new proof import is
`Sheaf.AlgebraicGeometry.FiniteConstantLabelSubgroupNeighborhood`, which is also fully proved.
That module imports the existing proved finite-section tools in
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections` for its proof.

The proof lifts the finitely many zero, sum and negative sections onto one covering sieve,
chooses a member above the specified point, and restricts the original set chart compatibly
with the sheafification unit. The labels inject into the abelian group of sections and their
range forms an actual subgroup. A bijection with that subgroup transports its group structure
to the original finite label type. Naturality propagates the additive identities from the
terminal object to every object, giving the required abelian presheaf transformation.

Updated the original node's proof, proof dependencies and proof origin. Added one node for the
proved neighborhood lemma and two records for the existing proved tools used by it. No existing
statement, definition, public import, or target was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finite_constant_abelian_neighborhood`.

Also fully proved the new public declaration
`AlgebraicGeometry.Scheme.finite_constant_label_subgroup_neighborhood`
(node `lem-weil-pbc-finite-constant-label-subgroup-neighborhood`) and its private
`finite_label_sections_cover` helper. No holes were added and none remain in either delivered
module. This is a proof, not a decomposition into new holes: net holes closed is one.

Both modules compile without warnings. `#print axioms` for each public theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. All files compiled in import
order, and the final delivery dry run checks the mechanical requirements and all declarations.
The finite subgroup and its structure are actual constructions; the inverse of the bijection
is determined uniquely by the injective label map.

## No longer needed

The new proof removes these dependencies from the original node's proof route:

- `def-weil-pbc-geometric-stalks`;
- `lem-weil-pbc-sets-sheafification-geometric-stalk`;
- `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`.

Their associated tools in `Mathlib.CategoryTheory.Sites.Point.Basic`,
`Mathlib.CategoryTheory.Sites.Point.Skyscraper`, and
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` are not used by this argument. These modules may
remain reachable through other library imports; no claim of global unreachability is made.
The original module had only the statement import `Sheaf.AlgebraicGeometry.EtaleSheaves`,
which is still required. During import minimization, explicit proof imports of
`Mathlib.CategoryTheory.Sites.CoverLifting` and `Mathlib.Algebra.Group.TransferInstance` were
removed because the required declarations are already available through existing imports.
Removing `ConstantSheafSections` fails to resolve the finite-section theorem, so that proof
import is necessary. No unit statement or realized unit step is bypassed: the item is below
the unit's own steps in `dag/units/sk-thm-p1.json`.

## Where the brief, the DAG or earlier work was wrong

The original geometric-stalk argument is mathematically valid but unnecessary here. The
existing finite-section covering theorem yields closure of the labels under all three
operations directly, without constructing a geometric point or a common pointed refinement.
Stacks [Tag 03RU](https://stacks.math.columbia.edu/tag/03RU) was checked: it supplies definitions,
not this refinement theorem. The actual source of the shorter route is the already proved
`ConstantSheafSections` lemmas plus Mathlib's sheafification/localization compatibility.

Edge cases: empty S on an object containing x is excluded by local lifting of the zero section;
the cover chosen above x cannot be empty; its member has a point and therefore its empty sieve
cannot be covering. Disconnected members are allowed, since injectivity of constant labels
only requires that the empty sieve is not covering. No connectedness, nonemptiness of S,
Noetherian, or characteristic hypothesis is added. There is no error in an existing statement.

Searches ran through LeanFinder, Loogle, remote grep and local source reads. LeanSearch returned
an Internal Server Error and is recorded as unavailable. The source reads found the exact
finite-family lifting and label-injectivity tools, and the restriction isomorphism together
with its unit formula. Blueprint searches for finite constant objects and sheafification
localization found no duplicate of the added assertion.

## New nodes

`lem-weil-pbc-finite-constant-label-subgroup-neighborhood` records the fully proved local
set-chart assertion: the original finite labels inject into the terminal sections and their
image contains zero and is closed under addition and negation. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteConstantLabelSubgroupNeighborhood.lean`. The node includes
its complete proof and exact Lean signature; it adds no sorry.

`lem-weil-pbc-finite-constant-set-sections-cover` records the two existing proved declarations
in `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections`: simultaneous local
lifting of a finite section family and injectivity of labels on nondegenerate objects.
It adds no Lean file and no sorry.

`lem-weil-pbc-set-sheafification-localization-compatible` records Mathlib's existing
sheafification restriction isomorphism, its compatibility with the unit, and the direct
restriction identification `Sheaf.pushforwardOverMapIso`. It adds no Lean file and no sorry.
All three node files are under `dag/nodes/sec-proper-base-change/`. No change record is needed.

## Second reading by F1

1. Compared both delivered Lean modules against the repository versions; the existing target statement is byte-for-byte unchanged, with only its proof and the new supporting module added.

2. Compiled both modules with the launcher; there are no errors or warnings. The proof contains no forbidden declarations or `sorry`, and its axioms are restricted to the permitted standard axioms.

3. Checked the added subgroup theorem and its node: it is a strict intermediate closure statement, true by the finite-section lifting argument, with no new holes or restatement of the target.

4. Checked pruning and imports: the proof uses the finite-section route and keeps the unit route; obsolete geometric-stalk dependencies are removed from the node proof dependencies.

5. Checked DAG proof steps, dependencies, origin, and realized unit route against the Lean proof. Verdict: accepted.

Second reading changed only this report; no Lean proof repair was needed. Independent LeanFinder search with "finite set chart for a sheaf of groups becomes a subgroup of sections after restricting to a cover" found no duplicate intermediate theorem. The existing target docstring describes the older geometric-stalk route; its recorded DAG proof and this report describe the actual finite-section route. The original docstring and all existing signatures were preserved.
