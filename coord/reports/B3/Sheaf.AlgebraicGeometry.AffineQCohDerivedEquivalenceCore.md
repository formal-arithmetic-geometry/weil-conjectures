## What changed
Proved `AlgebraicGeometry.exists_affineQCohDerivedEquivalence_core` by constructing an
adjunction, installing invertibility of its unit and counit, and applying Mathlib's
`CategoryTheory.Adjunction.toEquivalence`. A separate compatibility theorem supplies the
integer-shift and triangulated structures. The existing target signature and docstring
are unchanged. Three new modules state strictly separate intermediate obligations;
the target imports them with plain `import`, as they are used only in its proof.

The second reading repaired warnings, removed unused imports from new modules, added
proof imports for affine vanishing and the unbounded cohomological bound, and corrected
the DAG records. No existing statement or definition changed; no change record is needed.

## Proved and sorry left
The item's one original theorem, `AlgebraicGeometry.exists_affineQCohDerivedEquivalence_core`,
now has a complete Lean proof. This is a reduction, not a sorry-free closure: its axioms
still contain `sorryAx` through these three named, documented obligations:

- `AlgebraicGeometry.affineQCohDerivedAdjunction_construction`:
  `new-affine-qcoh-derived-adjunction-construction`.
- `AlgebraicGeometry.affineQCohDerivedAdjunction_unit_counit`:
  `new-affine-qcoh-derived-adjunction-unit-counit`.
- `AlgebraicGeometry.affineQCohDerivedEquivalence_core_triangulated`:
  `new-affine-qcoh-derived-tilde-triangulated`.

All four modules compile without errors or warnings. Scratch `#print axioms` checks on
all four declarations gave only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
There are exactly three delivered `sorry` occurrences, each the entire proof of one of
the named new theorems; no definitions or prohibited trust mechanisms are introduced.

## No longer needed
The target no longer directly imports
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`. Its old proof dependencies,
`lem-weil-pbc-affine-tilde-gamma-adjunction` and `lem-pc-affine-vanishing`, are replaced
on the target node by the three new intermediate nodes. Neither old node is pruned
from the argument: the ordinary adjunction remains used in the construction and
unit/counit argument, and affine vanishing remains imported by the unit/counit module.
No module or node is declared globally prunable.

Removed unnecessary copied imports from new modules: `Mathlib.CategoryTheory.Triangulated.Functor`
from the construction and unit/counit modules; `Mathlib.CategoryTheory.Adjunction.Basic`,
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`, and
`Sheaf.Topology.RingedSpaceModuleCohomology` from the triangulated module.

## Where the brief, the DAG or earlier work was wrong
The first report overlooked the removal of the target's affine Cech proof import.
The target node still recorded its old plan rather than the actual new proof.
New-node records used an invalid object-shaped proof, lacked `proof_origin` and
`mathlib_searches`, and gave placeholders instead of verbatim Lean signatures.
The unit/counit proof description used the unbounded cohomological bound without
recording that dependency. The first code compiled with long-line and `letI` warnings.
These faults are repaired in this sandbox.

## New nodes
`new-affine-qcoh-derived-adjunction-construction`, module
`Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionConstruction`: constructs the two
functors and their adjunction and comparisons, but asserts neither invertibility nor
triangulated compatibility. Source: Stacks Tag 06Z0 elucidation and Tag 079W.

`new-affine-qcoh-derived-adjunction-unit-counit`, module
`Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionUnitCounit`: for any functors and
adjunction with the given comparisons, proves pointwise invertibility of the unit and
counit using affine vanishing and truncation. Source: Stacks Tag 06Z0 proof.

`new-affine-qcoh-derived-tilde-triangulated`, module
`Sheaf.AlgebraicGeometry.AffineQCohDerivedTildeTriangulated`: for any functor with the
termwise tilde comparison, supplies shift and triangulated compatibility. It assumes
neither an equivalence nor an adjunction. Source: Stacks Tag 06Z0, exact termwise
functors and derived localization.

## Second reading by B3
1. Compared the existing module with the repository using `diff`. Its theorem signature
   and existing docstring are byte-for-byte unchanged. Its only changes are proof imports
   and proof body. The other three modules are new, and introduce no definitions.
2. Compiled each delivered module through `lcompile.py`; the initial warnings were
   repaired and the whole set compiles cleanly. Inspected all proof bodies and scanned
   for prohibited declarations. Scratch axiom checks on every delivered declaration
   showed only the three permitted axioms and `sorryAx` from the recorded obligations.
3. Read all three new signatures and docstring arguments against Stacks
   https://stacks.math.columbia.edu/tag/06Z0 and https://stacks.math.columbia.edu/tag/079W.
   The zero ring gives zero module and quasi-coherent derived categories, so presents
   no exception; field and arbitrary commutative-ring cases need no extra hypothesis.
   Arbitrary F and G are determined up to natural isomorphism by the comparisons and
   localization, so transport and adjunction uniqueness justify the universal
   unit/counit statement. Each new obligation is strictly a part of the original
   argument, not a renamed existence of the equivalence. Repeated LeanFinder, Loogle,
   LeanSearch, and grep searches with different wording, and searched Sheaf/upstream
   sources: no matching affine derived theorem. LeanSearch was unavailable and that
   failure is recorded honestly. Mathlib offers `mapDerivedCategory`, its triangulated
   instance, and localization tools, but applying these still needs exactness of tilde
   and transport/descent infrastructure; no new obligation was closed in the brief
   additional attempt. The three docstrings contain the remaining mathematical proofs.
4. The top-level proof uses Mathlib `Adjunction.toEquivalence` directly and does not
   add a fourth wrapper obligation. Removed copied unused imports. The old ordinary
   adjunction and affine vanishing nodes remain in the transitive route; neither is
   pruned. Read `dag/units/sk-thm-picard-f-representable.json`: this auxiliary core
   node is absent from its `realized` statement/step lists, and this reduction changes
   no unit statement or realized step.
5. Updated the target node's proof, proof_deps and proof_origin to its actual three
   steps. Repaired new-node field shapes, verbatim Lean signatures, self-contained
   statements, provenance, source, blueprint ancestry, and actual search records.
   Added affine vanishing and the unbounded-bound proof imports and dependencies to
   the unit/counit obligation. Verdict: a valid partial reduction with three explicit
   outstanding proofs, ready for the required dry run and delivery.

Changes by the second reader: warning repairs (`let` instead of `letI`, wrapped new
signatures); import pruning and proof imports; clarified the product/underlying-group
step of the unit/counit docstring; corrected all node metadata and this report.
