## What changed

Proved `AlgebraicGeometry.IsCurve.injective_brauer_pullback_finite_modification`
with its signature unchanged. The proof applies the existing isomorphism-off-finite-support
cohomology theorem to the canonical units comparison, then composes with the finite
pushforward edge map. Naturality and the adjunction formula identify this composite with
the exact canonical pullback in the statement.

Added two fully proved modules: `Sheaf.AlgebraicGeometry.Curve.DenseOpenFiniteComplement`
and `Sheaf.AlgebraicGeometry.Curve.GmFiniteModificationOpenIso`. The first treats reducible
curves by working in each irreducible component, proves finite support directly from
Mathlib's finite irreducible decomposition and sobriety, and uses `residueFieldIsoBase`.
The second computes open inverse image by restriction and proves objectwise that the
projection used to pull back units is an isomorphism. Updated the parent DAG proof and
its dependencies to this route. All three modules compile locally without warnings.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.IsCurve.injective_brauer_pullback_finite_modification`
(node `lem-sc-brauer-finite-modification-injection`).

Also proved `AlgebraicGeometry.IsCurve.dense_open_finite_complement`
(node `lem-sc-dense-open-finite-complement`) and
`AlgebraicGeometry.Scheme.isIso_upperStar_map_gmSheafToLowerStar_of_isIso_restrict`
(node `lem-sc-gm-finite-modification-open-iso`). No sorry remains in any delivered module,
and no intermediate statement is left sorry. This does not assert that every existing
foundational declaration used by the library is sorry-free.

## No longer needed

Removed these proof imports from the item:
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`;
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen` (redundant through `FiniteSupport`);
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`;
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`;
- `WeilConjectures.SixFunctors.Finite.Exact`.

The finite closed-image/surjectivity argument
(`lem-weil-pbc-finite-closed-map-finite-fibres`) and reduced-etale argument
(`etale-proposition-etale-reduced`) are unnecessary: the cohomology comparison handles
both kernel and cokernel, and does not require the units map itself to be mono.
The unproved module `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`
(node `lem-sc-noetherian-closed-points-finite`) is bypassed by a direct finite-component
argument. The underlying mathematical finiteness fact remains used and is proved here.
The separate dependency `lem-weil-pbc-alg-closed-finite-extension-trivial` is unnecessary
because `residueFieldIsoBase` supplies the residue-field isomorphism directly.

The original direct edges to finite-type Noetherianity and closed-point residue fields
move into the proved dense-complement helper. Finite-support acyclicity,
separably closed point acyclicity, the long exact sequence, and exact finite pushforward
are packaged by the existing proved cohomology tools; their transitive uses are retained,
not claimed globally pruned. The replacement cohomology tool is
`lem-sc-iso-off-finite-set-cohomology`, a generic existing proved tool in the same chapter.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan is longer than necessary: the library already
has a bijectivity theorem for a sheaf map which is an isomorphism outside finite closed
support. Reducedness of C is unused in this proof, but the existing signature is preserved.
The original docstring records the valid original plan and is preserved. The DAG records
the implemented shorter route. LeanSearch returned an internal server error; both attempts
are recorded as unavailable, with no mathematical verdict inferred.

Checked edge cases: empty C forces the support empty; V = C has empty complement;
zero-dimensional and reducible curves are handled component by component; neither helper
requires reducedness or smoothness of Y. For the units helper, only the assumed
isomorphism of the restriction is used to make each projection an isomorphism.

## New nodes

`lem-sc-dense-open-finite-complement`, in
`dag/nodes/sec-curve-estimates/lem-sc-dense-open-finite-complement.json`, records the fully
proved geometric finite-support input. Blueprint searches for dense-open complements and
finite complements found no blueprint statement with these exact hypotheses and clauses.

`lem-sc-gm-finite-modification-open-iso`, in
`dag/nodes/sec-curve-estimates/lem-sc-gm-finite-modification-open-iso.json`, records the fully
proved restriction-of-units input. Blueprint searches for units, the isomorphism locus,
and isomorphisms over opens found no matching node. No change record is needed:
all existing statements and definitions are unchanged.

## Second reading by N1

1. Compared the original module with the repository using `diff -u`: its entire existing
   theorem signature and docstring are byte-for-byte unchanged. Changes are confined to
   proof imports and the proof body. The other two modules are new, contain only the named
   theorems recorded in their nodes, and introduce no definitions. No change record is needed.
2. Compiled all three delivered modules in import order with `lcompile.py --all`, without
   errors or warnings. Searched their source for sorry and forbidden proof mechanisms: none.
   Compiled scratch copies with `#print axioms` for all three declarations: each depends
   exactly on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
3. There are no split-off open statements. Read both proved helper statements clause by
   clause. For dense complements, density meets the nonempty open exclusive to each
   irreducible component, so the dimension-one lemma applies to a genuinely nonempty open
   in that component; closedness descends along its closed inclusion. Sobriety turns each
   irreducible piece of the complement into a singleton. `residueFieldIsoBase` applies
   because finite type is supplied by `IsCurve`. This includes empty schemes, zero-dimensional
   components, nonreduced curves, and reducible curves. For the units helper, pullback
   cancellation makes the actual projection an isomorphism; no smoothness, reducedness or
   surjectivity is assumed. Empty opens are included. Independent LeanFinder search for
   proper closed subsets missing every component of a one-dimensional Noetherian scheme
   found component finiteness and sobriety tools but no exact replacement. Loogle search
   for `"gmSheafToLowerStarGmSheaf"` returned zero hits. Local searches in Sheaf, the source
   library and upstream slopmaster2 found the existing irreducible finite-complement lemma
   and affine-open existence theorem; neither states the arbitrary dense-open helper on
   reducible curves. No duplicate of either new theorem was found.
4. Read the proof downward: finite-complement helper, restriction-of-units helper, the
   existing generic degree-at-least-two cohomology bijection, then the finite edge map.
   Naturality and the adjunction counit identify the composite with the unchanged canonical
   pullback, rather than an unspecified injective map. The generic cohomology result is a
   proved tool and preserves the units/finite-support argument. Read `sk-prop-h2.json`:
   this node is below the unit level and no realized unit statement or step is replaced.
   All three public imports of the original module supply its signature; the new modules
   are proof imports. Removed the redundant direct `CohomologyClopen` import, since
   `FiniteSupport` publicly imports it; recompilation passed.
5. Read all three node records against their Lean declarations and proof bodies, and checked
   the cited dimension-one closed-point, residue-field, restriction and finite-edge statements.
   The new nodes have complete statements, provenance, searches, Lean records, and proofs;
   their clauses agree with Lean. The parent proof and dependency union describe the
   implemented route. For completeness, every old direct dependency absent from the new
   parent's `proof_deps` is listed here: `lem-weil-pbc-finite-closed-map-finite-fibres`,
   `etale-proposition-etale-reduced`, `lem-weil-pbc-finite-type-over-noetherian`,
   `lem-sc-noetherian-closed-points-finite`, `lem-weil-pbc-alg-closed-finite-extension-trivial`,
   `lem-weil-pbc-closed-point-residue-field-base`, `lem-sc-finite-support-acyclic`,
   `lem-kun-03qu-sep-closed`, `lem-weil-pbc-sheaf-ext-cohomology-long-exact`, and
   `lemma-weil-pbc-finite-direct-image-exact`. The finite-type and residue-field facts move
   into the new geometric helper; acyclicity, the long exact sequence and finite exactness
   remain transitive inputs to the generic tools. Only the closed-image, reduced-etale,
   closed-points-finiteness helper and finite-extension-triviality edges are bypassed.

Second reading changed only the redundant proof import, the source/blueprint information
in the two new module docstrings, and this report's explicit pruning and review details.
No theorem statement, definition, or proof argument required repair.
