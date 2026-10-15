## What changed

Proved `PrincipalWLocalization.Retained.properties` in
`lean/Sheaf/RingTheory/RetainedLocalizationProperties.lean`, with its existing signature,
and `structuralMap` definition unchanged. All helpers are private and proved.
Updated the proof docstring and the existing node
`lem-weil-pbc-retained-localization` to describe the implemented route.

The proof constructs the evaluation map from the principal w-localization to each `R_x`,
proves its surjectivity, and computes every selector's value. The ambient point/component
classification then identifies selector support. The retained map is surjective, and its
spectrum is precisely the closed subspace of ambient primes avoiding all selectors.
Intersecting constructible neighborhoods gives exactly the retained prime pairs.

For canonical local rings, the proof uses the source library's filtered-colimit and
finite-product API for maps bijective on stalks. W-locality descends along the retained
surjection; restricting the ambient closed-point homeomorphism gives the required patch
homeomorphism with its diagonal compatibility. For the quotient assertion, maximality
makes all quotient prime pairs diagonal. The canonical quotient map is consequently
bijective on spectra and on stalks, so
`RingHom.BijectiveOnStalks.bijective_of_bijective` proves its bijectivity directly.

The final proof needs only the existing proof imports
`Sheaf.RingTheory.PrincipalWLocalizationPoints` and `Sheaf.RingTheory.IndEtaleStability`.
The second reader removed three redundant proof imports and the redundant public import
of `Mathlib.AlgebraicGeometry.Scheme`; its entire public closure remains reachable through
`Sheaf.RingTheory.RetainedLocalization`. This direct public-import change is declared in
`coord/changes/retained-localization-redundant-scheme-import.md`, including all 31 transitive
importers. No declaration interface changes, other module edits, new public declarations,
or split modules are needed.

The complete file compiles cleanly through `lcompile.py`. The generic proofs cover `T = ∅`,
`T = Set.univ`, and the zero ring: there is no nonemptiness or nontriviality assumption.
Evaluation surjectivity only chooses denominators at an actual prime, and finite-product
stalk bijectivity also covers an empty product. The five assertions in the original theorem
signature are untouched.

## Proved and sorry left

Closed: `PrincipalWLocalization.Retained.properties`
(node `lem-weil-pbc-retained-localization`), the module's sole original `sorry`.

Sorries left in the item: none. Sorries added anywhere: none. Split off: none.
This is one hole closed with no new holes, rather than a decomposition.
The proof uses the existing stage-3 dependencies `PrincipalWLocalization.points` and
`RingHom.indEtale_principalZariski_stability`; their existing upstream holes remain their
own items. This delivery does not claim those dependencies are already proved.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.IsIso`.
- `Sheaf.RingTheory.IndPrincipalZariski` (already provided through the retained definition).
- `Sheaf.RingTheory.PrincipalWLocalization` (already provided through the retained definition).
- `WeilConjectures.RingTheory.ProEtale.WLocal` (already provided through the retained definition).
- `Mathlib.Topology.Homeomorph.Lemmas` (already transitively available).

Also removed the redundant public import `Mathlib.AlgebraicGeometry.Scheme`; see the change
record above. The first worker's two newly added proof imports,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` and
`WeilConjectures.RingTheory.ProEtale.IndZariski`, were redundant and are absent from the final
delivery. Their API remains used through existing public imports.

Pruned proof dependencies:

- `lem-weil-pbc-zero-dimensional-spectrum-profinite`, and its module
  `Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite`.
- `lem-weil-pbc-compact-hausdorff-bijection` (no attached Lean module).
- `lem-weil-pbc-affine-homeomorphism-local-rings` (no attached Lean module).

The quotient proof needs neither profiniteness of zero-dimensional spectra, a compact
Hausdorff homeomorphism criterion, nor the geometric affine homeomorphism/local-ring
criterion. It uses the already-proved source-library ring-map criterion instead.
The other removed direct imports are redundant imports, not pruned mathematical
nodes: their definitions remain needed and publicly reachable through
`Sheaf.RingTheory.RetainedLocalization`.
The retained-localization node does not realize a unit-level statement or step; the
unit's prescribed realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error or disputed assertion was found. The planned final compact Hausdorff
and affine geometric argument is valid but unnecessary with the proved source-library
stalk API. The node now records the shorter route and cites the existing
`lem-weil-pbc-ind-zariski-bijective-on-stalks` dependency for the stalk argument.

The selector-support fact needed a genuine compatibility proof: the ambient existential
prime-pair equivalence alone does not assert the selector formula. The delivery proves it
using the explicit evaluation maps and constancy of clopen membership on components.
Thus the retained-pair classification does not assume that missing compatibility.

The source `Algebra.IndZariski.pi` route is inconvenient for the general universe of the
finite `Fin n` products in our presentation. A private proof directly applies
`RingHom.BijectiveOnStalks.pi` and
`Algebra.BijectiveOnStalks.of_colimitPresentation`; it needs no source-library adaptation.

## Second reading by E1

1. **Unchanged statements and data: pass.** Read the original blueprint file, order 1225,
   over the server's read-only source path, both repository declarations, the complete
   sandbox module, and the retained and principal-localization constructions. Both existing
   declaration signatures are byte-for-byte identical; the complete `structuralMap` body is
   unchanged. For arbitrary commutative `R` and closed `T`, the proof establishes each of the
   source's five assertions: ind-principal-Zariski, exactly the pairs `x ∈ T, y ≤ x`, the
   canonical localization maps, the conditional patch closed-point identification, and the
   canonical quotient isomorphism. In particular, the quotient argument retains the
   hypothesis that every point of `T` is closed. No hypothesis or target definition changed.

2. **Proof and trust checks: pass.** The full file compiles without errors or warnings.
   A separate scratch copy printed the axioms of both public declarations and all 19
   private helpers. Only `propext`, `Classical.choice`, `Quot.sound`, and upstream `sorryAx`
   occur. The generic stalk, quotient, neighborhood-intersection, and topological restriction
   helpers use only the three standard axioms. `properties` still depends on the existing
   open ambient-point and stability theorems and on the proofs used to construct its input
   diagrams; this is an upstream dependency, not a new hole. There is no `sorry`, forbidden
   declaration, or unchecked kernel escape in the delivered module. The choices defining
   `partAt` select the unique partition member; evaluation is the unique colimit map. No
   arbitrary data witness is taken from an unproved mere-existence theorem.

3. **Split statements and edge cases: pass.** No new public statements, nodes, modules,
   or holes were split off. Read each private helper, including the localization-universal-
   property compatibility, selector evaluation, and fraction-surjectivity arguments. The
   ring maps are actual constructions. Empty `T`, the full spectrum, the zero ring, and
   empty finite products are admitted. For the quotient helper, `J = ⊤` gives the bijection
   of zero quotients; no maximal ideal or point is chosen unless one is given. The closed-
   point restriction helper also handles empty spaces. No new unproved search obligation
   arises.

4. **Shortest route and pruning: pass after import cleanup.** Searched `lean/Sheaf` and
   the source's `WLocalization` and `StalkIso` APIs. The upstream w-localization is a
   different construction; it cannot simply replace this retained algebra. The private
   finite-product/filtered-colimit bridge correctly uses the existing source API rather
   than introducing another open statement. Read `StalkIso.quotientMap` and
   `StalkIso.bijective_of_bijective`: they apply to the canonical quotient map once the
   prime-pair calculation makes its spectrum bijective. The selector proof uses only the
   ambient theorem's actual component and closed-point clauses, not an unstated support
   formula. The three removed old proof dependencies are all listed above. The unit
   `sk-thm-properbasechange` realizes its statement through torsion assembly/bounded-below
   base change and its three steps through projective-line, reduction, and torsion assembly
   nodes; this auxiliary retained-localization node realizes none of them. Those route
   nodes and imports are preserved.

5. **DAG agreement: pass.** The six current steps correspond to the actual Lean proof:
   colimit presentation and composition, explicit selector evaluation, retained closed
   embedding/range, canonical stalk bijectivity, restriction of the ambient closed-point
   homeomorphism, and quotient prime diagonality plus the source stalk criterion. Checked
   the statements of `PrincipalWLocalization.points`, the stability theorem, the defining
   principal presentation, and the source colimit and finite-product stalk lemmas against
   their uses. `proof_deps` is exactly the union of the step citations, and `proof_origin`
   describes this implementation. Compared node JSON: only `proof`, `proof_deps`, and
   `proof_origin` differ. No source or statement metadata was silently rewritten.

Changes made by this reading: removed redundant direct imports of `Scheme`,
`Homeomorph.Lemmas`, `ConcreteCategory.Basic`, and `IndZariski`; compiled the resulting
module and its axiom-check copy; added the declared import-change record with all 31
transitive users and the unchanged public path to `Scheme`; corrected the report's import
and signature descriptions. No mathematical proof needed repair.
