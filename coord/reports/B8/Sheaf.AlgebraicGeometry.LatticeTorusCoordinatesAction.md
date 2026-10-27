## What changed

Completed the six theorem bodies in `Sheaf.AlgebraicGeometry.LatticeTorusCoordinatesAction` without changing their signatures or public imports.

The coordinate equivalence is Mathlib's `MonoidAlgebra.domCongr`, with the bialgebra equivalence giving comultiplication and counit compatibility, monomial induction giving antipode compatibility, and `hopfSpec.mapIso` giving the exact group-scheme comparison. Natural base change uses `scalarTensorEquiv` and the same coordinate equivalence; its naturality is proved on pure monomial tensors.

Constructed the Laurent quotient equivalence explicitly. The two residue classes for each coordinate form a unit. Products of their integer powers give the inverse map from the group algebra; polynomial evaluation gives the forward quotient map. The inverse identities are checked on polynomial generators and on arbitrary lattice monomials. The construction uses neither nontrivial coefficients nor positive rank.

The affine chart comparison is the composite of pullback pasting, the Over base equation, pullback symmetry and `pullbackSpecIso`; both projection equations are proved. Finite presentation follows more directly from finite generation of the lattice and the Noetherian field coefficient ring, followed by base change. Finite type and quasi-compactness then follow by base change and composition.

For the action, proved the connected-component inclusion is an isomorphism using joint surjectivity of the realization charts. Constructed the component-chart open cover, pulled it back along the torus projection, and proved the actual canonical morphism is over k by its chart scalar equations. Constructed its Over morphism and its `ModObj` record, with the unit and associativity diagrams supplied by two new, separate statements. These are individual diagram identities for an arbitrary canonical coaction; neither restates the action theorem, its component-isomorphism assertion or the construction of the Over morphism.

Only the assigned existing module and its node are changed. Added two modules and their nodes. No shared definition, instance, public declaration signature or adopted source-library module changes. No change record or downstream adaptation is needed.

## Proved and sorry left

Original module: 6 holes closed; 0 holes remain there.

Five original holes have direct complete proofs, with no split obligations:

- `AlgebraicGeometry.latticeTorus_coordinates`.
- `AlgebraicGeometry.latticeTorus_baseChange`.
- `AlgebraicGeometry.latticeTorus_presentation`.
- `AlgebraicGeometry.latticeTorus_affineCharts`.
- `AlgebraicGeometry.latticeTorus_finiteType`.

`AlgebraicGeometry.latticeTorus_action` is a decomposition: the component-isomorphism, canonical-coaction and base-compatibility arguments are proved, and the complete proof assembles its action structure from two separate action-diagram identities.

Exactly two new holes remain:

- `AlgebraicGeometry.Monoscheme.canonicalTorusCoaction_unit`, node `lem-trf-canonical-torus-coaction-unit`, module `Sheaf.AlgebraicGeometry.CanonicalTorusCoactionUnit`.
- `AlgebraicGeometry.Monoscheme.canonicalTorusCoaction_associativity`, node `lem-trf-canonical-torus-coaction-associativity`, module `Sheaf.AlgebraicGeometry.CanonicalTorusCoactionAssociativity`.

Thus this packet closes 6 existing holes and adds 2, a net reduction of 4. The action decomposition is not counted as an independent complete proof. All private helpers and the component cover construction are fully proved, with no holes in definitions.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FineFanBlowup`: no declaration from it is needed directly by these proofs. Its definitions remain transitively available through the existing public monoscheme interface.

Removed `lem-trf-monoscheme-finite-chart-components` from this item's proof dependencies. The connected-component inclusion follows directly from connectedness and the realization chart colimit, so no finite-chart component classification, domain theorem, lattice classification or dense-torus theorem is needed for it. The input coordinate equivalence already supplies the finite generation used by the other clauses. Its module `Sheaf.AlgebraicGeometry.MonoschemeFiniteChartComponents` was not imported and is not newly imported.

Removed `def-trf-fine-fan-blowup` from this item's direct proof dependencies. Coaction existence and its chart formula are already part of `MonoschemeToricRealization`; this proof does not redo the overlap localization construction. The node still supplies definitions below that existing interface.

The arbitrary-base local-finite-presentation proof does not use the Laurent quotient or base-chart theorem; these two independently requested clauses are still fully proved. No entire library module or declaration is withdrawn, and no claim is made that the two removed direct DAG dependencies have no other consumers. Generic affine fibre products, open-cover base change and uniqueness of morphism gluing remain used.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target statement changes. The actual signature of `Monoscheme.existsUnique_torusAction` specifies a unique morphism by its chart formulas, but does not supply an Over structure, a unit law or an associativity law, despite its docstring discussing the latter laws. The Over compatibility is proved in this packet; the two absent diagrams are the new obligations. The original plan's finite-presentation argument through Laurent charts is correct but longer than finite type over the Noetherian field followed by base change.

Read ILO VIII printed pp.103–104, including Proposition 3.2.2, 3.2.4 and Lemma 3.2.12, the original node and its dependencies' Lean signatures, and the latest blueprint locality proof and unit record. No unit realization is bypassed. Checked the new laws on a rank-zero torus and an affine monoid chart: counit evaluation is the identity and both iterated coactions give the same triple monomial tensor. Empty monoschemes have no ToricComponent, so the new assertions have no missing empty case. They require no connectedness of the ambient monoscheme and apply componentwise.

## New nodes

`lem-trf-canonical-torus-coaction-unit` records the unit diagram for any morphism over k with the specified chart coactions. Its proof is the local counit calculation followed by open-cover uniqueness, the unit portion of original Step 6. The Lean statement is in `CanonicalTorusCoactionUnit.lean`, with a complete proof in words in its docstring.

`lem-trf-canonical-torus-coaction-associativity` records the associativity diagram under the same local coaction hypothesis. Its proof compares the two triple tensor monomial formulas and then uses the product chart cover, the associativity portion of original Step 6. The Lean statement is in `CanonicalTorusCoactionAssociativity.lean`, with a complete proof in words in its docstring.

Mathlib searches were actually run through msearch.py: LeanSearch, Loogle, LeanFinder and grep; the node records contain their queries and returned results. The blueprint search for `torus action` returned no matching blueprint nodes. No change records are required.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
