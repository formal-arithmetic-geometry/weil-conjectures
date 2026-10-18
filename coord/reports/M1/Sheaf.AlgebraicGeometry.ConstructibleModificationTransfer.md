## What changed

Proved `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_modification`
with the existing source theorem `HasConstructibleDirectImages.of_modification`.
The private, fully proved `constructibleDirectImages_iff_nonnegative` converts the two
constructibility conventions, compares bounded-below and total direct images, and handles
negative degrees by left t-exactness. The main proof supplies quasi-compactness of the open
inclusion using the finite-type field structure on X.

Added only proof imports of
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` and
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification`.
All existing signatures, visibility and public imports are unchanged. Updated the node's
proof, proof_deps and proof_origin to this reuse route. No change record is necessary:
no interface or definition changes and no consumer adaptations.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_modification`
(node `lem-finrepair-modification-c`). Added 0 holes; 0 remain in the delivered module.
This is a proof, not a decomposition. No new nodes or modules.

Single-file lcompile passes without warnings. `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
Empty schemes, empty or total U, q = 0, and the zero coefficient ring require no exclusions:
the source transfer theorem permits all these cases; the equivalence treats q < 0 by zero
homology and q ≥ 0 by compatibility, with no uniform amplitude assumption.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `Sheaf.AlgebraicGeometry.ModificationExtensionZero`
- `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence`

The separate proof obligations `lem-finrepair-modification-extension-zero`,
`lem-weil-pbc-grothendieck-spectral-sequence`,
`lem-weil-pbc-derived-functor-long-exact`,
`lem-weil-pbc-module-sheaves-enough-injectives` and
`lem-weil-pbc-module-direct-image-left-exact` are no longer dependencies of this wrapper.
In particular it does not depend on the sorried canonical-map statement
`Sheaf.AlgebraicGeometry.ModificationExtensionZero.modification_extension_zero`.
The proved source modification theorem provides the derived-object identification needed
here; the stronger assertion about the particular canonical map is unnecessary.

`prop-constructible-pullback`, `lem-weil-pbc-open-closed-short-exact`,
`lem-fin-extension-by-zero`, `lem-fin-closed-immersion` and `thm-constructible-serre`
are no longer direct DAG dependencies or imports of this wrapper. Their source modules and
proofs remain transitively used by the existing source modification theorem; no claim is
made that those modules leave the global targets' closure. Removed the seven old direct
tool-use approvals accordingly. The unit record has no realized statement or proof steps
for this node, and the same open-closed modification route is preserved by the source proof.

## Where the brief, the DAG or earlier work was wrong

The item already has a proved source-library counterpart:
`AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_modification`,
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification`, lines 153-179.
It is stronger geometrically (no properness of f or reducedness of Z needed).
The original DAG plan did not account for this available proof. The project's property C
uses only nonnegative degrees and finite constant-value constructibility; the source
property uses all integer degrees and finitely generated stalks. The private equivalence
checks these differences explicitly rather than assuming them definitionally equal.

Read the original blueprint node and unit text, the original node's eleven dependency
statements and attached declarations, the source modification proof and its property C,
the constructibility comparison and the total/bounded-below compatibility proof.
Searches run through msearch: leanfinder for modification constructibility transfer
(returned topological constructible-image results only), loogle IsConstructibleSheaf
(unknown identifier), and grep modification (no relevant Mathlib theorem). Local rg found
the exact source theorem. Both new imports pass import_direction.py's no-cycle check.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
