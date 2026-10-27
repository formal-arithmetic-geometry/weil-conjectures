## What changed

Proved `AlgebraicGeometry.Scheme.rootTower_finite_tensor` in
`Sheaf.Paper.RootTowerFiniteTensor`, with all existing public definitions and the theorem
signature unchanged. Private helpers construct sectionwise kernel division, obtain local
surjectivity from the proved root transitions and repleteness, and construct the normalized
finite tensor isomorphism by scalar-extension lifts and abelian epimorphism descent.
The covering-sieve equivalence follows from naturality and sheaf separatedness.

Added private proof imports `Sheaf.Paper.PurTwistRootTransitions`,
`Sheaf.Paper.ScalarExtensionDualTowerCore`, and `Mathlib.CategoryTheory.Sites.EpiMono`.
Updated the existing node's proof, proof dependencies, proof origin, and removed obsolete
tool approvals to match this route. No public interface, source-library file, target,
unit statement, or unit proof step changed. The local proof-elaboration commands flagged
by preflight are recorded in
`coord/changes/root-tower-finite-tensor-proof-elaboration.md`; they do not change any
mathematical interface. There are no downstream Lean consumers to adapt.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.rootTower_finite_tensor`
(node `lem-amb-root-tower-finite-tensor`). Proved 1 of 1 original sorries; 0 remain in the
item, 0 added elsewhere, and 0 split off. Every private helper has a complete proof.
The module compiles without errors or warnings (39.5 seconds before this documentation
update); delivery performs the final compilation and independent checks.

## No longer needed

Removed the private proof imports:
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`;
- `Sheaf.AlgebraicGeometry.EtaleComparison`;
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.

The direct dependencies `lem-amb-kummer-any-base`, `lem-pur-etale-proetale-cover`,
`det-pe-morphisms-etale-comparison`, and
`lem-weil-pbc-weakly-etale-composition-base-change` are replaced by the already proved
`lem-pur-twist-root-transitions`: this proof does not rebuild Kummer covers.
The direct dependency `lem-weil-pbc-site-sheafification-sections-local` is unnecessary:
abelian epi descent constructs the additive inverse, and
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective` supplies residue linearity.
The raw tensor/sheafification dependencies `def-pur-sheaf-tensor-product` and
`def-weil-presheaf-modules-sheafification` are replaced in proof_deps by the normalized
scalar-extension API. Their definitions remain available through the unchanged public
imports and statement dependencies. Removed precisely these seven obsolete tool_uses
entries. This is pruning of this proof's direct dependencies, not a claim that the
modules are unused throughout the library; no upstream declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The DAG's explicit cover-refinement construction
can be replaced by Mathlib's abelian epimorphism descent, preserving the prescribed
normalization. Existing root-transition and scalar-extension declarations suffice; no
new unproved theory is needed. Positive exponents remain encoded by r + 1, including
r = 0. The argument uses no nonzero-coefficient or flatness assumption, and applies to
the zero coefficient ring and the empty scheme.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
