## What changed

Completed `AlgebraicGeometry.Scheme.supportQuotient_flat_kflat_stalk_comparison`
in `Sheaf.AlgebraicGeometry.SupportQuotientFlat`, preserving its full statement,
all seven existing definitions, and every public import. All added helpers are
private and proved. Declaration-scoped transparency settings avoid repeated
expansion of categorical definitions during instance inference. No definition or statement repair, consumer adaptation, new
module, or new node is needed. Preflight classifies the new declaration-scoped
elaboration commands as an interface change; their scope and all 195 downstream
importers are documented in
`coord/changes/D6-support-quotient-flat-scoped-proof-commands.md`.

The proof computes etale stalks directly from the defining cokernel and the
open-extension adjunction. It deduces fixed-scalar flatness on stalks, then proves
flatness of the specified etale realization by the local relation criterion.
The exact constant comparison is identified with a left-adjoint uniqueness
isomorphism. The existing open-comparison unit normalization gives the counit
square; preservation of cokernels gives the normalized quotient isomorphism.
Flatness transfers through comparison and the intrinsic realization, and the
independent-universe bounded-flat criterion gives the two degree-zero K-flat
clauses. Cancellation of the pulled-back quotient epimorphism proves uniqueness.

Updated the item's DAG proof, dependencies and proof origin to this route.
The unit record has no realization on this node; no unit statement or unit
proof step is bypassed. The inherited public theorem docstring describes the
original planned proof; the updated DAG and this report describe the actual one.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.supportQuotient_flat_kflat_stalk_comparison`
(blueprint `lem-pur-support-quotient-flat`). Added 0 holes, split off 0 statements.
There are no textual `sorry`s in the delivered module or any other delivery file.
This is a proof from the existing named library declarations, with no new
assumption or axiom. Existing dependencies retain their own proof status.

## No longer needed

Removed these proof imports:

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.SixFunctors.OpenClosedFlatness`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`

The direct stalk/cokernel route does not use these old proof-dependency nodes:

- `def-weil-pbc-proetale-operations`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-sf-comparison-pullback-exact`
- `lem-sfb-open-closed-flatness`
- `lem-weil-pbc-closed-immersion-finite`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`
- `lem-weil-pbc-finite-stalk-formula-restriction`
- `lem-weil-pbc-free-yoneda-presheaf-module`
- `lem-weil-pbc-open-closed-short-exact`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lemma-openclosed-stalk-lowerstar`
- `prop-weil-pbc-inverse-image-modules-exact`

Withdrew all six obsolete top-level `tool_uses` approvals:
`lem-sfb-open-closed-flatness`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-weil-pbc-free-yoneda-presheaf-module`, `lem-sf-comparison-pullback-exact`,
`lem-weil-pbc-proetale-ringed-open-closed`, and
`lem-weil-pbc-finite-stalk-formula-restriction`.
The independent-universe bounded-flat result replaces the equal-universe
bounded-flat theorem. Canonical adjunction/cokernel APIs replace free Yoneda
and the closed-direct-image identifications. Exactness of comparison is already
provided by its existing instances; the proof needs preservation of cokernels.
These removals describe this proof's needs; they do not claim that other parents
stop importing those modules. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan required identifying both quotients with the closed direct
image. That is unnecessary: the etale open-extension stalk formulas compute the
quotient stalks immediately, and comparison transfers the resulting flatness.
The old bounded-flat API equates the site object, morphism and coefficient
universes, while this item has distinct universes. The existing independent-
universe theorem fits the unchanged K-flat conclusion.

An earlier attempt initially contained an unfinished scalar-action transfer
and used the coefficient category where a rank-one module object was needed
in the constant-stalk calculation. The retained packet contains the completed
comparison and main proof; this resumption repaired its compiler timeout by
limiting automatic unfolding in the six affected declarations. No mathematical statement was changed. Empty closed/open subsets,
empty schemes, and the zero coefficient ring are included by the same stalk,
zero-object and categorical identities, without nonemptiness assumptions.

Validation: the retained proof was read in full and checked against current
sources. All seven definitions, the public theorem statement and public imports
are unchanged. Removed the retained global debugging profiler and heartbeat
options. The full proof compiled cleanly in 32.9 seconds with the repaired
transparency settings; the final packet scopes each setting to its declaration.
The initial resumed dry run timed out at 60 seconds; the final dry run repeats
compilation, axiom checking and server preflight after this repair. The DAG
also records the independent-coefficient tensor comparison used for zero terms.
The review class is CODEX for the node update and documented declaration-scoped
elaboration commands.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
