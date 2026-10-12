## What changed

Proved `KaehlerDifferential.exists_basis_differentials_of_separating_transcendenceBasis_basis`
in `Sheaf.FieldTheory.SeparablyGeneratedDifferentialsBasis`, with its signature and
public imports unchanged. Added proof-only imports of Mathlib's polynomial differential
basis, formally étale differential base change, separable field extensions,
intermediate-field fraction-ring structure, and scalar extension of bases.

Evaluation identifies the polynomial ring with the generated subalgebra; the generated
intermediate field is its fraction field. Compose the formally étale localization with
the separable algebraic extension, then transport the scalar-extended polynomial basis
through the canonical differential isomorphism. The final computation proves each basis
vector equals `D k K (x i)`. Updated the existing node's proof, proof dependencies, and
proof origin to describe this construction. No new declarations or interface changes.

Validation: the module compiles without warnings through `lcompile.py`. The construction
uses no nonempty-index assumption and applies unchanged at `r = 0`; arbitrary field
characteristics and the original two universes are retained. The delivery dry run checks
all declaration axioms and the unchanged statement.

## Proved and sorry left

Closed the sole original hole:
`KaehlerDifferential.exists_basis_differentials_of_separating_transcendenceBasis_basis`
(node `new-separably-generated-differentials-basis`). One of one holes proved;
zero holes added, zero split off, and no `sorry` remains in the delivery.
Every mathematical dependency used in the proof is proved in Mathlib.

## No longer needed

No original imports removed, and no Sheaf or WeilConjectures proof-dependency modules
are imported. The standalone node `lem-weil-pbc-kahler-differentials-localization`
is no longer needed in this node's proof dependencies: direct base change along the
composite formally étale map replaces the separate localization-of-differentials step.
Its Mathlib module `Mathlib.RingTheory.Etale.Kaehler` remains needed for the canonical
base-change isomorphism, so this does not claim an entire module is pruned from the
project's target closure. No other original proof-dependency nodes are removed.
The finite-degree argument using `hfg` is also unnecessary.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The planned finiteness argument was stronger than necessary:
`Algebra.FormallyEtale.of_isSeparable` handles all separable algebraic field extensions.
Both `hfg` and `hsep` are redundant, but their binders remain verbatim in the theorem.
The proof explicitly references them to preserve the signature without unused-variable
warnings. The blueprint unit's statement and realized steps are unaffected.

The first dry run flagged a file-level scoped instance command as an interface change.
Removed that command and constructed the fraction-ring instance locally from
`IntermediateField.mem_adjoin_iff_div` and `IsFractionRing.of_field`.

The cited local Stacks TeX file is absent on this machine. Read the corresponding official
pages instead: https://stacks.math.columbia.edu/tag/031W,
https://stacks.math.columbia.edu/tag/090W, and
https://stacks.math.columbia.edu/tag/04EG. Also read the pinned Mathlib proofs and signatures.

## Second reading by P2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof text, proof-only imports, and documentation differ. The DAG node updates only proof metadata and dependencies.

2. Compiled the module with `lcompile.py` and checked the declaration axioms. Compilation is clean, there are no `sorry`s, prohibited declarations, or hollow definitions, and the theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

3. The proof introduces no split-off statements. Its intermediate construction is local, and the existing theorem is proved directly using Mathlib's polynomial basis, fraction-ring, formally étale, and differential base-change results. The theorem statement remains unchanged and no duplicate library declaration was found.

4. The route is shorter than the former localization/base-change sequence: the polynomial-to-generated-field map is shown to be a fraction-ring localization, formal étaleness is composed directly, and the polynomial basis is scalar-extended once. All imports needed only by the proof are plain imports; no removable import remains. The old localization node is removed from `proof_deps` as recorded above.

5. The DAG proof steps, dependencies, and origin describe the construction actually present in Lean. The unit route and target statement are retained.

No changes were needed during this second reading.
