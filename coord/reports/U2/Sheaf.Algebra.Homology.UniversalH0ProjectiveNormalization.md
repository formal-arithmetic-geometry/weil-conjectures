## What changed

Replaced the sole proof of `CochainComplex.universalH0_projective_normalization` without
changing its signature, visibility, public imports, or existing docstring. The proof first
obtains a connective projective model, transports the universal H0 condition through its
scalar-extended homotopy equivalence, cancels the degree-zero complement, and composes the
homotopy equivalences in the derived category. Mathlib supplies the finite-projective
retraction; the proof explicitly transports it to the requested
`ULift (Fin m) →₀ R` model and verifies its composite pointwise.

Added three modules:

- `Sheaf.Algebra.Homology.UniversalConnectiveProjectiveModel`: proved from the opcycles
  criterion. It constructs `P.truncGE 0`, proves finite projectivity and finite support
  termwise, obtains its quasi-isomorphism from the identity scalar-extension test, and
  uses Mathlib K-projectivity to obtain a homotopy equivalence.
- `Sheaf.Algebra.Homology.ResidueConnectiveProjectiveOpcycles`: the remaining algebraic
  criterion for finite projectivity of the canonical quotient `P.opcycles 0`. It requires
  only negative residue homology, with no H0 rank hypothesis or replacement-complex output.
- `Sheaf.Algebra.Homology.ConnectiveUniversalH0ZeroDifferential`: the separate degree-zero
  cancellation step, assuming the negative terms have already been removed.

The main module's new proof imports are the two model lemmas,
`Mathlib.RingTheory.Finiteness.Projective`, and `Mathlib.CategoryTheory.Adjunction.Additive`.
No data definition was added and no dependent module was adapted. The main node and the
three new nodes record the route actually used. The unit route is preserved.

## Proved and sorry left

Closed the original hole in `CochainComplex.universalH0_projective_normalization`
(node `lem-sc-universal-h0-projective-normalization`). This is a decomposition into two
strictly smaller holes, not a proof with all dependencies closed: one original hole closed,
two holes added; the closure ledger's net is -1 before any independent pruning effects.

Also proved the new theorem `CochainComplex.universalConnective_projective_model`
(node `lem-sc-universal-connective-projective-model`) with an actual good-truncation
construction and a complete Lean proof of the homotopy comparison.

Every remaining sorry in the delivered files:

- `CochainComplex.residueConnective_projective_opcycles`
  (`lem-sc-residue-connective-projective-opcycles`): its entire proof is `by sorry`.
- `CochainComplex.connective_universalH0_zero_differential`
  (`lem-sc-connective-universal-h0-zero-differential`): its entire proof is `by sorry`.

The item itself has no sorry. All four modules compiled via `lcompile.py --all` without
warnings other than the expected sorry notices. The final dry run additionally probes
the axioms and runs the delivery preflight.

Checked the new statements on the zero ring, the zero complex, a complex supported only
in degree zero, and a split contractible negative pair. For the opcycles criterion the
zero ring has no primes, but every module is zero, so the vacuous residue hypothesis is
correct. For the degree-zero criterion, the minimal-model kernel calculation uses a
non-zero-divisor, so it remains valid over nonreduced rings. No generator is assumed to
remain nonzero in residue fields without the local homotopy/base-change comparison.

## No longer needed

Replaced Mathlib.Algebra.Homology.Homotopy in the new opcycles criterion with
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex, which supplies exactly
the complex, scalar-extension, and homology vocabulary needed by its statement.
Removed the unused lem-pc-ring-derived-map-representative dependency from the
proved connective-model node; Mathlib K-projectivity supplies the comparison directly.

No pre-existing import was removed: the item had only its five statement imports.
Removed the following nodes from the item's proof route, together with their scheme
model modules:

- `lem-sc-perfect-finite-free-residue-model` /
  `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`.
- `lem-sc-perfect-universal-h0-bottom-model` /
  `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel`.

The degree-zero argument now works over each local ring using the existing
`lem-sc-perfect-local-pseudocoherent-free-model` /
`Sheaf.RingTheory.MinimalFreeModel`, without spreading a sheaf model to an affine open.
The finite-projective residue cokernel criterion
`lem-pc-finite-projective-cokernel-localization` is still needed below the new algebraic
statements; it is not pruned. These are route-local pruning claims; other callers may
still need the two scheme modules.

During import minimization the attempted `Mathlib.LinearAlgebra.Finsupp.Pi` import in the
main file and `Mathlib.Algebra.Homology.Embedding.CochainComplex` import in the connective
model were removed after compilation confirmed their tools were already available.

## Where the brief, the DAG or earlier work was wrong

The original DAG's two local-model dependencies have scheme-sheaf signatures, not
fixed-ring-complex signatures, so neither is a direct application to this theorem.
The new degree-zero lemma makes the fixed-affine argument explicit and uses the existing
local-ring minimal model instead. No original statement is disputed or changed.
The negative-tail existence part can be constructed as good truncation once its zeroth
opcycles is known projective; no separate chosen complex or explicit repeated cancellation
is required in that proved module.

Scalar extension has no available global Additive instance in the item's original
imports. The proof obtains it locally from `extendRestrictScalarsAdj.left_adjoint_additive`;
no global instance was introduced.

Read the Stacks statements and proofs at Tags 00O0, 00NX, 0BCC, 0BCD, and 0BF2. The new
proof sketches are marked as agent-written fixed-affine adaptations, not as verbatim
statements of those tags. Blueprint searches for opcycles, negative tail, degree-zero
complement, connective, finite projective, rank one, and 0BCD found no exact duplicate.
LeanSearch returned Internal Server Error; the records say unavailable. Actual LeanFinder,
Loogle, and source grep results are recorded in the new nodes and sandbox search log.

## New nodes

`lem-sc-residue-connective-projective-opcycles`, in
`dag/nodes/sec-abelian-varieties/`, states the algebraic criterion for the single canonical
quotient at the end of the negative tail. Its complete proof sketch is induction by
residue-split cancellation, with finite presentation and local-to-global projectivity.
Its module contains one named public sorry and no definitions.

`lem-sc-universal-connective-projective-model`, in the same chapter, states the negative-tail
model step without any H0 hypothesis. Its module is proved: good truncation realizes the
complex, and the K-projective quasi-isomorphism criterion gives the homotopy equivalence.

`lem-sc-connective-universal-h0-zero-differential`, in the same chapter, states only the
remaining degree-zero cancellation for an already connective model. Its complete proof
sketch first checks the cycle inclusion on local minimal models and then cancels the
residue-injective complementary summand. Its module contains one named public sorry and
no definitions. All three nodes inherit the parent's unit and blueprint ancestor.

## Second reading by U2

1. Compared the delivered main module against the repository with diff. The only changes
   are four private proof imports and the original theorem body. Its complete signature,
   visibility, existing docstrings, definitions, and public imports are byte-for-byte
   unchanged. There are no adapted modules or interface change records. Verdict: pass.
2. Compiled all four modules with lcompile.py --all. Inspected every body: two named
   theorem-only sorries remain, exactly those listed above; no hollow definitions,
   forbidden declarations, arbitrary data witness definitions, or hidden holes occur.
   The derived comparison composes genuine homotopy equivalences; the finite-free
   retraction is checked pointwise. Delivery probes check all declaration axioms.
   Verdict: pass with the explicitly reported two open dependencies.
3. Read both split-off statements and their full docstring proofs independently, checking
   the zero ring, empty support, a degree-zero-only complex, and a contractible negative
   pair. Checked the residue-injective criterion against Stacks Tag 00O0, local minimal
   models against 0BCC, and finite projectivity against 00NX. The kernel multiplier
   argument is valid without reducedness. Each hole is strictly a part of the parent
   argument: negative-tail quotient projectivity versus connective degree-zero
   cancellation. Independent LeanFinder, Loogle, and grep queries are in the search log.
   Source searches found no exact duplicate. FlatOpcyclesTorCriterion.opcycles_of_exactAt
   instead requires tensor exactness for every module; it does not directly establish
   the residue-only criterion, and does not close either hole in a few minutes.
   Verdict: true, needed, strictly smaller statements with matching nodes.
4. Reviewed the good-truncation construction and the two-step main reduction from the
   top downward. Mathlib supplies truncation, K-projectivity, and finite projective
   retractions directly. The old parent's three proof dependencies are all accounted
   for: the two scheme-model nodes are no longer used, while the cokernel localization
   criterion remains needed below the new holes. The unit sk-prop-av-cube realized fields
   contain no designated nodes (statement [], steps [[]]); the delivery changes no unit
   record or chapter route. Replaced the broad Homotopy import with ShortComplex.HomologicalComplex in the
   new opcycles module; compilation confirmed the smaller import supplies its signature. Verdict: pass after import pruning.
5. Compared all node Lean records with their declarations, and checked new-node source,
   creation, blueprint, unit, searches, proof steps, and dependency unions. Corrected
   the proved connective-model node: its old derived-map representative dependency was
   not used in Lean; Mathlib IsKProjective.quasiIso_iff is used directly instead. Existing
   parent node changes are confined to proof, proof_deps, and proof_origin.
   Verdict: pass after this DAG correction.

Second reading changed only the narrowed import, the connective-model proof dependency
record, and this report; no Lean proof or statement needed repair. One original hole
closed and two holes added remains a decomposition, with net -1 holes before pruning.
