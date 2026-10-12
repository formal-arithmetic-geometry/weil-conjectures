## What changed

Replaced the only sorry in `Sheaf.RingTheory.GradedSyzygy`,
`MvPolynomial.exists_graded_free_resolution_two`, by a complete Lean reduction along the
original four-step argument. Its signature and all pre-existing public imports are unchanged.
The proof constructs two graded free covers, gives both kernels their inherited internal
gradings, applies second-syzygy Tor vanishing and the existing graded Nakayama criterion,
and proves injectivity, degree preservation, both kernel-image equalities and surjectivity.
Dependent case analysis packages the three different modules and bases on `Fin 3`.

Added three modules, one per new node. `GradedKernelInternal` is proved from the existing
`graded_kernel_finite` and `exists_finite_homogeneous_generators` declarations. Its proof
constructs the direct-sum component inclusion, proves injectivity using the source internal
decomposition, and constructs a preimage of each kernel element by summing its homogeneous
components. The proved private helper identifies each supplied generator map with a finsupp
linear-combination map to obtain finite homogeneous spanning sets. The other two new modules
state separate outstanding construction and homological-computation steps, with sourced proof
instructions in their docstrings. No definition or existing statement changed.

The original node's proof and proof dependencies now match the Lean reduction. New nodes
record their statements, proof steps, source, three kinds of searches and Lean signatures.

## Proved and sorry left

The original module has no sorry left: its one declaration
`MvPolynomial.exists_graded_free_resolution_two` is proved from named intermediate statements.
This is a reduction; its transitive axioms still include the outstanding imported proofs.

Also proved `MvPolynomial.graded_kernel_internal_finite`
(node `lem-sc-p1-graded-kernel-internal`) and its private helper
`finite_homogeneous_spanning` in `Sheaf.RingTheory.GradedKernelInternal`.

The delivery adds exactly two remaining sorries, each the whole proof of a public theorem
in its own module:

- `MvPolynomial.exists_graded_free_cover`, in `Sheaf.RingTheory.GradedFreeCover`,
  node `lem-sc-p1-graded-free-cover`.
- `MvPolynomial.second_syzygy_tor_vanishes`, in `Sheaf.RingTheory.SecondSyzygyTorVanishes`,
  node `lem-sc-p1-second-syzygy-tor-vanishes`.

The construction works with `M : Type v` and free modules in the ring universe `u`.
Kernel carriers are small because they are submodules of the supplied small free modules.
The Tor lemma explicitly allows a larger-universe target; its proof instructions replace it
by the small quotient `F₀ / ker q₀` before categorical dimension shifting.

Edge-case checks: the free-cover construction allows rank zero and arbitrary integer shifts;
the inherited decomposition handles the zero kernel by an empty sum; Tor vanishing allows
zero-rank free modules. For `M = k`, the construction has the usual Koszul ranks 1, 2, 1.
Negating the last basis degrees gives exactly the original convention `b a ∈ G (-d a)`.

All four delivery modules compile locally together in dependency order without warnings.
The final delivery dry run checks server compilation and preflight as well.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.Algebra.Category.ModuleCat.TorSymmetry`.
- `Sheaf.Algebra.TorDimensionShifting`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpace.KoszulResolution`.
- `Sheaf.RingTheory.FiniteHomogeneousGenerators`.
- `Sheaf.RingTheory.GradedKernelFinite`.

These are relocated dependencies, not globally pruned nodes or modules: the new free-cover,
kernel-grading and Tor modules still use them in the original argument. The original node
now depends directly on the three new nodes and `lem-sc-p1-graded-nakayama-free`; its former
finite-generator, kernel, Koszul, Tor-symmetry, dimension-shifting and Tor-definition nodes
remain transitively needed. No original mathematical step or unit route was bypassed.
There is no globally pruned node or module in this delivery.

## Where the brief, the DAG or earlier work was wrong

The finite-generator declaration provides a surjection from a finsupp module and scalar
homogeneity on its canonical vectors, but no internal shifted grading or homogeneous basis
on that source. This is the separate free-cover construction now stated explicitly.

The graded-kernel declaration provides closure under homogeneous components and finite
homogeneous generators spanning the kernel in its ambient source. It does not provide an
internal decomposition or homogeneous generators spanning top in the kernel carrier.
`graded_kernel_internal_finite` supplies this glue with a completed Lean proof.

The dimension-shifting declaration's second clause assumes a projective-dimension bound
for `M`; it cannot itself establish that bound here without circularity. The Tor step must
use its first isomorphism clause, symmetry, and the resolution of the residue field.
The Koszul declaration is an exact sequence of explicit linear maps, rather than a packaged
projective resolution. The remaining Tor theorem records the required packaging and the
identification of the variable-ideal quotient with constant-coefficient `k`.

LeanSearch returned HTTP 500 for all three new-node queries; those attempts are recorded
as unavailable, not as evidence of absence. LeanFinder and source searches found no exact
replacement. Blueprint searches found only the ancestor graded-resolution statement.
The referenced blueprint literature file is absent from this machine's read-only snapshot;
proof origins are marked agent-written expansions of the existing sourced DAG steps.

## New nodes

`lem-sc-p1-graded-free-cover`, module `Sheaf.RingTheory.GradedFreeCover`: the first-cover
construction, also used for the first kernel. Its only proof dependency is the existing
finite-homogeneous-generator statement; the shifted coefficient grading is elementary glue.
It remains sorry.

`lem-sc-p1-graded-kernel-internal`, module `Sheaf.RingTheory.GradedKernelInternal`: inherited
internal decomposition and finite homogeneous generation in the kernel carrier. Proved from
the existing finite homogeneous generators and graded kernel results; no new sorry.

`lem-sc-p1-second-syzygy-tor-vanishes`, module
`Sheaf.RingTheory.SecondSyzygyTorVanishes`: only the Tor vanishing for a second kernel of two
finite free surjections. It asserts no grading or freeness of that kernel and does not
restate the original resolution theorem. It remains sorry, with the original Koszul,
symmetry, dimension-shifting and Tor-definition dependencies retained.

## Second reading by A3

1. I compared `Sheaf.RingTheory.GradedSyzygy` with the repository version. The target
   declaration is byte-for-byte unchanged; only its proof and the explicitly listed new
   modules are delivered. Verdict: pass.
2. I compiled all four sandbox modules with `lcompile.py --all`. There are no errors,
   forbidden declarations, or unlisted sorries. The two remaining sorries are named public
   split theorems with docstrings and matching DAG nodes. Verdict: pass.
3. I searched the existing Lean sources and checked the recorded Mathlib searches. The new
   declarations are not duplicates; their hypotheses and conclusions are the precise
   construction and Tor reductions used by the target. Verdict: pass.
4. I read the proof from the target downward. It uses the shortest available local route,
   keeps the Koszul, Tor symmetry, dimension-shifting and Nakayama steps, and records the
   five direct imports removed from the old proof. Verdict: pass.
5. I compared each node's Lean signature, proof steps, dependencies and origin with the
   delivered code. The unit record is unchanged and the route is retained. Verdict: pass.

I changed only this second-reading report section; no Lean declaration, statement, definition,
or DAG mathematical content was changed during review.

No change record is needed: no pre-existing definition, theorem signature, instance,
attribute or public import changed. The unit's `realized` arrays are empty and unchanged.
