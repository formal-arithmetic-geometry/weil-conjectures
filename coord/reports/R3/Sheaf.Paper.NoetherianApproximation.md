## What changed

Completed and checked the earlier sandbox attempt. The signature and visibility of
`Algebra.exists_finiteType_subring_relativeGlobalCompleteIntersection` are unchanged.
Its complete Lean proof now combines a concrete finite coefficient model, bounded
principal neighbourhoods, cover descent, and the polynomial-quotient lower bound.
The original module's public imports and existing docstrings are unchanged.

The private, fully proved helpers in `Sheaf.Paper.NoetherianApproximation` are:
`finite_coefficient_model` (adjoin the finite coefficient set),
`equation_count_le_of_point` (contract an original prime and apply the original
presentation hypothesis), and `polynomial_quotient_fibre_lower_bound` (identify the
fibre using Mathlib's base-changed naive presentation and transfer the existing
lower-bound theorem along the induced spectrum homeomorphism).

Added `Sheaf.Paper.NoetherianCoefficientNeighborhood`, with a complete proof of
`Algebra.exists_coefficient_model_principal_neighborhood`. It uses the existing
`AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension`,
`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`, and
`Algebra.exists_away_fibre_dimension_le`, together with Mathlib's quotient
presentations, tensor cancellation, residue-field map, and fibre-prime correspondence.
The local fibre dimension is proved nonnegative and finite before invoking the
natural-number version of the neighbourhood theorem.

Added `Sheaf.Paper.NoetherianBoundedCoverDescent` for the remaining steps 4-5.
Its statement assumes a bounded principal-open cover and concludes only an upper
bound after coefficient enlargement; it has no complete-intersection hypothesis,
no equation-count inequality, and no lower dimension bound. It is strictly a part
of the original argument, not the original theorem renamed. Its docstring and node
explain the finite subcover, lifted unit identity, coefficient enlargement, field
extension, localization, and local-to-global dimension argument.

Updated the original node's proof, proof_deps, and proof_origin to match the Lean
reduction. Added matching nodes for the two new public declarations. Removed unused
proof imports from the unproved cover-descent module and replaced its unnecessarily
broad presentation import with direct public imports needed by its signature.

All three modules compile together in import order through `lcompile.py --all`.
Searches in Mathlib, both library roots, and the blueprint found no theorem giving
the same descent statement. Smooth Noetherian descent requires smoothness, absent
here. LeanSearch was attempted but unavailable; this is recorded without treating
it as an absence result. The source's proof was read at
https://stacks.math.columbia.edu/tag/00SU because the remote clone has no local
`literature/stacks-project/algebra.tex`.

## Proved and sorry left

Closed the original direct hole:
`Algebra.exists_finiteType_subring_relativeGlobalCompleteIntersection`
(node `lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation`).
There is no direct sorry in the item's module.

Also proved the new
`Algebra.exists_coefficient_model_principal_neighborhood`
(node `lem-weil-pbc-noetherian-coefficient-model-principal-neighborhood`).
The three private helpers named above are completely proved.

Added exactly one direct hole, and the only sorry anywhere in the delivery:
`Algebra.exists_finiteType_model_of_bounded_principal_cover`
(node `lem-weil-pbc-noetherian-bounded-principal-cover-descent`).
Its whole proof is `:= by sorry` in its own new module.

This is a decomposition: one original hole closed and one lower hole added, net
zero direct holes. The original theorem is not claimed to be free of sorryAx in
its transitive dependencies. Existing imported declarations and their outstanding
proof dependencies remain unchanged.

Edge cases checked against the new statement and the combining proof: the index
type may be empty, in which case the unit identity makes the descended quotient
zero. If the descended fibre is nonzero, its prime lies in one of the selected
opens, so the covering index type is inhabited. With the index type chosen as
`PrimeSpectrum S`, this gives an original point and hence `c ≤ n` from the original
hypothesis. Thus the `c > n` and zero-ring cases remain vacuous as required.
For `c = 0` there are no equation coefficients or relation multipliers; the same
adjoin and unit-identity argument applies. No arbitrary object is defined from an
unproved existence statement: the delivery adds no definitions.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension`;
- `Sheaf.RingTheory.FibreDimensionNeighborhood`;
- `Sheaf.Topology.DimensionSupremumLocalDimensions`;
- `WeilConjectures.Mathlib.Topology.KrullDimension`.

Their needed content remains available in the modules that now own the relevant
steps. This is a relocation of dependencies, not a claim that these four modules
are absent from the targets' transitive import closure. The existing
`Sheaf.RingTheory.PolynomialQuotientDimensionLowerBound` import remains used.

The original node's old `proof_deps` absent from its new direct list are exactly:

- `lem-weil-pbc-tensor-cancel-base-change`;
- `lem-weil-pbc-field-extension-base-change-faithfully-flat`;
- `lem-weil-pbc-faithfully-flat-surjective-spectrum`;
- `lem-weil-pbc-dimension-at-point-field-extension`;
- `lem-weil-pbc-dimension-supremum-local-dimensions`;
- `lem-weil-pbc-fibre-dimension-neighborhood`;
- `lem-weil-pbc-spec-localization-away-basic-open`;
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`;
- `lem-weil-pbc-algebra-localization-away-base-change`;
- `lem-weil-pbc-dimension-at-point-open-subspace`.

Second reading also removed redundant `import Mathlib.Algebra.MvPolynomial.Eval`
from the item (available through the new neighbourhood module's public imports),
and `public import Mathlib.RingTheory.FiniteType` from the new neighbourhood
module: it is absent from that module's signature and the proof's finite-type
instances remain available through its proof imports. Both removals compile.

The original root node no longer directly depends on the individual field-extension,
faithful-flatness, local-dimension, principal-neighbourhood, localization and finite
cover steps: these are recorded under the new nodes, or under the existing global
field-extension theorem used by them. No original mathematical dependency is
asserted to be globally pruned, and no blueprint unit or realized unit step is
bypassed. The new cover-descent module has only signature imports; it does not
import unused proof-plan modules while its proof is still sorry.

## Where the brief, the DAG or earlier work was wrong

The previous attempt already contained compiling proof code but lacked both new
node files, the updated original node, and a delivery report. These omissions are
repaired. The six-step mathematical route is retained.

The final Lean step cannot infer `c ≤ n` merely from an upper bound expressed using
natural subtraction `n - c`. The reduction instead remembers that a nonzero
new fibre requires an inhabited covering family. Since our family is indexed by
original primes, the original complete-intersection hypothesis supplies `c ≤ n`.
No definition, existing theorem statement, or target statement was changed.

## New nodes

`lem-weil-pbc-noetherian-coefficient-model-principal-neighborhood`, in
`dag/nodes/sec-proper-base-change/`, records the proved coefficient-model
neighbourhood theorem of `Sheaf.Paper.NoetherianCoefficientNeighborhood`.
It realizes the original split's steps 1-3 and uses the existing global
field-extension dimension theorem rather than redoing its faithful-flatness proof.

`lem-weil-pbc-noetherian-bounded-principal-cover-descent`, in the same directory,
records the remaining public theorem of `Sheaf.Paper.NoetherianBoundedCoverDescent`.
It realizes steps 4-5 without including step 6's lower-bound or equation-count
arguments. Both nodes inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`,
with their blueprint ancestry through the unchanged original approximation node.
No change record is required: existing public signatures and public imports are
unchanged; there are no adapted existing modules.

## Second reading by R3

1. **Interfaces: pass.** Compared the complete item with the repository using
   `diff -u`. The only existing declaration's signature is byte for byte unchanged;
   its visibility, public imports and existing docstrings are unchanged. No existing
   definition is altered. The other two modules are new, so there are no forced
   adaptations or statement-change records.
2. **Proof and axioms: pass as a decomposition.** Compiled all three modules in
   import order through `lcompile.py --all`, with no errors or warnings. Searched
   every delivered Lean file for forbidden declarations and attributes. There is
   exactly one direct `sorry`, the named public cover-descent theorem, with its
   full proof docstring and matching node; there are no definitions added.
   Scratch-copy `#print axioms` checks of all three public theorems show only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The neighbourhood
   theorem also inherits upstream open proofs; neither it nor the main theorem is
   claimed closed under transitive dependencies. The delivery tool probes all
   declarations, including the three private proved helpers.
3. **Split statements: pass.** Read both new statements and their complete proof
   descriptions against [Stacks 00SU](https://stacks.math.columbia.edu/tag/00SU).
   The unproved theorem isolates the finite-cover identity and persistence of an
   upper bound under coefficient enlargement. It omits the complete-intersection
   hypothesis, the lower bound and equation-count argument; those are handled by
   the item's real Lean reduction. Checked empty index types, zero rings/quotients,
   zero relations, `n = 0`, `c > n`, and `d = 0`. In particular the empty family
   forces a zero descended quotient by the lifted unit identity, and a nonzero
   descended fibre supplies an original prime through `Nonempty ι`. All cases
   agree with the stated conclusions. Independent searches with different words
   through `msearch.py` Lean Finder, Loogle (`Algebra.FiniteType, Subring`), and
   grep, plus `rg` in both library roots and Mathlib RingTheory, found no matching
   bounded-cover descent theorem. Read Mathlib smooth Noetherian descent; its
   smoothness assumption prevents its use here. Closing the remaining descent
   statement requires the full coefficient-identity/base-change argument, rather
   than a short application found by these searches.
4. **Route and pruning: pass after report repair.** Read the full reduction and
   `dag/units/sk-thm-p1.json` `realized`; no realized unit statement or step is
   bypassed. The concrete coefficient model, existing neighbourhood and field
   extension theorems, bounded cover descent, and existing polynomial-quotient
   lower bound retain the six-step route. Removed two redundant imports as listed
   above. Named all ten old proof dependencies absent from the new direct list;
   they are relocated dependencies, not globally pruned modules.
5. **Nodes: pass.** Read all three node files and compared them with the proofs.
   Each `proof_deps` is exactly the union of its proof steps' `uses`. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`. Both new nodes have
   the required source, search records, blueprint ancestry, chapter/unit, creation,
   status, and Lean declaration records. Their Lean signatures match the modules.

Changed only the two redundant imports and this report (explicit dependency list,
independent checks, and the second-reading verdict); retained the valid proofs and
new theorem statements. One original direct hole is replaced by one strictly
lower direct hole: net zero, a decomposition, with no globally pruned module.
