## What changed

Proved `AlgebraicGeometry.symmetric_stabilization_differentials` with its exact original
signature and definitions. Its proof imports two new, fully proved modules:
`Sheaf.RingTheory.ReducedTensorDifferentials` and
`Sheaf.RingTheory.SymmetricAlgebraDifferentials`. Tensor cancellation is already
exposed by the original differential import.

The first component constructs the tensor-product derivation with an algebra map to a
trivial square-zero extension, constructs the reverse map by restricting the universal
derivation to both factors, and proves both inverse identities. The second constructs
the symmetric-algebra derivation with `SymmetricAlgebra.lift`, then proves its differential
equivalence using the generator formulas. The item's proof extends that equivalence to
Q, proves the scalar tower from hEta, cancels the intermediate base change, and composes
the product equivalences. The DAG records these actual steps. All added instances and
construction helpers are private; all new imports used only by proofs are non-public.

No existing statement, definition, universe, visibility or public import was changed.
No other existing module was adapted. This is entirely below the unit level; none of
`sk-thm-p1.realized` is bypassed or modified.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.symmetric_stabilization_differentials`
(node `lem-weil-pbc-symmetric-stabilization-differentials`).

Also proved, without any holes:
- `AlgebraicGeometry.reduced_tensor_differentials`
  (node `lem-weil-pbc-reduced-tensor-differentials`).
- `AlgebraicGeometry.symmetric_algebra_differentials`
  (node `lem-weil-pbc-symmetric-algebra-differentials`).

Holes closed: 1. Holes added: 0. Holes left in the item's module or new modules: none.
This is a proof, not a decomposition into new obligations. Both component lemmas and
all their helpers use only proved Mathlib declarations. All three modules compile
with `lcompile.py --all`; the delivery dry run also checks every declaration's axioms.
Explicit `#print axioms` for the target and both new public theorems reports exactly
`[propext, Classical.choice, Quot.sound]` for each, with no `sorryAx`. The dry run
printed OK, with only the second reading pending, and nothing was pushed.

The statements allow zero rings and zero modules. For K=0 the symmetric algebra is
R and its relative differentials vanish, so the new symmetric equivalence has zero
on both sides. No proof assumes a basis, finite generation, projectivity, smoothness,
flatness or nontrivial rings. The general tensor lemma specializes correctly to S=R,
and kills exactly the R-scalars rather than all S-scalars.

## No longer needed

The four original public Mathlib imports remain unchanged. The second reading removed
the redundant proof import `Mathlib.LinearAlgebra.TensorProduct.Tower` from the item
and the redundant public import `Mathlib.RingTheory.TensorProduct.Maps` from the new
`ReducedTensorDifferentials` module; `Kaehler.Basic` already publicly exposes both.
The two new component imports and their proof-only square-zero-extension imports are used.

The old direct proof dependencies `def-weil-pbc-kahler-differentials` and
`lem-weil-pbc-symmetric-algebra-universal-property` are replaced in the parent by the
proved component nodes. They remain dependencies of those components, so neither
node nor its Mathlib module is pruned from the transitive proof/import closure.
The old base-change node remains a direct dependency. No library module is asserted
to leave the targets' closure.

`Sheaf.AlgebraicGeometry.CotangentComplexSymmetricAlgebra` was inspected but is not
needed or imported: its statement assumes a finite generating presentation, whereas K here is
arbitrary. The new proof needs none of that module's conormal, polynomial presentation,
finite-presentation or quotient-module machinery. This is an avoided candidate route,
not a claim to have pruned an existing import.

## Where the brief, the DAG or earlier work was wrong

The previous attempt moved the target to a reversed-factor statement and introduced a
cycle. This delivery instead proves both genuinely separate component calculations,
and neither new node imports or depends on the target. No new `sorry` is used.

The supplied DAG correctly described the universal-property argument but did not have
separate declarations for the tensor-product splitting or the symmetric-algebra
calculation; its three dependency nodes supply universal properties rather than the
completed calculations. The two new nodes record those steps, now fully proved.

The local `literature/stacks-project` texts are absent on this machine. The source
passages were read on the official Stacks pages for Tags 07M7, 00DM and 00RO. The source
expansion is attributed to H1 in `proof_origin`; the target's generality is proved in
Lean rather than inferred from the more specialized smooth setting of 07M7.

LeanSearch returned an HTTP internal-server error. It is recorded as unavailable;
LeanFinder, Loogle, direct Mathlib searches and whole-blueprint searches were performed.
The existing finite-generator cotangent statement is not a duplicate of the new
arbitrary-module theorem.

## New nodes

`lem-weil-pbc-reduced-tensor-differentials`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-reduced-tensor-differentials.json`, records
the splitting for arbitrary S over R over A. Its declaration is fully proved in
`lean/Sheaf/RingTheory/ReducedTensorDifferentials.lean`. It realizes steps 1 and 3 of the
parent plan before the symmetric-algebra-specific calculation.

`lem-weil-pbc-symmetric-algebra-differentials`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-symmetric-algebra-differentials.json`, records
Omega[Sym_R(K)/R] equiv Sym_R(K) tensor_R K with its generator formula, fully proved in
`lean/Sheaf/RingTheory/SymmetricAlgebraDifferentials.lean`. It realizes step 2 of the
parent plan and makes no finiteness assumption on K.

No change record is needed: no existing interface changed.

## Second reading by H1

1. **Existing interfaces: pass.** Read the complete repository/sandbox diff of
   `SymmetricStabilizationDifferentials.lean`. The only original declaration is
   `AlgebraicGeometry.symmetric_stabilization_differentials`; its signature, universe,
   docstring, public visibility, and all four original public imports are byte-for-byte
   unchanged. Its body replaces `sorry` with composition of proved equivalences.
   The two other modules and nodes are new, with no forced adaptation or change record.

2. **Kernel proof: pass.** Independently compiled all three modules through
   `lcompile.py --all`, including after import cleanup. Read every construction and
   inverse identity: `Hfst` identifies the tensor algebra map's first component with
   tau; `hdS` and `hdB` identify its differential restrictions; `hfg`, `hder` and `hgf`
   prove both inverses. In the symmetric module, `hf` makes the first component the
   identity, `symmetricDerivation_ι` checks generators, and `hgf`/`hfg` establish the
   equivalence. No definition uses an unproved existence theorem or arbitrary witness.
   No delivered source contains `sorry` or any forbidden declaration/attribute.
   Scratch copies with `#print axioms` for all three public theorems each report only
   `propext`, `Classical.choice`, and `Quot.sound`. The delivery probe checks helpers too.

3. **New component statements: pass; no split-off holes.** Matched every ring,
   algebra, scalar-tower and compatibility hypothesis with its node and Lean signature.
   The tensor theorem splits Omega[D/R], retaining Omega[S/R]; it does not mistakenly
   kill all S-scalars. The symmetric theorem includes its stated generator formula and
   assumes no finite generation or projectivity. Checked K=0, the zero-ring case,
   S=R (the second tensor summand vanishes), and the torsion example R=Z, K=Z/2:
   Sym_R(K)=Z[x]/(2x), whose relative differentials have precisely the relation 2 dx=0.
   Both new statements are separate parts of the argument and fully proved.
   Repeated searches with different wording: LeanFinder for derivations on tensor
   products, Loogle `Derivation, SymmetricAlgebra`, launcher grep, and direct `rg` over
   Mathlib, lean/Sheaf, lean/WeilConjectures and the upstream checkout. Read the hits:
   `tensorKaehlerEquiv` computes Omega[D/S], not this Omega[D/R] splitting;
   `cotangentComplex_symmetricAlgebra` requires a finite generating presentation;
   `localized_differentials_equiv` requires finite generation and smooth/localized
   projectivity hypotheses. None supplies either arbitrary-module component outright.

4. **Top-down route and pruning: pass after report correction.** The parent applies
   tensor splitting, the symmetric calculation, scalar extension, tensor cancellation
   and product congruence. The two components use Mathlib universal properties directly,
   not open Sheaf theorems. Checked `dag/units/sk-thm-p1.json`: no realized unit statement
   or step is removed or bypassed. Read the official Stacks source pages
   [07M7](https://stacks.math.columbia.edu/tag/07M7),
   [00DM](https://stacks.math.columbia.edu/tag/00DM), and
   [00RO](https://stacks.math.columbia.edu/tag/00RO): the arbitrary-module calculations
   expand the stabilization argument by universal properties; smoothness and finite
   projectivity in the surrounding application are not needed for these calculations.
   Removed two redundant explicit imports, preserving the target's original interface.
   Corrected `No longer needed` to list both old dependencies removed from the parent's
   direct list and explain that the components retain them transitively.

5. **DAG consistency: pass.** Compared the parent node with the repository: only
   `proof`, `proof_deps`, and `proof_origin` changed. Each delivered node's `lean.statement`
   is the verbatim Lean signature, and each `proof_deps` is the union of its steps' uses.
   Read the three old universal-property nodes and their Mathlib mappings: the component
   proofs use their actual declarations (`liftKaehlerDifferential`, `liftBaseChange`,
   `SymmetricAlgebra.lift` and generator extensionality). The new nodes have sources,
   complete construction/inverse proofs, recorded searches, creation/blueprint records,
   the parent's chapter/unit and new Lean module records. Neither depends on the parent;
   the import graph is acyclic. No new node is a renamed remaining obligation.

Changes by this reading: removed the redundant Tower import in the item and Maps import
in the new tensor module; corrected the direct/transitive dependency accounting and the
finite-generation description in this report. Proofs and all theorem signatures remain
as written by the first worker. One original hole closed, zero holes added, none left.
