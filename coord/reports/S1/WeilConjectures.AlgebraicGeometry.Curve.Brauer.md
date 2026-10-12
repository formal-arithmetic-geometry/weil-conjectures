## What changed

Replaced the sole remaining sorry in
`WeilConjectures.AlgebraicGeometry.Curve.Brauer`, namely
`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`, by a complete Lean
reduction following the two reductions of `lem-sc-brauer-zero-all-curves`.
All existing declaration signatures and docstrings are unchanged.

The proof constructs the nilradical subscheme. Mathlib's subscheme-range and
nilradical-support lemmas prove its underlying closed embedding is a homeomorphism,
so it is again a curve. It then imports and applies
`AlgebraicGeometry.exists_finite_smooth_modification_of_reduced_curve`, installs its
separated, finite-type, dimension, smoothness and finiteness witnesses, and applies the
already proved smooth-curve Brauer vanishing theorem. Two canonical pullback injections
transfer subsingletonness first to the reduced curve and then to the original curve.
The main proof contains no sorry.

Added three ordinary proof imports: the existing module
`Sheaf.AlgebraicGeometry.ReducedCurveNormalization` and the two new modules
`Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection` and
`Sheaf.AlgebraicGeometry.Curve.BrauerFiniteModificationInjection`.
The injections are strictly parts of the argument: neither asserts Brauer vanishing,
and the second does not assume the modifying scheme is smooth. Each new module has one
public theorem, its own DAG node, the unchanged canonical cohomology-map formula,
and a complete proof in words. Updated the parent node's proof and proof dependencies
to match this assembly. The unit's Kummer route is unchanged; its existing smooth
Brauer theorem is still used. The finite smooth modification is the same component
normalization construction of the parent plan, used as an existing geometric tool.

## Proved and sorry left

Reduced the original one of one sorries:
`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup` now has a complete
compiling proof from named dependencies. Its imported dependencies still contain
sorries, so this is a stage-3 reduction, not a claim of an axiom-free closed theorem.
The four previously proved declarations of the module are unchanged.

The only sorries added or left in the delivered Lean files are:

- `AlgebraicGeometry.IsCurve.injective_brauer_pullback_reduction`, in
  `Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection`, node
  `lem-sc-brauer-reduction-injection`.
- `AlgebraicGeometry.IsCurve.injective_brauer_pullback_finite_modification`, in
  `Sheaf.AlgebraicGeometry.Curve.BrauerFiniteModificationInjection`, node
  `lem-sc-brauer-finite-modification-injection`.

Local compilation of both new modules and the main module passed without warnings.
The main theorem uses Mathlib directly for reduction geometry instead of importing
`Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism` and its sorry theorem.

Edge cases checked mathematically: empty curves (empty reduction and modification),
reduced curves (the nilradical is zero), zero-dimensional curves including nonreduced
Artinian schemes (the nilradical filtration still applies), disconnected curves,
and a reducible nodal curve (the finite modification separates the branches, and the
units cokernel is supported at the finitely many exceptional points). For finite
modifications, V = C makes the map an isomorphism; Y need not be reduced, because only
reducedness of the etale test scheme over C is used for the units monomorphism.
No positive-characteristic restriction is introduced.

## No longer needed

No existing imports were removed: they are used by the module's earlier proofs or its
public statements. No node or module is claimed globally pruned.

The parent no longer directly depends on the original thirteen low-level dependencies
except `lem-sc-brauer-zero`. The cohomology comparison, affine and Noetherian vanishing,
and etale-reducedness dependencies now occur in the two injection nodes. The normalization
construction, existence and smoothness dependencies are packaged by the existing
`lem-weil-pbc-reduced-curve-normalization` node. Point cohomology is used through the
finite-support argument. These are reorganized dependencies, not claims that the
underlying theory is unnecessary.

`Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism` was considered during proof
construction and removed before delivery: the required reduction geometry is proved
from Mathlib in the main module, without importing that theorem.

## Where the brief, the DAG or earlier work was wrong

No existing statement was found false or changed. The original plan gives the two
injection arguments in words but has no named theorem stating either complete
injection, so these two glue steps were split into explicit new statements. The
recorded component-normalization tool fits the reduced curve after its structure
morphism's typeclass hypotheses are installed explicitly.

The blueprint Markdown file is absent from this machine's literature tree. The complete
numbered proof quoted in `lem-sc-brauer-zero-all-curves.json` was read and used; the new
proof-origin records say they were extracted from that retained quotation. No claim
of consulting a missing document is made.

LeanFinder returned unrelated elliptic-curve and Selmer-group injections; Loogle returned
zero hits for CohomologicalBrauerGroup; grep and full-blueprint searches found no matching
reduction or finite-modification injection. Both LeanSearch requests returned Internal
Server Error and are recorded as unavailable, with no inferred no-match verdict.

## New nodes

`lem-sc-brauer-reduction-injection`: the canonical map from H²(G_m) on a curve to its
reduction is injective. Its proof is the nilradical units sequence, quasi-coherent
cohomology vanishing above dimension one, the finite filtration, and exact finite
pushforward. This step also holds over a field which is not algebraically closed.

`lem-sc-brauer-finite-modification-injection`: for a reduced curve over algebraically
closed k, a finite morphism which is an isomorphism over a dense open induces an
injection on H²(G_m). Its proof is the units monomorphism, finite-support acyclicity
of its cokernel, the long exact sequence, and exact finite pushforward. No hypothesis
or conclusion of smooth-curve Brauer vanishing is included in this theorem.

No change records: no existing public signature or definition changed.

## Second reading by S1

1. Compared the delivered main module with the repository version. Existing declaration
signatures and statements are byte-for-byte unchanged; the only original theorem body
changed is the intended proof, with three proof-only imports added. The two new modules
contain the split statements recorded by their nodes.

2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds
without errors or warnings. The only remaining `sorry`s are the two named split theorems,
with matching DAG nodes; no definitions contain `sorry`, and no forbidden declarations
were introduced. Scratch `#print axioms` checks on all five existing declarations
and both new declarations show only `propext`, `Classical.choice`, `Quot.sound` and,
for results with open dependencies, `sorryAx`. The Tsen specialization itself uses
only the three standard axioms.

3. Checked both split-off injection statements against their node statements and the
blueprint proof. They are true reductions strictly weaker than the parent vanishing
claim, retain the exact canonical cohomology maps, and add no unnecessary smoothness
hypothesis on the modified scheme. Searches recorded in the report found no existing
library or Mathlib duplicate.

4. Read the proof top-down. It uses the Mathlib nilradical support/homeomorphism route,
the existing reduced-curve finite smooth modification, the existing smooth Brauer
vanishing theorem, and the two named injections. The unit's reduction and normalization
route is retained. No import was removed; the added imports are proof-only where
appropriate, and the parent DAG proof and dependencies match the proof.

5. Checked the DAG records for both new nodes and the parent: statements, proof steps,
proof dependencies, proof origins, Lean declarations, chapter and unit agree with the
Lean files. No statement or definition change record is needed.

Second-reader searches used `grep` with “Gm cohomology nilpotent thickening finite
birational”, `loogle` with `"gmSheaf", "Injective"`, and local `rg` for units,
nilpotents and finite cohomology. No duplicate injection was found. The generic-point
injection requires regularity and cannot replace these steps.

For completeness, the original parent dependencies no longer used directly are:
`def-sc-etale-qcoherent-module`, `def-sc-normalization`,
`etale-proposition-etale-reduced`, `lem-kun-03qu-sep-closed`,
`lem-sc-cech-spectral`, `lem-sc-etale-affine-qcoherent`,
`lem-sc-noetherian-cohomology-above-dimension`, `lem-sc-normalization-exists`,
`lem-sc-normalized-curve-smooth`, `lem-weil-pbc-finite-pushforward-cohomology`,
`lemma-weil-pbc-finite-direct-image-exact`, and `pqf-lem-affine-vanishing`.
They are reorganized into the split injections and existing normalization theorem;
none is asserted globally unnecessary. The unit's `realized` fields are unchanged
(the existing record has empty realization lists).

I clarified the report's dependency accounting and added this second-reading section;
no Lean proof or DAG content required repair.
