## What changed

Repaired the earlier sandbox delivery. The existing declaration
`AlgebraicGeometry.Scheme.Modules.picard_kunneth_qcoh` retains its exact signature and
public imports. Its proof uses conjunction introduction and two separate theorems:
`picard_kunneth_iso_exists` (the isomorphism and its generator formula) and
`picard_kunneth_functoriality` (pullback compatibility of the external cup operation).
Each child has its own module, complete proof docstring, source, exact Lean signature,
and complete DAG record. The parent node now records this two-part proof.

The malformed duplicate node `lem-sc-picard-kunneth-qcoh-iso` from the previous sandbox
attempt was removed before delivery. No existing library statement or definition changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.picard_kunneth_qcoh`
(node `lem-sc-picard-kunneth-qcoh`). Its proof compiles from the two named statements.

Added two holes, each the entire proof of one public theorem:

- `AlgebraicGeometry.Scheme.Modules.picard_kunneth_iso_exists`
  (node `lem-sc-picard-kunneth-qcoh-iso-exists`, module
  `Sheaf.AlgebraicGeometry.PicardKunnethQcohIso`).
- `AlgebraicGeometry.Scheme.Modules.picard_kunneth_functoriality`
  (node `lem-sc-picard-kunneth-qcoh-functoriality`, module
  `Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality`).

This is a decomposition: one upper hole closed, two lower holes added, net -1.
It supplies no independent sorry-free geometric theorem. The two child statements are
strictly separate parts of the original argument; neither implies the other or repeats
the whole parent statement. No data definition was introduced or chosen from mere existence.

Checked the edge cases mathematically: n=0 recovers the global-section tensor map;
a zero coefficient module or an empty factor gives zero cohomology; the induction uses
a nonnegative vanishing bound, including the case of zero cohomology in every degree.
The pullback clause imposes no compactness or affine-diagonal hypotheses on X' and Y'.
The inverse-image covering comparison does not require such hypotheses.

## No longer needed

Removed these proof-only imports from the parent module:

- `Sheaf.Algebra.Homology.TensorKunneth`
- `Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
- `Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor`
- `Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.CechComparisonMapNaturality`
- `Sheaf.Paper.CechCupPullbackCompat`
- `Sheaf.Paper.HigherDirectImagePresheaf`

Their planned geometric and homological roles remain in the child nodes and modules.
No existing dependency node or module is claimed to be globally pruned; the original
Kunneth proof route is preserved below the isomorphism child. The parent's proof_deps
are now precisely the two child node IDs. All original public imports remain.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's new nodes had incomplete metadata, prose instead of exact Lean
signatures, copied review records, mismatching blueprint IDs, and empty proof_deps despite
nonempty step uses. Its isomorphism child incorrectly documented only Steps 1--3:
constructing the Cech map does not establish that it is a quasi-isomorphism. The repaired
child includes Steps 1--7, including the short-exact-sequence argument, induction, and
acyclic case. The previous report incorrectly called this an analytic proof and wrote
an unauthorized placeholder second-reading section; both were removed.

Existing `tensor_kunneth` is a theorem about integer-indexed total complexes, not scheme
cohomology. The Cech comparison and cup compatibility statements require explicit
comparison maps and their predicates. They do not directly state the exact scalar Ext
transport, geometric total-complex comparison, and degree reindexing needed here.
The two extracted statements keep these outstanding arguments explicit rather than
asserting the Cech map is already an isomorphism. Their docstrings state the full route.
The cube unit and all existing target signatures remain unchanged.

Mathlib LeanSearch returned Internal Server Error, recorded as unavailable without an
absence verdict. LeanFinder, Loogle and local source searches ran; no exact quasi-coherent
scheme Kunneth or scalar external-cup pullback theorem was found.

## New nodes

`lem-sc-picard-kunneth-qcoh-iso-exists`: the canonical isomorphism clause, proved in words
by Steps 1--7 of the original node, with integer-to-natural degree reindexing and the
pure-tensor characterization. Its Lean declaration is in
`lean/Sheaf/AlgebraicGeometry/PicardKunnethQcohIso.lean`.

`lem-sc-picard-kunneth-qcoh-functoriality`: the independent pullback-compatibility clause,
proved in words by the original Step 8, with coefficient identification and arbitrary
target-cover comparison. Its Lean declaration is in
`lean/Sheaf/AlgebraicGeometry/PicardKunnethQcohFunctoriality.lean`.

Both nodes inherit chapter `sec-abelian-varieties`, unit `sk-prop-av-cube`, and the
blueprint ancestor `thm-sc-theorem-of-cube`, with the full via chain. No change record
is needed: existing signatures, definitions, and public imports are unchanged.

## Second reading by X3

1. Compared the delivered parent module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only the proof
   imports and proof body changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The parent has no
   `sorry`; the two explicitly split child theorems each contain exactly the named
   `sorry`, with no axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. Reviewed the two split statements and their DAG records. Each is a strict conjunct of
   the parent (isomorphism characterization and pullback compatibility), has a complete
   source and proof route in its docstring, and is not duplicated elsewhere. Verdict:
   pass; the decomposition is necessary because the geometric arguments remain open.
4. Checked the parent proof against the child declarations and checked imports. The
   parent uses exactly the two child theorems; proof-only imports were moved into the
   child modules and the removed imports are listed above. Verdict: pass.
5. Checked the DAG proof steps, dependencies, chapter and unit fields. The parent node
   records both child dependencies, and both child nodes retain the cube unit route and
   their stated proof origins. Verdict: pass.

Changed during this second reading: no Lean declarations or statements; added this
review section only. The delivery remains a one-hole-to-two-hole decomposition with
the parent proof closed.
