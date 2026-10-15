## What changed

Proved `PrimeSpectrum.wLocal_clopen_partition_properties` with its signature and public
imports unchanged. The file now uses only its original public import
`WeilConjectures.RingTheory.ProEtale.WLocal`.

The existing source library supplies a proved homeomorphism from closed points to connected
components. Its inverse composed with the component projection is a continuous retraction.
Partition parts lift by inverse image; clopen membership is constant on connected components,
which proves uniqueness. Restriction gives the converse. Closed specialization and injectivity
on closed-point component classes prove the final open-containment clause.

Patch compactness is the Mathlib instance. Patch Hausdorffness is proved directly: refine an
open distinguishing two primes by a compact open, which is clopen constructibly. The resulting
total separation implies Hausdorffness. The closed-point profiniteness instances already exist
in the source library.

Updated the item's DAG proof and dependencies. Added one DAG attachment for the already proved
source homeomorphism; it adds no Lean module or proof obligation. Read the full source-library
proofs in WLocal/Basic, WLocal/ClosedPoints, WLocal/ConnectedComponents, Constructible, and the
connected-component API. Checked Stacks Tag 0968, `lemma-spectral-split`, including the final
assertion and the homeomorphism argument at the beginning of (2) implies (1).

## Proved and sorry left

Closed: `PrimeSpectrum.wLocal_clopen_partition_properties` (the module's sole original hole;
node `lem-weil-pbc-w-local-partition`).

Holes added: none. Sorries left in delivered Lean: none. This is a complete proof, not a
new decomposition. `#print axioms PrimeSpectrum.wLocal_clopen_partition_properties` returned
exactly `propext`, `Classical.choice`, and `Quot.sound`.

The final file compiles cleanly using `lcompile.py` in approximately two seconds. The proof
covers the zero ring, the empty closed-point space, empty and arbitrary infinite index types,
and empty partition parts without nonemptiness assumptions or finite-support choices.

## No longer needed

Removed all five explicit proof imports:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff`
- `Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite`
- `WeilConjectures.Topology.SpectralSpace.ConnectedComponent`

The two removed Sheaf modules are unnecessary for this proof, including their holed declarations
`t2Space_constructibleTopology` and `AlgebraicGeometry.Spec.profinite_of_isMaximal`.
The other three imports are redundant; the source WLocal API already provides everything used.
In particular, the source connected-component module remains a transitive source dependency;
its proven results are not claimed to be globally pruned.

The item no longer directly uses these planned nodes:

- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-qcqs-scheme-spectral`
- `lem-weil-pbc-spec-localization-away-basic-open`
- `lem-weil-pbc-spectral-constructible-topology-hausdorff`
- `lem-weil-pbc-proper-ideal-contained-in-maximal`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`
- `lem-weil-pbc-zero-dimensional-spectrum-profinite`
- `lem-weil-pbc-quasicompact-components-clopen-intersection`

The last node's result is used internally by the already proved source homeomorphism; only the
item's direct dependence on it is removed. The affine-spectrum notion remains implicit in the
unchanged statement. No claim is made that other target branches stop using any listed module.
The quotient construction, two finite-cover arguments and partition-finiteness argument are
unnecessary: inverse image under the retraction preserves arbitrary unions directly.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface correction was needed. The DAG plan overlooked the proved
source homeomorphism and source closed-point profiniteness instances, and therefore planned
unnecessary quotient and compactness arguments. The route change is entirely below the unit
level; none of `sk-thm-properbasechange`'s realized statements or steps is bypassed.

Mathlib searches were run through msearch.py: LeanFinder and Loogle returned clopen/component
and preimage API, grep found no exact Mathlib theorem, and LeanSearch returned an internal
server error, recorded as unavailable. Direct source-library search found the exact theorem.
Blueprint searches for w-local connected, closed points components, and Tag 0968 found no
standalone blueprint node for the general source theorem. The existing profinite-component
ring-pullback node includes an affine special case together with substantially more ring theory;
none of that construction is imported here.

## New nodes

`lem-weil-pbc-w-local-closed-points-components-homeomorphism` attaches the existing proved
`WLocalSpace.isHomeomorph_connectedComponents_closedPoints`, its bundled
`WLocalSpace.closedPointsHomeomorph`, and its injectivity consequence
`WLocalSpace.closedPoints_eq_of_mk_eq`. Its hypotheses are the source `WLocalSpace` class:
spectrality, closed closed-point subset, and uniqueness of closed specializations. Its statement
holds for arbitrary w-local spectral spaces. Stacks Tag 0968 supplies the source; the Lean source
already contains the complete proof. No new module, sorry, or change record is required.

## Second reading by E2

1. **Visible interface: PASS.** Independently compared the sole delivered Lean module
   against the repository with `diff -u` and compared the full theorem signature as a
   byte string: identical. There are no new declarations, changed definitions, changed
   public imports, or adapted modules. Only the original proof, its proof-plan docstring,
   and five plain proof imports differ. No change record is needed.
2. **Proof and trust: PASS.** Read the complete proof and the source WLocal/Basic,
   WLocal/ClosedPoints, WLocal/ConnectedComponents, Constructible and connected-component
   arguments. Independently compiled the delivered file with `lcompile.py`: clean,
   approximately 1.9 seconds. A scratch copy with `#print axioms` for the target,
   the source homeomorphism, its bundled homeomorphism, its injectivity consequence,
   and the spectrality and compactness instances returned only `propext`,
   `Classical.choice`, and `Quot.sound` in every case. Delivered Lean contains no
   `sorry` or prohibited declaration/trust mechanism. The retraction uses the inverse
   of a proved bijection, so it makes no arbitrary choice from an unproved existence.
3. **Split statements and edge cases: PASS.** There are no split-off theorems or new
   holes. The sole added node attaches an already proved general source theorem,
   strictly a tool for the partition assertion; its hypotheses exactly match
   `WLocalSpace`. Checked the proof for the zero ring/empty spectrum, empty closed-point
   space, empty and singleton index types, empty parts, and arbitrary infinite index
   types: inverse images handle all cases without a finiteness or nonemptiness assumption.
   Fresh LeanFinder search for the quotient map restricting to closed points returned
   general connected-component quotient API, not this theorem. Fresh Mathlib grep for
   constructible Hausdorff/total-separation results found no shortcut; direct `rg`
   searches of Sheaf and the source library confirmed the already used source theorem.
4. **Route and pruning: PASS.** The proof starts with Mathlib compactness and a short
   compact-open separation argument, then uses proved upstream instances and the exact
   source homeomorphism. No unproved Sheaf theorem is needed. The retained public import
   is necessary for the statement's `IsWLocalRing`; there are no proof-only public imports.
   Independently compared old and new `proof_deps`: all nine removed nodes are listed
   under `No longer needed`, as are all five removed imports. Read the unit record
   `dag/units/sk-thm-properbasechange.json`: none of its realized statement or step nodes
   is removed or bypassed. This is a change below the unit level. Confirmed the
   homeomorphism and open-containment argument against
   [Stacks Tag 0968](https://stacks.math.columbia.edu/tag/0968).
5. **DAG agreement: PASS.** The existing node differs only in the permitted `proof`,
   `proof_deps`, and `proof_origin` fields. Its dependency set is exactly the union
   of its proof steps' `uses`. The five steps describe the actual Lean proof.
   The new node records the exact existing declaration, source and bundled consequences,
   creation provenance, blueprint attachment, unit/chapter and actual search results;
   its source proof and axiom checks confirm its closed status. No Lean obligation was
   hidden behind the added node.

Changes made by the second reader: appended this independent review and recorded fresh
searches. No repair to the Lean proof or DAG was needed. Holes closed remain
`PrimeSpectrum.wLocal_clopen_partition_properties` (1 of 1); holes added and split off: 0.
