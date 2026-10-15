## What changed

Proved `AlgebraicGeometry.affineClosedSpecializationLocalization` in the item module. The
proof uses the localization weakly-etale theorem, the affine weakly-etale equivalence,
Mathlib's localization spectrum range and embedding results, and maximal-ideal existence.
The proof-only imports were pruned to `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`;
`Sheaf.RingTheory.IndPrincipalZariski`, the direct weakly-etale ring import, and the direct
`Mathlib.RingTheory.Ideal.Maximal` import are no longer needed; the latter two are supplied
transitively by the retained imports.

## Proved and sorry left

The theorem `AlgebraicGeometry.affineClosedSpecializationLocalization` is proved with no `sorry`.
Holes closed: `AlgebraicGeometry.affineClosedSpecializationLocalization` (one).
Holes added: none. Sorries left in the item: none. No new declarations were added.

## No longer needed

The proof does not use `Sheaf.RingTheory.IndPrincipalZariski`, the direct import
`WeilConjectures.Mathlib.RingTheory.Etale.Weakly`, or the direct import
`Mathlib.RingTheory.Ideal.Maximal`. The only old proof-dependency node no longer used is
`lem-weil-pbc-spec-localization-away-basic-open`. The localization embedding, localization
weakly-etale, and maximal-ideal inputs remain used. The definition node
`def-weil-pbc-ind-etale-algebra` also remains used: its recorded declaration
`AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff` supplies the affine equivalence,
now imported directly from its defining upstream module. Removing the larger
`Sheaf.RingTheory.IndPrincipalZariski` import does not remove this logical dependency. The final specialization clause is obtained directly
from `IsLocalization.under_le_under_iff` and ideal order, so no basic-open argument is needed.

## Where the brief, the DAG or earlier work was wrong

The planned proof's basic-open specialization step is unnecessary: localization ideals are
order-embedded by `IsLocalization.under_le_under_iff`, which gives the required specialization
immediately from the contracted ideal inclusion.

## Second reading by D4

1. Interface: compared the entire delivered Lean module with the repository using `diff`.
   The sole existing declaration's signature is byte for byte identical through `:= by`;
   its docstring, universe, namespace, public section and five public imports are unchanged.
   Only proof-only imports and the proof body changed. There are no definition changes,
   added declarations, adapted modules, or change records. The node's mathematical statement
   and statement dependencies are unchanged.

2. Proof: compiled the delivered module through `lcompile.py`, cleanly in 2.3 seconds.
   Compiled a scratch copy containing the entire proof followed by `#print axioms
   AlgebraicGeometry.affineClosedSpecializationLocalization`, cleanly in 2.7 seconds:
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Checked the source for `sorry`, axioms, unsafe/opaque declarations, foreign implementations
   and skipped kernel checking: none. There are no definitions or hidden witness constructions.

3. Split statements: none were introduced, so there is no relabelled hole or new-node search
   obligation. Checked the original statement against
   [Stacks 096V](https://stacks.math.columbia.edu/tag/096V), with `f = 1`, and the flatness
   definition in [Stacks 092B](https://stacks.math.columbia.edu/tag/092B).
   Read the upstream localization weakly-etale theorem and the affine equivalence.
   For `I = top`, every element is a quotient unit, the localization has empty spectrum,
   and all image/specialization clauses are empty. For `I = bottom`, `S` consists of units,
   the spectrum map is an equivalence and each point may specialize to itself. The zero ring
   is covered by the empty-spectrum case. No nontriviality, finite-generation or Noetherian
   assumption is introduced.

4. Route and pruning: read every proof step. A quotient inverse lifted to `A` excludes
   intersection of `S` with a prime contained in one above `I`. Conversely, a decomposition
   of `1` in `p + I` contradicts disjointness, so `Ideal.exists_le_maximal` supplies a prime
   above both. The range theorem and embedding are precisely the two recorded Mathlib
   declarations. For the final clause, contraction reflects ideal order by
   `IsLocalization.under_le_under_iff`; `PrimeSpectrum.le_iff_specializes` has the required
   direction. Loogle independently returned that exact order-reflection lemma; a fresh
   quotient-unit grep found only specialized nilpotent-ideal facts. Library searches found
   no duplicate of the complete theorem. The existing direct argument is sound and needs
   no rewrite. All added imports are proof-only; the removed maximal-ideal and ring imports
   are supplied transitively. `dag/units/sk-thm-properbasechange.json` was read: the item and
   removed basic-open node are not any of its `realized` statement/step nodes, and the
   unit's projective-line, reduction and torsion-assembly route is preserved.

5. DAG: compared the delivered node with the repository, read the dependency nodes and their
   Lean records, and matched their statements against the proof. The first worker had
   removed `def-weil-pbc-ind-etale-algebra` even though its recorded affine equivalence is
   used. Restored it in step 1 `uses` and `proof_deps`, and explained the direct-module import
   in that step. The union of `uses` now equals `proof_deps`. The other retained dependencies
   are exactly localization weak etaleness, localization spectrum embedding/range, and
   maximal-ideal existence. `proof_origin` describes the actual document/Mathlib route.
   Only permitted node fields differ; there are no new nodes needing stage-3 fields.

Second-reading changes: corrected the DAG's affine-equivalence dependency and the report's
pruning claims; added the missing removed `Mathlib.RingTheory.Ideal.Maximal` import to the
report and made the one closed / zero added holes explicit. The Lean proof needed no repair.
