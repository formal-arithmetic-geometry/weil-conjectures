## What changed

Corrected `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_isSeparable`
to require `hAlgebra : algebraMap κB k′ = (Spec.preimage ρB).hom`.
The previous arbitrary instance was unrelated to the geometric hypotheses and
made this intermediate statement false. The correction and its only forced
caller adaptation are recorded in
`coord/changes/compatibleStrictHenselization_residue_isSeparable.md`.

Proved the corrected theorem using a single-model residue comparison, the proved
private field-point factorization lemma `residue_factorization_descends`, and
Mathlib `IsSeparable.map` and `IsSeparable.tower_top`. The private helper constructs
the base residue embedding into κB from `SpecToEquivOfField`, transports across
the equality of image points, and cancels `fromSpecResidueField`.

Added the proved module
`Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel` and its node.
Its statement transports residue separability and the structural factorization
from the coordinate colimit to any affine local model. The second reading found
the existing `AlgebraicGeometry.strictHenselizationResidue` in
`Sheaf.Paper.StrictHenselizationFunctoriality` and used it to close the initial
single-model hole. Its complete transport argument is in the docstring and node.

Adapted the sole caller in
`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial` by
appending `rfl` to its invocation. Every other byte of that module is unchanged.
No definition or Challenge target changed.

## Proved and sorry left

Closed the one original hole, with the documented correction of its false
algebra-instance interface:
`AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_isSeparable`,
node `lem-weil-pbc-compatible-strict-henselization-residue-separability`.

Also proved the private helper
`AlgebraicGeometry.residue_factorization_descends` and the new theorem
`AlgebraicGeometry.Scheme.strictHenselization_residue_separable_model`,
node `lem-weil-pbc-strict-henselization-residue-separable-model`.
There are no added or remaining holes in the three delivered modules, and no
holes inside definitions. The caller's polynomial theorem remains proved with
its original signature. Direct holes closed: one; holes added: zero. This final
delivery is not a decomposition. The pinned ledger determines project-wide net
progress after landing.

Validation: all three modules compile in import order with `lcompile.py --all`.
Scratch copies with `#print axioms` show precisely `propext`, `Classical.choice`,
and `Quot.sound` for the original theorem, private helper, model theorem, and
polynomial theorem; no `sorryAx` is reachable. The original caller fails against
the changed dependency, while the adapted caller compiles.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`
and `Sheaf.RingTheory.StrictHenselizationTriples` from the item. The old
`proof_deps` nodes `lem-weil-pbc-etale-local-ring-triples` and
`lem-weil-pbc-strict-henselization-triples` are no longer direct proof dependencies.
The model module also removes those imports, using the proved existing residue
comparison from `Sheaf.Paper.StrictHenselizationFunctoriality` instead. The two
old modules remain in that theorem's import closure. No module is pruned from
the targets' import closure. No node of `dag/units/sk-thm-p1.json`'s `realized`
statement or steps is bypassed.

The second reading also removed the unused local `b` in the item's proof.
The earlier unused derivative module and node were already discarded by the
first worker and are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The original statement used an arbitrary `Algebra κB k′` without requiring its
algebraMap to equal the map induced by ρB. The change record gives a
characteristic-zero counterexample: two embeddings of an algebraic closure of
Q(t) into an algebraic closure of Q(t,u), sending t to u and t to t respectively.
Separability for the geometric embedding need not even be algebraicity for the
other embedding. The sole caller already uses the geometric algebra structure.
No compiled geometric counterexample is claimed.

The first worker missed the existing pointed residue comparison in
`Sheaf.Paper.StrictHenselizationFunctoriality`. The second reader found it by
searching for residue extensions, pointed maps and henselization isomorphisms.
Transporting it proves the single-model theorem without a new geometric hole.

Sources checked independently at the official Stacks pages: Tags 04HX and
04GP (5) identify the residue closure and its affine/triple colimit description;
Tag 095T uses the inclusion of these geometric residue closures.

## New nodes

`lem-weil-pbc-strict-henselization-residue-separable-model`: the residue field
of an affine local strict-henselization model is separable over its base image
point's residue field, with the closed-point structural factorization. This is
a proved transport consequence of `strictHenselizationResidue`, rather than a
new unresolved identification. Its witnesses are used only within theorem
proofs. It has no compatible second model or arbitrary auxiliary embedding.
Field bases give their separable closures; positive characteristic asserts
separability, not perfectness. Empty schemes admit no geometric point or model;
nonreduced local models are covered by the actual maximal-ideal quotient.

The change record is
`coord/changes/compatibleStrictHenselization_residue_isSeparable.md`.

Searches: the first worker used LeanFinder and Loogle for `IsSeparable.map` and
`IsSeparable.tower_top`; LeanSearch was unavailable. The second reader used
LeanFinder with "spectrum of colimit of pointed etale neighborhoods residue field
algebraic separable extension", which returned the field-point APIs, and searched
Mathlib and both local library roots for residue separability, pointed evaluation
and henselization isomorphisms. This found `strictHenselizationResidue`, used in
the final proof. The new node records that search and the resulting route.

## Forced adaptations

`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial`
(unclaimed): compiling the original against the changed dependency fails at
its existing `hs x`:

```text
Application type mismatch: The argument x has type IsLocalRing.ResidueField A
but is expected to have type
algebraMap (IsLocalRing.ResidueField B) k′ = (Spec.preimage ρB).hom
in the application hs x.
```

The second reader independently reproduced this failure using a scratch copy.
Only line 75 changes: append `rfl` to the separability invocation. The preceding
local algebra is exactly `(Spec.preimage ρB).hom.toAlgebra`; the added equality is
reflexive. The adapted module compiles. All its signatures and visibility remain
identical. `tools/downstream.py --uses` finds only the item and this caller as
textual users, with 101 import descendants. No target's type or meaning changes.

## Earlier second reading (a previous round; superseded)

1. Compared both existing modules with the repository by `diff -u`. The sole
   signature change is the declared `hAlgebra` correction, recorded verbatim
   in the change record and node. The polynomial caller differs by exactly
   one appended `rfl`. No existing definition or visibility changed. Verdict:
   the statement correction is necessary; no accidental interface change.
2. Compiled all three final modules in import order. Scanned them for `sorry`,
   axioms and prohibited commands. Printed axioms in scratch copies for every
   theorem, including the private helper. Only the three permitted axioms occur;
   there is no `sorryAx`. Independently compiled the original caller against the
   changed dependency and reproduced the claimed forced error. Verdict: kernel
   proofs with the necessary caller adaptation.
3. Checked the single-model assertion against the actual colimit definition and
   Stacks 04HX/04GP, including field, empty, nonreduced and positive-characteristic
   cases. Searched with different terms and found the existing pointed residue
   theorem. Used it to prove the new assertion. The original two-model argument
   genuinely assembles this transport with residue factorization and separability
   descent; it is not a renamed restatement. Verdict: true new lemma, zero holes
   split off, no data chosen from an unresolved existence theorem.
4. Checked the route from the top, then the field-point algebra assembly and the
   model transport. Proof imports are private; public imports are used in the
   signatures. Removed the unnecessary local `b`, replaced the model's direct
   triple imports with its existing proved comparison, and listed both old
   proof-dependency nodes above. The `sk-thm-p1` realization is preserved. Verdict:
   shorter existing-library route used; no unit bypass or claimed module pruning.
5. Compared Lean signatures with both node `lean.statement` records. The item's
   steps and proof dependency describe the model reduction; the new node now
   records the existing functoriality residue theorem and the actual quotient,
   field-point and separability transport. Source and statement-change records
   agree with the final Lean. Verdict: DAG follows the implemented proof.

Second-reading changes: closed the new single-model hole using the existing
`strictHenselizationResidue`, updated its docstring, imports and node proof route,
removed the unused local `b`, and rewrote the report/change record to reflect
zero added holes. Kept the correct geometric compatibility argument and the
necessary interface correction.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial
Original against changed dependencies failed:
```
/tmp/forced-adaptation-5tulau_d/lean/Sheaf/AlgebraicGeometry/CompatibleStrictHenselizationResiduePolynomial.lean:78:37: error: Application type mismatch: The argument
  x
has type
  IsLocalRing.ResidueField A
of sort `Type u` but is expected to have type
  algebraMap (IsLocalRing.ResidueField B) k' = CommRingCat.Hom.hom (Spec.preimage ρB)
of sort `Prop` in the application
  hs x

(with the modules compiled into /tmp/forced-adaptation-5tulau_d/.lbuild) [10.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

The whole-blueprint search was recorded for the repair: `python3 tools/blueprint_refs.py search strict henselization residue` found only the broader ancestor statement `lemma-weil-pbc-p1-exchange-geometric-stalk`, not an exact duplicate. The repaired blueprint therefore points to that ancestor and records the four via-nodes required by the reviewer.

## Second reading by B3

1. Compared the item and adapted caller with the repository versions. The only
   interface change is the documented `hAlgebra` equality; the caller adds only
   the forced `rfl` argument, and the new model module is separately recorded.
   Verdict: no accidental statement or definition changes.
2. Compiled all three modules with `lcompile.py --all`, and inspected the
   declarations for prohibited commands and unfinished proofs. Scratch
   `#print axioms` checks contain only the permitted axioms and no `sorryAx`.
   Verdict: the delivered proofs compile cleanly.
3. Checked the corrected compatibility hypothesis and the model theorem on
   field, empty, nonreduced, and positive-characteristic cases. The model
   theorem transports the existing `strictHenselizationResidue` result; the
   factorization helper is a strictly smaller algebraic reduction. Verdict:
   statements are true and exactly as strong as required; no holes were added.
4. Checked the proof route and imports. The model proof uses the existing
   functoriality residue comparison, and the item uses that model theorem plus
   separability transport. The two old triple imports are removed and their
   nodes are listed as no longer direct dependencies. Verdict: route is short,
   unit `sk-thm-p1` is preserved, and pruning is complete.
5. Compared DAG `lean.statement`, proof steps, dependencies, and source/change
   records with the Lean declarations. The new model node and corrected item
   node match their modules, and the forced adaptation record explains the
   exact caller edit. Verdict: DAG and Lean agree.

Second-reading changes: added this review record, closed the model proof using
existing residue comparison, removed an unused local, and kept the required
geometric algebra compatibility correction. No additional holes were introduced.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial
Original against changed dependencies failed:
```
/tmp/forced-adaptation-q7zxa7wn/lean/Sheaf/AlgebraicGeometry/CompatibleStrictHenselizationResiduePolynomial.lean:78:37: error: Application type mismatch: The argument
  x
has type
  IsLocalRing.ResidueField A
of sort `Type u` but is expected to have type
  algebraMap (IsLocalRing.ResidueField B) k' = CommRingCat.Hom.hom (Spec.preimage ρB)
of sort `Prop` in the application
  hs x

(with the modules compiled into /tmp/forced-adaptation-q7zxa7wn/.lbuild) [2.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
