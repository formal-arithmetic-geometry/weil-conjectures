## What changed

The signature and visibility of
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model`
are unchanged. Its proof is now a complete Lean assembly. A proved private helper
identifies the cover over any base mapping into D(f) as a finite etale surjective
base change of the original torsor, using beta, the range formula for open
immersions, and pullback pasting. If g is a unit, the root puncture is the whole
spectrum and this proves the conclusion directly. In the nonunit case the proof
applies the existing regular-integral-divisor purity theorem to the new finite
normalization data, composes its restriction isomorphism with the cover
identification, and checks the projection equation.

Surjectivity is proved here: canonical structural flatness preserves the
nonzerodivisor, freeness of the positive-degree monic root algebra preserves it
again, and injectivity of localization gives density of the puncture. The
restriction isomorphism and torsor surjectivity put this puncture in the finite
image. Closedness of that image makes it the entire spectrum.

`StrictHenselizationStructuralFlat.lean` proves canonical structural flatness
from the existing `RingHom.Flat.of_isColimit` theorem. The small representative
category is cofiltered, every stage is etale and flat over R, the stage maps
form a natural transformation, and the defining structural-map characterization
identifies their colimit composite with b. This theorem has a real proof and
introduces no hole.

`StrictHenselRootPurityData.lean` states the remaining geometric construction:
for nonunit g, it supplies the regular integral root Cartier divisor and a
finite normalization model etale on the puncture and near the divisor generic
point. It does not assert an everywhere-etale extension or surjectivity.
Its source and full argument are in its docstring and its node. Finiteness
uses the tame-normalization result 0EYH, not an unmentioned excellence assumption.

The main module adds proof-only imports of the two new modules, the existing
`RegularIntegralDivisorEtalePurity` module, Mathlib's isomorphism criterion,
and Mathlib's flat-module lemmas. The structural-flatness module uses proof-only
imports of the existing colimit-flatness source module and etale morphisms.
The existing node now records the actual four-step Lean assembly. No other
existing module is changed. The blueprint unit's trait/root/purity route is kept.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model`
(node `lem-sbc-strict-hensel-root-finite-etale-model`): 1 of 1 original holes.
The main module has no remaining sorry.

Also proved the new supporting theorem
`AlgebraicGeometry.Scheme.strictHenselization_structural_ringHom_flat`
(node `lem-sbc-affine-strict-henselization-structural-flat`) and the private
`cover_pullback_properties` helper.

Added exactly one hole:
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data`
(node `lem-sbc-strict-hensel-root-purity-data`). Its proof is exactly `by sorry`
in its own new module. This delivery decomposes the original geometric proof;
the existing purity theorem and its lower dependencies are reused and are not
claimed to be sorry-free. The net change in directly introduced holes is zero:
one original hole closed and one simpler finite-model hole added.

## No longer needed

No original import is removed; no mathematical dependency module is pruned.
The original direct regular-ring and strict-henselization definition dependencies
are now used through the finite-model and flatness nodes. Their notions remain
needed, so this is not counted as pruning. No root-splitting or prescribed-chart
module is imported: those modules already reach this item and would close an
import cycle. No section or splitting result is needed by the finite model theorem.
Specifically, the old direct `proof_deps` entries `def-weil-regular-scheme` and
`def-weil-pbc-strict-henselization-limit` are replaced by the two new bridge
nodes; neither definition module is pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The original module did not import the stated regular-divisor purity dependency;
that proof-only import is now present. The plan's reference to strict henselization
flatness had no declaration specialized to this canonical ring structural map;
the new theorem proves that missing bridge from the existing filtered-colimit
flatness theorem. The Abhyankar-to-purity passage lacked Lean data describing
the root Cartier divisor and the finite model with its generic-point etale
neighbourhood; the new finite-model statement makes that passage precise.

No mathematical statement was changed or disputed. The source paragraphs were
read in Stacks Tags 09EB, 0BRM, 0EYG, 0EYH and 0EYE. The literature sources listed
as obtained are absent from this clone, so the corresponding official tag pages
were read directly. LeanSearch returned Internal Server Error, recorded as
unavailable; LeanFinder, Loogle and Mathlib grep searches are logged.

Edge cases: a finite group has positive cardinality, making the root polynomial
monic of positive degree. The unit-equation case is proved without a divisor,
normalization or purity. In the nonunit case the actual strict henselization has
a nonzero regular local quotient by g, so the root divisor is nonempty and
integral. Empty ambient schemes cause no change to the generic-point argument:
the finite-model lemma is only invoked when its nonunit hypothesis applies.
No data is chosen inside a definition from a mere unproved existence theorem;
all finite-model witnesses are eliminated within a proof of a proposition.

## New nodes

`lem-sbc-affine-strict-henselization-structural-flat` records the proved flatness
bridge for the canonical affine strict henselization ring map. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat`.

`lem-sbc-strict-hensel-root-purity-data` records the one remaining finite tame
normalization construction in the nonunit case. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData`. Its conclusion
is the input to the existing purity theorem; it is strictly a part of the original
argument. The generic point is packaged as an explicit witness with dense singleton closure;
its uniqueness in the integral scheme identifies it with the canonical generic
point when applying purity. The main module proves the unit case, purity assembly, and surjectivity
rather than handing its original conclusion to this lemma.

No change record is needed: existing signatures, definitions, and visibility
are unchanged, and there are no forced adaptations.

## Second reading by H2

1. Compared the delivered main module with the repository version. Existing
declaration signatures and definitions are unchanged; the only additions are
proofs, proof-only imports, and the two supporting modules declared in this
delivery. Verdict: pass.

2. Compiled all three sandbox modules with `lcompile.py --all`. The main target
has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the
single remaining `sorry` is the named purity-data theorem and is documented by
its node and source. An appended scratch-copy `#print axioms` check reports
only `propext`, `Classical.choice`, and `Quot.sound` for structural flatness;
the main theorem and purity-data theorem additionally report `sorryAx`, as
expected from the remaining geometric inputs. Removed the scratch copy after
compilation. Verdict: pass.

3. Checked the split-off purity-data statement and structural-flatness bridge
against their nodes and docstrings. The former is a strictly smaller finite
normalization input to the existing purity theorem; the latter is the exact
flatness fact used by the density argument. Both are true at the stated
strength, and no duplicate declaration was found. Verdict: pass.
Independent LeanFinder search used "finite cover tamely ramified along a regular
Cartier divisor ... Kummer root base change"; its normalization and unramified
hits do not supply this statement. Loogle search for colimit ring-map flatness
returned no hit. Repository searches for normalization finiteness and strict
henselization flatness found no replacement for the two new declarations.
Read Stacks Tags 0BRM, 0EYG, and 0EYH directly. For the trivial group the root
ring is H and the same finite-model construction applies; nonunit g guarantees
the divisor is nonempty. The unit case is handled separately in the main proof.

4. Checked the proof route and imports. The unit route through the root algebra,
finite model, and divisor purity is retained. The added imports are proof-only
where appropriate, and no unused original dependency was removed. Verdict:
pass.
The unit's `realized` fields are currently empty in the repository, an existing
blueprint incompleteness; this delivery leaves them unchanged and follows the
written trait/root/purity route.

5. Checked all node metadata against the Lean declarations and proof uses. The
main node records the four-step assembly, and each new node records its own
statement, source, dependencies, and split status. Verdict: pass.
Verified mechanically that each node's recorded Lean signature occurs verbatim
in its module and that `proof_deps` is exactly the union of the proof steps'
`uses`. Only `proof`, `proof_deps`, and `proof_origin` change in the existing node.

Changed during second reading: added this required review section only; no Lean
source or node content was changed.
