## What changed

Proved `AlgebraicGeometry.Scheme.reduced_artinian_tensor_normalization_charts`
with its existing signature and visibility unchanged. Added three fully proved public
helper modules: `FiniteAffineTensorBaseChange`, `FiniteAffineNormalizationCoproduct`,
and `ReducedArtinianAffineNormalizationCharts`. The target imports them only for its proof.
The base-change helper pulls back the disjoint coproduct cover and computes its projections.
The normalization helper constructs inverse maps by the universal property. The Artinian
helper decomposes the source into residue-field spectra and uses a proved affine
normalization identification. The final proof composes the selected chart inclusions.
Updated the existing DAG proof and added matching nodes for the new public theorems.
All four modules compile cleanly through lcompile.py, including universe u and empty families.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.reduced_artinian_tensor_normalization_charts`
(node `lem-sbc-reduced-artinian-tensor-normalization-charts`).
Added 0 holes; no `sorry` remains in any delivered module.
Also fully proved:
`AlgebraicGeometry.Scheme.finite_affine_tensor_base_change`,
`AlgebraicGeometry.Scheme.finite_affine_normalization_coproduct`, and
`AlgebraicGeometry.Scheme.reduced_artinian_affine_normalization_charts`.
The private finite-coproduct isomorphism, integrality induction and affine normalization
identification are all proved. No axioms, hollow definitions or arbitrary data chosen
from an unproved existence theorem were introduced.

## No longer needed

No repository imports, nodes or modules were removed; the old node had no proof dependencies.
Second reading removed redundant `Mathlib.RingTheory.TensorProduct.Basic` from the new
`FiniteAffineTensorBaseChange` module and redundant
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` from the new
`ReducedArtinianAffineNormalizationCharts` module. In the latter, `Limits` and
`Artinian.Module` are now proof-only imports, and `Artinian.Defs` is public for the signature. The original plan's separate theorem
that integral closure commutes with finite products is not needed: normalization's
universal property and the source's residue-field coproduct decomposition give the charts.
No extra localization theorem is imported; Mathlib's normalization construction already
contains the localization compatibility. A trial proof import of
`Mathlib.Topology.Category.TopCat.EpiMono` in the new base-change module was removed;
the retained imports provide the API it uses. The trial import was never in the repository.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's proof was a valid mathematical plan but had
no named proof dependencies for its geometric glue. The delivered route avoids its
product-integral-closure step. Source checks: Stacks 01JO gives affine tensor pullbacks;
035H defines relative normalization; 035I gives the universal property used here;
0307 explains localization compatibility already built into Mathlib.
The unit's spreading theorem and its realized steps remain untouched.
Edge cases: the finite-integrality induction handles r=0 explicitly, and a zero Artinian
ring has empty maximal spectrum; the coproduct-cover selection therefore never assumes
nontriviality or an inhabited family. Quotient algebra structures are explicitly the
quotient of the actual includeRight structural map.

## New nodes

`lem-sbc-finite-affine-tensor-base-change` records the fully proved base-change identification,
without Artinian/reduced or normalization hypotheses. Module: `FiniteAffineTensorBaseChange`.

`lem-sbc-finite-affine-normalization-coproduct` records the fully proved finite normalization
coproduct isomorphism and each structural equation, without Artinian/reduced assumptions.
Module: `FiniteAffineNormalizationCoproduct`.

`lem-sbc-reduced-artinian-affine-normalization-charts` records the fully proved chart cover
for one reduced Artinian affine algebra, with no tensor base change or supplied source
coproduct. Module: `ReducedArtinianAffineNormalizationCharts`. It uses the preceding
normalization coproduct node, plus the private fully proved affine normalization lemma.

All three nodes belong to `sec-smooth-base-change` and `sk-prop-input-spreading` and carry
actual recorded Mathlib searches (LeanSearch unavailable, LeanFinder/Loogle and grep run).
No change record or forced adaptation is needed.

## Second reading by A3

1. Compared the existing delivered module with the repository by diff and checked its
   complete theorem signature byte for byte: unchanged. No existing definitions,
   visibility, hypotheses or conclusions changed. The only existing-node fields
   changed are `proof`, `proof_deps` and `proof_origin`; no change record is needed.
2. Independently compiled all four modules through lcompile.py with no errors or
   warnings. Scanned every delivered Lean source: no sorry, axiom, unsafe, opaque,
   implemented_by, extern or skipped kernel check. A scratch module with explicit
   `#print axioms` for the target and each of the three public helpers reports only
   propext, Classical.choice and Quot.sound. The private coproduct construction is
   explicit data; the affine isomorphism transports a constructed integral closure.
   No data is chosen from an unproved existence theorem. Verdict: genuine proofs,
   one original hole closed and zero holes added.
3. No statements remain split off with sorry. Read the three fully proved helper
   statements and their proofs: base change, finite normalization coproduct, and
   one-algebra residue charts are strictly separate parts of the argument. Checked
   r=0 in the integrality induction, empty coproduct covers, zero reduced Artinian
   rings (empty maximal spectrum), r=1 and quotient-induced algebra maps. Repeated
   LeanFinder, Loogle and grep searches with different wording and searched the
   project and upstream sources. Mathlib normalizationCoprodIso handles two
   summands; it does not state the delivered finite affine presentation theorem.
   The existing NormalizationStalkFieldCoproduct theorem imposes a stalk base and
   a supplied field presentation; its affine identification helper is private.
   It cannot replace these public helper statements. Verdict: true and useful,
   without duplicating an accessible theorem or restating the item.
4. Traced the target downward through the three helpers and Mathlib. The universal
   property proof directly constructs inverse maps; using the binary coproduct API
   recursively would require additional normalization transports and structural
   equalities, and offers no shorter route. All direct proof-helper imports are
   used. Repaired proof-only import visibility and redundant imports in the new
   modules as recorded above. The original proof_deps list was empty, so no old
   dependency node is omitted from No longer needed. Checked
   dag/units/sk-prop-input-spreading.json: its realized arrays are already empty;
   no unit statement, step, route or record is changed by this delivery. Verdict:
   no bypass of a realized unit step, and no existing module pruned.
5. Matched each node's Lean statement against its module, and verified proof_deps
   equals the union of proof-step uses. The target names precisely the three
   helpers its proof invokes; the one-algebra helper names the finite coproduct
   helper. New nodes contain source, proof in words, origin, recorded searches,
   created, blueprint, chapter, unit and complete Lean records. Verdict: nodes
   agree with the compiled proofs.

Changed during second reading: corrected the target's proof docstring to describe
its actual universal-property route rather than a product-integral-closure proof;
made the new affine helper's Limits and Artinian.Module imports proof-only with
public Artinian.Defs, removed two redundant imports from the new modules, and
updated this report. No proof body or declaration signature needed repair.
