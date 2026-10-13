## What changed

Reduced `AlgebraicGeometry.exists_affineSpecifiedModelChainComparison` with its
signature and public imports unchanged. The proof constructs the pushout ring
diagram and initial map, proves bounded finite projectivity of both extended
complexes, and combines two separately stated comparison steps.

`AffineBaseChangeRingDiagram` gives explicit constructions using `Under.post`
and `Under.pushout`. `AffineModelComparisonData` is the explicit proposition
of scheme-derived equivalences, object isomorphisms, and two coherence equations
on sheafified chain maps. Neither definition contains a hole or selects a witness
from unproved mere existence. The new pushout definitions are marked irreducible
for elaboration; their actual bodies remain available to the kernel.

`AffineBaseChangeModelComparisonIsos` supplies the geometric comparison data
for the constructed diagram and its colimit cocone. It has no module-derived
category assumption and makes no module-derived Hom assertion.
`AffineModelHomTransportAssembly` converts supplied comparison data into Hom
equivalences and their two equations for arbitrary F, cocone C, and complexes E,K.
It does not construct the ring diagram or prove finite projectivity.

Its private `exists_affineTildeHomEquiv` is proved from the existing affine
quasi-coherent derived equivalence: full faithfulness and conjugation by the
localization factorization give a Hom equivalence with the chain-map formula.
The unfinished public assembly step has a full proof in words and its own node.
No existing dependency is adapted. The second reader restored the original target
docstring, made the new geometric module's scheme-isomorphism proof import private,
and corrected the ring-diagram node's description of its concrete definitions.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_affineSpecifiedModelChainComparison`
(`lem-pc-affine-specified-model-chain-comparison`). Its module has no holes.
The private `scalarExtension_bounded_finite_projective` is proved: `map_isZero`
retains the original bounds and tensor-product instances give finiteness and
projectivity termwise. The ring construction, comparison-data definition, and
private affine Hom helper also contain no holes.

Two new holes remain, each exactly `:= by sorry`, in separate modules with
source, complete proof in words, and matching node:

- `AlgebraicGeometry.exists_affineBaseChangeModelComparisonIsos`
  (`lem-pc-affine-base-change-model-comparison-isos`).
- `AlgebraicGeometry.exists_affineModelHomTransportAssembly`
  (`lem-pc-affine-model-hom-transport-assembly`).

This is a decomposition: one baseline hole closed, two new holes added, net
minus one. The new statements separate geometric comparison from categorical
Hom assembly; neither repeats the original hypotheses and conclusion. Existing
imported holes are unchanged. No sorry-free target is claimed.

## No longer needed

Removed the upper module's direct proof imports
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`. They remain needed below
the geometric step and affine Hom helper, respectively, so neither is globally
pruned. The assembly statement uses arbitrary F,C,E,K rather than importing the
specialized geometric comparison theorem. Its imports of affine derived
comparison and Mathlib's `HomCongr` are used by the proved private helper.

All six original proof dependencies remain needed as statement dependencies or
below these steps: `def-pc-scheme`,
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-affine-qcoh-derived-equivalence`, `lem-pc-perfect-hom-transport`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-pc-scheme-iso-derived-equivalence`. None is globally pruned. No existing module or node is claimed globally pruned. The
blueprint unit's realized statement and step lists are empty, and no realized
unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report claimed a compiling reduction without a completed
check. The construction and finite-projectivity argument are now written in
Lean, with shared comparison data to avoid repeatedly elaborating its large
formula. The categorical assembly proof was attempted through full faithfulness,
`Iso.homCongr`, and the private affine chain-map identity, but repeatedly exceeded
the 60-second compiler limit. The public assembly is therefore honestly left as
a named step, rather than claimed proved. The attempted proof is retained only
in scratchpad and is not part of the delivery.

The geometric step is strictly separate: it supplies equivalences of different
scheme-derived categories and coherent object comparisons. The categorical
step accepts arbitrary diagrams, cocones, and complexes and does not require
boundedness or projectivity. The original theorem genuinely proves the ring
construction and the two finite-projectivity conclusions before combining them.

No false statement was found or existing signature changed. Mathematical edge
cases checked: singleton index preorders, zero rings and empty spectra, zero
complexes, and empty support intervals. The support argument needs no flatness
of the ring maps. Supplied t,e,he are retained. No finite-presentation hypothesis
on s is introduced. Affine derived full faithfulness allows arbitrary complexes.

Sources read: Stacks Tags 09RE, 06Z0, and 08DW. LeanFinder, Loogle and grep
searches found no existing combined statement. `Iso.homCongr` and the existing
`exists_affineQCohDerivedEquivalence` give the categorical route. Earlier logged
LeanSearch requests returned Internal Server Error; their unavailable results
are not treated as no matches.

## New nodes

- `def-pc-affine-base-change-ring-diagram`: actual pushout diagram construction.
- `def-pc-affine-model-comparison-data`: explicit coherent comparison proposition.
- `lem-pc-affine-base-change-model-comparison-isos`: remaining geometric step.
- `lem-pc-affine-model-hom-transport-assembly`: remaining categorical step.

Node proof descriptions and dependencies follow this reduction. There are no
change records or forced adaptations.


## Second reading by M2

1. **Interface comparison — PASS.** Diffed the existing module against the
   repository and checked its theorem signature byte for byte. There is no
   added hypothesis, changed conclusion, changed existing definition or public
   import change. The only existing node changes are `proof`, `proof_deps`, and
   `proof_origin`. Four new modules and their four nodes are explicitly reported;
   no change records or adaptations are required. Restored the existing theorem
   docstring byte for byte rather than extending its API documentation.
2. **Kernel and holes — PASS.** Compiled all five delivered modules through
   `lcompile.py --all`, then compiled scratch copies with explicit `#print axioms`
   for every public declaration and both private proved helpers. The only direct
   holes are the two public named theorems listed above. No definition contains a
   hole, and no prohibited axiom or implementation escape is present. The ring
   constructions are actual Mathlib colimit constructions; no definition selects
   arbitrary data from an unproved existence theorem. Axioms are confined to
   `propext`, `Classical.choice`, `Quot.sound`, and inherited or listed `sorryAx`.
3. **Split statements — PASS AS DECOMPOSITION.** Read both full signatures,
   their docstring arguments and their nodes. The geometric step supplies coherent
   scheme equivalences and object comparisons but no module-derived Hom result.
   The assembly step assumes those comparisons for arbitrary F,C,E,K, and neither
   constructs the ring diagram nor asserts finite projectivity. Neither restates
   the original item. Checked singleton tails, zero rings/empty spectra, zero
   complexes, and empty support intervals; all are compatible with the stated
   constructions. No flatness or finite-presentation assumption is silently needed.
   Independent LeanFinder and Loogle searches used categorical full-faithfulness
   and localization terminology, and grep searched tilde/Hom, base-change and
   K-flat natural comparison terminology in both library roots. Existing affine
   equivalence and `Iso.homCongr` are already reused. Read Stacks Tags
   [09RE](https://stacks.math.columbia.edu/tag/09RE),
   [08DW](https://stacks.math.columbia.edu/tag/08DW), and
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0).
4. **Route and pruning — PASS.** The upper proof constructs F,r and proves both
   bounded finite-projective clauses before combining the strictly separate
   geometric and Hom steps. The private Hom helper already uses the shortest
   affine full-faithfulness/conjugation route found. The removed direct proof
   imports remain needed below, and all six old proof-dependency nodes are
   accounted for above; no module is globally pruned. The unit
   `sk-thm-picard-semicon` has `realized.statement = []` and `realized.steps = [[]]`;
   its statement and perfect-complex/base-change proof route are preserved.
   Made `SchemeIsoDerivedEquivalence` a plain proof import in the new geometric
   module because its signature does not require that module's theorem.
5. **DAG agreement — PASS.** Read all five node files. Their recorded Lean
   signatures match the source modulo whitespace, and the existing signature
   is byte-identical to the repository. Proof-dependency lists equal the unions
   of their proof-step uses. The four new records have sources, search records,
   split status, creation/item/group metadata, blueprint ancestry, chapter/unit
   and Lean records. Corrected the ring construction node's inaccurate claim
   that its actual `def` declarations were `abbrev`s.

Changes by this reader: restored the existing docstring; privatized one proof-only
import; corrected the construction metadata and made the retained old dependency
list explicit. Tried closing categorical Hom assembly with the existing helper
and congruence, keeping definition transparency restricted; this exceeded the
60-second compiler limit, so restored its reviewed named hole. The time limit
was not raised and no declaration was split to evade it. The final delivery is
one original hole closed, two strictly smaller holes added (net minus one), with
no claim of a sorry-free proof or global pruning.
