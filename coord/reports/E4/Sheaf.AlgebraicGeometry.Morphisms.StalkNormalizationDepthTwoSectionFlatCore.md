## What changed

Repaired the returned duplicate-statement rejection by generalizing
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core` in
place. It now proves descent and openness for arbitrary finite p:E→L, locally
Noetherian L, and a flat test t:T→L whose pullback of p is flat and which meets x.
This is strictly the descent-and-openness part of the normalization argument,
and is no longer the same statement as the existing caller theorem.

Removed both duplicated private helper declarations. Their tensor and stalk
arguments are written inline in the generalized proof, so no helper theorem is
redeclared under the same or a different name. The original helpers in
SmoothLocalDepthTwoClosedFiberFlat are private and cannot be imported for use.
The existing caller imports the core, so using its complete theorem in the core
would create an import cycle. No renamed duplicate remains.

The only caller, `GaloisCover.stalk_normalization_depth_two_section_flat`, keeps
its signature and visibility exactly. Its forced proof adaptation obtains the
split formal test, transports flatness of the coproduct projection, and applies
the generalized core. Its original imports stay; only the necessary proof-only
formal-test import is added. Both existing DAG nodes follow this proof route.
The current H9 repair adds all seven recorded proof-dependency imports to the
formal-test module. The C1 repair adds PowerSeriesPuncturedSectionFullyFaithful,
a separate exact statement of Stacks 0EY9, and its node. The formal test imports
it proof-only and records its id in proof[3].uses and proof_deps.
All four delivered modules compile using lcompile.py --all.

## Proved and sorry left

The generalized `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
is fully proved with no sorry. This corrects and replaces the disputed old
interface; it does not claim a proof of that false old statement. The unchanged
caller theorem is proved from this core and the formal test.

Exactly two added holes remain:
- `AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_split_formal_test`,
  node `lem-sbc-stalk-normalization-split-formal-test`.
- `AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_section_fully_faithful`,
  node `lem-sbc-power-series-punctured-section-fully-faithful`.

Both are public named theorems with whole proofs `by sorry`. The original
core's disputed interface is retired by correction, not proved. The caller already had a proof in the repository baseline; its proof is adapted,
not counted as a newly closed textual hole. The one old core hole is retired
with its false interface, and two strict lower holes are added: textual net
minus one, with zero unchanged-statement holes proved. This is an interface repair and decomposition,
not a proof of the old statement or a net hole reduction. The generalized core
has no sorry dependency. There are no holes in definitions.

## No longer needed

Removed from the repository core: Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated,
Mathlib.AlgebraicGeometry.Morphisms.Smooth,
WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor,
WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale,
Mathlib.AlgebraicGeometry.Normalization, and Sheaf.RingTheory.Depth.
The proof-only StalkNormalizationSplitFormalTest import is absent from the core
and added to its caller. FunctionField and Geometrically.Connected appeared only
in the returned repair, not the repository baseline. The generalized
statement needs only Noetherian, Flat and Finite interfaces; its proof uses
FiniteFlatTargetLocus and RingHom.FaithfullyFlat.

The core no longer directly uses its two old proof dependencies,
lem-weil-pbc-flat-local-depth-formula and lem-weil-pbc-normal-local-depth-two.
The caller no longer directly uses those two or
lem-sbc-generic-fibre-action-extension and lem-sbc-normal-integral-generic-hom-full;
all four are instead dependencies of the formal test.
No node or module is globally pruned. The formal test is now a direct dependency
of the caller, not the core. FlatLocalDepthFormula, NormalLocalDepthTwo,
GenericFibreActionExtension and NormalIntegralGenericHomFull are used by the
formal calculation and remain on the unit route. The forced-adaptation rule
prevents unrelated pruning of the caller's pre-existing imports.

## Where the brief, the DAG or earlier work was wrong

The current return H9 correctly identified seven missing proof imports of
the formal test; all seven are now present in the prescribed position.
C1 correctly identified that depth-two uniqueness and the depth formula do
not supply 0EY9 full faithfulness. Its exact statement now has its own module,
node, source proof, searches, Lean attachment, import and DAG edge. The earlier
second reading overlooked both issues; its stale certification was removed
pending the dispatcher's fresh independent reading.

The earlier repair duplicated the caller's entire statement and two private
helper statements from SmoothLocalDepthTwoClosedFiberFlat. The returned
import_prune_check rejection correctly detected all three. Generalizing the
core to the actual reusable descent-and-openness step resolves the main
duplication; inlining eliminates the duplicate helper declarations entirely.
The first exploratory rename was discarded; it is not part of this delivery.
The original source-hypothesis omission and cone counterexample remain the
reason the disputed old interface cannot be proved. The caller still carries
all required source hypotheses, and the unit's formal splitting, descent and
openness route remains intact.

## New nodes

`lem-sbc-stalk-normalization-split-formal-test` gains its missing proof imports
and the 0EY9 dependency in its fourth step. It states the power-series test and G-indexed splitting isomorphism,
not the target flat neighbourhood. Its source, proof in words, edge cases and
Lean attachment are retained. Zero variables and trivial G are included;
no arbitrary object is defined from a sorry existence theorem.

`lem-sbc-power-series-punctured-section-fully-faithful` states Stacks 0EY9
exactly, using constantCoeff to identify Y_0 with Spec A and the inverse-image
open with V_0. Hom-set bijectivity expresses full faithfulness of the library's
actual finite-etale pullback functor. The module is
`Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionFullyFaithful`.
It contains a complete source proof, including the source's omitted injectivity
detail and the arguments behind 0EKP and 0EL8. Its two recorded dependencies
(Hartogs and the flat local depth formula) are imported proof-only.
Searches used leansearch (unavailable), leanfinder (eight irrelevant hits),
and Mathlib grep (zero hits); all are in searches.jsonl. Blueprint search for
0EY9 found no node; library matches cite it but do not state it. This is a
strict full-faithfulness ingredient, not a renamed normalization statement.
Checked d=1, nonnormal and disconnected rings/covers, and empty covers; there
is no extra normality assumption. d=0 is deliberately excluded as in 0EY9;
the formal-test argument treats it separately as the identity slice.

Change record: `coord/changes/stalk-normalization-depth-two-section-flat-core.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlat`
(unclaimed) fails unchanged against the generalized core at original line 118:

```text
Application type mismatch: hσ has type σ ≫ c = 𝟙 S
but is expected to have type ↥S
in stalk_normalization_depth_two_section_flat_core c ?m.403 hσ
```

The added proof import and replacement of lines 108–118 are necessary to supply
the new interface: obtain the formal test and its point, prove its pullback
flat, then apply descent and openness. No existing signature or visibility
changes. The old module was compiled against the changed overlay and failed;
the adapted module compiled with that same overlay. deliver3.py repeats both
the original-baseline and original-overlay checks. The previous independent
review described the returned version and is removed pending a fresh reading.


## Second reading by E4

1. Compared both existing modules with the repository using diff. The caller's
   signature and visibility are byte-for-byte unchanged. The core's changed
   signature is explicitly recorded in the change record and its node's
   statement_change, including the caller. No definition or Challenge target
   changes. Verdict: the declared interface repair is accurately scoped.
2. Independently compiled all four delivered modules with lcompile.py --all.
   Searched all delivered Lean text for forbidden declarations and sorry: only
   the two reported whole-proof public theorem holes occur; there are no data
   definitions. Compiled scratch copies with #print axioms for all four
   declarations. The generalized core uses only propext, Classical.choice and
   Quot.sound; the adapted caller and split statements additionally use sorryAx.
   Verdict: the core is proved, and the caller remains dependent on a named hole.
3. Read both split statements, their full docstring arguments and their nodes.
   Compared the full-faithfulness statement to Stacks 0EY9 and the formal split
   calculation to the final paragraphs of 0EYJ. The constant-coefficient
   restriction is exactly the zero-section restriction, with d positive in
   0EY9. Checked d=0 separately in the formal test, the trivial group, empty
   covers in 0EY9, and nonnormal/disconnected A for 0EY9. Generic rational-point
   data supplies the G-indexed splitting; no group-order assumption is used in
   this depth-two step. Neither split statement repeats the neighbourhood
   conclusion. Fresh leanfinder search for morphisms extending from the zero
   section found only standard-etale algebra lemmas; loogle query
   MvPowerSeries, Function.Bijective had no hits; Mathlib grep and library rg
   found no existing equivalent theorem. The existing power-series extension
   theorem requires a different open containing a closed-fibre generic point.
   Verdict: both holes are true strict ingredients, but neither has a short
   available proof that can be substituted here.
4. Read the tensor descent proof and FiniteFlatTargetLocus: lifting (z,b), local
   faithful flatness, and tensor injectivity prove precisely the generalized
   core. The caller transports coproduct flatness and applies that core.
   Searched Mathlib faithfully-flat and ring-hom flat files for a shorter
   composition descent theorem; the available base-change descent has a
   different scalar configuration, and the existing direct argument is sound.
   Core proof imports are private and necessary. The formal test now imports
   every one of its eight proof dependencies privately, including 0EY9. The
   caller's legacy imports are retained under the forced-adaptation scope.
   No longer needed lists every removed old core and caller DAG edge; these
   ingredients remain in the formal-test route. Read the unit's realized field
   (currently empty statement and step lists); no recorded realization is
   bypassed or changed, and its formal splitting/descent route is retained.
   Verdict: no further pruning is justified in this delivery.
5. Read all four node files and the change record against the Lean declarations
   and imports. proof_deps are the unions of the recorded step uses; the core
   uses FiniteFlatTargetLocus and the caller uses the formal test and core.
   New nodes contain sources, searches, creation/blueprint records, verbatim
   Lean attachments and whole proof plans. Verdict: records agree with Lean.

Second-reading changes: corrected the report's hole accounting: the baseline
caller was already a proof, and replacing the false core interface is not a
proof of an unchanged statement. Added this independent review and fresh search
evidence. No Lean proof, signature, import or node repair was needed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlat
Original against changed dependencies failed:
```
/tmp/forced-adaptation-b1i2t37p/lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationDepthTwoSectionFlat.lean:118:60: error: Application type mismatch: The argument
  hσ
has type
  σ ≫ c = 𝟙 S
of sort `Prop` but is expected to have type
  ↥S
of sort `Type u` in the application
  stalk_normalization_depth_two_section_flat_core c ?m.403 hσ

(with the modules compiled into /tmp/forced-adaptation-b1i2t37p/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
