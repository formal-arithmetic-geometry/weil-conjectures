## What changed

Repair upstream review #1424 by removing the deprecated theorem `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison` from `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` and replacing its nine proof occurrences in eight caller modules with `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. The canonical theorem and private single-complex helper are already proved on the baseline and are unchanged. No imports change. All nine delivered modules compiled without errors or warnings, each within 60 seconds (4.5–47.2 seconds). Static declaration comparison confirms that all eight callers preserve every existing signature and visibility. The change record is `coord/changes/ext-composition-remove-compatibility-alias.md`.

## Proved and sorry left

Baseline holes: 0. Holes closed: 0. Holes added: 0. Split off: 0. No sorry remains in the item or any delivered adapted module. `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq` and the private `singleComparison_hom` remain fully proved. This is duplicate-interface repair, not new proof progress or decomposition.

## No longer needed

The deprecated alias `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison` is removed. No imports, DAG dependencies, nodes or modules are pruned. Both existing imports are used: Ext.Map supplies the public statement and Shift.ExactFunctor supplies shift compatibility of the derived comparison.

## Where the brief, the DAG or earlier work was wrong

The generic brief says the module still contains sorry; the assigned baseline already has no holes and compiles cleanly in 6.1 seconds. The actual assignment is the duplicate repair listed in coord/repairs.txt. The earlier change record claimed the eight callers were adapted, but the current sources still use the compatibility alias. The referenced upstream comparison theorem is absent from the pinned source and Mathlib, as confirmed by source reading, rg, and the required LeanFinder/Loogle/grep searches through msearch.py. The general theorem is already available under the requested canonical name in the held module. Its node `lem-weil-pbc-ext-exact-functor-composition-comparison` already records the exact statement and proof route, so no node update is necessary. The unit route is preserved.


Dry-run tool failure: deliver3.py completed delivered-file compilation, original-versus-adapted
counterfactual compilation and all axiom probes, then preflight rejected the eight adaptations
with `unheld adaptation requires the item's own interface change`. Reproduction through
stage3_delivery.diff_module gives:

```text
removed: ['CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison']
interface: []
```

The original declaration starts with ` theorem exactFunctorCompositionComparison` (one leading
space). leanindex.py's `_HEAD` pattern starts at a declaration keyword at column zero, and
its command/interface parser therefore misses this removed public theorem. The declaration
parser used for `removed` recognizes it. stage3_delivery.check_changes then rejects each
forced adaptation at its `primary["diff"]["interface"]` test despite the removed declaration
and the recorded compiler evidence. Fix the maintainer-owned interface parser to recognize
indented top-level declarations, or include removed nonprivate declarations in the interface
change check. The worker has not edited or worked around the tools (AGENTS.md §3 and §6).
A fresh dry run on 2026-10-14 reproduced this failure after all nine delivered modules,
all eight baseline-versus-changed counterfactual checks, and every axiom probe passed.
Preflight reported the same eight false interface-change failures; its ninth finding
was the expected absent second reading, which belongs to the next worker. Nothing was pushed. The candidate and all compile/error evidence remain in this
sandbox for delivery after the tool is repaired.


Retry verification (2026-10-14, third worker): re-read the repair review, the held module,
canonical theorem, node and all nine file diffs. The retained canonical theorem and its
proof are unchanged; each of the eight caller diffs changes only the required references.
The current static audit is saved in scratchpad/current-static-audit.json and again shows
that diff_module recognizes the alias in `removed` but returns an empty `interface`.
Ran deliver3.py --no-push to completion. All nine delivered-file compiles, all eight
baseline/changed-dependency necessity checks and all axiom probes passed. Preflight again
failed with eight `unheld adaptation requires the item's own interface change` errors,
plus the expected missing second reading. Full fresh output is preserved in
scratchpad/dry-run-current.log. No Lean changes were needed, no tool was edited or bypassed,
and nothing was pushed. This remains a maintainer-owned tool blocker, not a proof failure.


Fourth-worker verification (2026-10-14): checked the repair review, node, unit route,
all nine Lean diffs and current caller holders (all eight callers remain unclaimed).
The canonical theorem and helper are unchanged; caller edits replace only the nine
required proof references and preserve all signatures, visibility and imports.
The fresh static audit is in scratchpad/fourth-static-audit.json. Ran the required
`deliver3.py G3 Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison --no-push`
to completion: all delivered modules compiled, all eight originals compiled against
the baseline and failed against the changed dependency, and all axiom probes passed.
Preflight still reports eight false interface-change errors, plus the expected absent
second reading. The complete returned tool output is in scratchpad/dry-run-fourth.log.
The fetched checker still skips indented command lines in leanindex.commands, so
removing the indented public alias is recognized by diff_module.removed but omitted
from diff_module.interface. The necessary maintainer repair is in the interface parser
or the forced-adaptation guard, not the Lean proof. No tool was edited or bypassed,
no second reading was fabricated, and nothing was pushed. The candidate is preserved.

Fifth-worker verification (2026-10-14): re-read the stage-3 contract, upstream review,
node and unit record, canonical theorem, change record, prior search results, and
all nine source diffs. Each caller changes only the forced theorem reference;
no signature, visibility, import, canonical proof or DAG route changes. The static
audit in scratchpad/fifth-static-audit.json reproduces the parser inconsistency:
the removed public alias is present in `removed` but `interface` is empty.
Ran the prescribed deliver3.py --no-push to completion again. All nine modules
compiled, all eight original-versus-changed counterfactual checks passed, and all
axiom probes passed. Preflight rejected the same eight adaptations with
`unheld adaptation requires the item's own interface change`, plus the expected
missing second reading. Full returned output: scratchpad/dry-run-fifth.log.
The maintainer-owned parser still ignores the indented top-level alias, so the
candidate cannot pass the required gate without a tool repair. No tool was edited
or bypassed, no second reading was written, and nothing was pushed.

Sixth-worker verification (2026-10-14): independently checked all nine source diffs,
the canonical theorem, upstream review #1424, the DAG node and unit route, and the
previous search evidence. No Lean edits are necessary. The fresh static audit in
`scratchpad/sixth-static-audit.json` confirms the removed public alias is recognized
in `removed` but omitted from `interface`. The required dry run completed all
nine delivered-module compiles, all eight original/baseline and original/changed
counterfactual checks, and the axiom probes. Preflight then rejected the eight
forced adaptations with `unheld adaptation requires the item's own interface change`,
plus the expected missing second reading. Full output is preserved in
`scratchpad/dry-run-sixth.log`. The tool still skips indented top-level declarations
in `leanindex.commands`; its forced-adaptation guard therefore misclassifies this
interface removal. No tool was edited or bypassed, no second reading was fabricated,
and nothing was pushed. The sandbox candidate remains ready for a fresh dry run
after the maintainer repairs that parser or guard.

Seventh-worker verification (2026-10-14): independently checked the held module,
upstream review, canonical theorem, DAG node, unit record and all nine candidate
diffs. All eight callers are unclaimed and retain identical declaration statements,
keywords and visibility; only the nine forced proof references change. The initial
static audit in `scratchpad/seventh-static-audit.json` reproduced the historical
parser defect. During the dry run, the freshly fetched baseline corrected the alias
header to column zero. The final audit in `scratchpad/seventh-final-static-audit.json`
now correctly lists the removed alias in both `removed` and `interface`.

The required `deliver3.py G3 Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison
--no-push` completed all nine module compiles, all eight original/baseline and
original/changed dependency checks, and all axiom probes. It printed
`OK (dry run): commit 570614b5ee compiles and passes the preflight except for the
second reading, which the second reader writes; nothing pushed.` Full output is in
`scratchpad/dry-run-seventh.log`. The previous blocker is resolved by the fetched
baseline; no worker tool edit or workaround was used. No Lean changes were needed,
no second reading was written, and nothing was pushed. The candidate is READY for
the independent second reader.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition

Change only the theorem reference on original line(s) 116 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

Change only the theorem reference on original line(s) 57 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural

Change only the theorem reference on original line(s) 72 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback

Change only the theorem reference on original line(s) 69, 73 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle

Change only the theorem reference on original line(s) 128 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition

Change only the theorem reference on original line(s) 78 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond

Change only the theorem reference on original line(s) 76 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.

### Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise

Change only the theorem reference on original line(s) 215 from `Abelian.Ext.exactFunctorCompositionComparison` to `Abelian.Ext.mapExactFunctor_comp_mk₀_eq`. Removing the alias makes the original reference unavailable; the canonical theorem has the same elaborated type. All signatures, visibility, imports and other proof lines are unchanged. The dry-run counterfactual checks below record the original compiler error against the changed dependency.


Original compiler errors against the changed dependency (lcompile.py):

### Original error: Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition/lean/Sheaf/AlgebraicGeometry/Cohomology/InverseImageCohomologyComposition.lean:116:13: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition/lean/Sheaf/AlgebraicGeometry/Cohomology/InverseImageCohomologyComposition.lean:89:77: error: unsolved goals
```

### Original error: Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial/lean/Sheaf/AlgebraicGeometry/EtaleCohomologyPullbackFunctorial.lean:57:8: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
```

### Original error: Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural/lean/Sheaf/AlgebraicGeometry/EtaleOpenObjectCohomologyNatural.lean:72:8: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural/lean/Sheaf/AlgebraicGeometry/EtaleOpenObjectCohomologyNatural.lean:43:51: error: unsolved goals
```

### Original error: Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback/lean/Sheaf/AlgebraicGeometry/EtaleOpenObjectCohomologyPullback.lean:69:8: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback/lean/Sheaf/AlgebraicGeometry/EtaleOpenObjectCohomologyPullback.lean:42:80: error: unsolved goals
```

### Original error: Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle/lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionCanonicalOpenToOpenCycle.lean:128:13: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle/lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionCanonicalOpenToOpenCycle.lean:75:77: error: unsolved goals
```

### Original error: Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition/lean/Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackComposition.lean:78:13: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition/lean/Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackComposition.lean:71:87: error: unsolved goals
```

### Original error: Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond/lean/Sheaf/AlgebraicGeometry/ScalarExtCupInverseImageSecond.lean:76:14: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
```

### Original error: Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise

```text
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise/lean/Sheaf/AlgebraicGeometry/StructureSheafCohomologyPullbackCompositionPointwise.lean:215:6: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/home/ubuntu/weil-sandbox/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison/scratchpad/Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise/lean/Sheaf/AlgebraicGeometry/StructureSheafCohomologyPullbackCompositionPointwise.lean:83:52: error: unsolved goals
```

## Second reading by G3

Independent second reader, 2026-10-14; did not write the delivered Lean proof.

1. PASS: compared all nine delivered modules against the repository byte for byte.
   The held module changes only by the recorded removal of the deprecated public
   alias `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`. The canonical
   theorem, private helper, signatures and imports are unchanged. Each of the eight
   callers is exactly its original text with the nine forced theorem references
   replaced; no declaration statement, visibility or definition changes. The removal
   is covered by `coord/changes/ext-composition-remove-compatibility-alias.md`.
2. PASS: freshly compiled all nine modules through `lcompile.py --all`, without
   errors or warnings (3.7–35.6 seconds per module). Static inspection found no
   `sorry`, axiom, unsafe, opaque, implemented_by or extern in any delivered module.
   A scratch copy with `#print axioms` for `singleComparison_hom` and
   `mapExactFunctor_comp_mk₀_eq` compiled and printed only `propext`,
   `Classical.choice`, `Quot.sound` for both. There is no new data construction,
   hollow definition or choice from an unproved existence theorem.
3. PASS: no statement is split off, no new declaration or node is introduced, and
   no holes are closed or added. The existing comparison remains valid at degree
   zero (naturality of e), for zero Ext classes, and for the reflexive comparison
   with the composite (the latter is also used by ScalarExtCupInverseImageSecond).
4. PASS: read the canonical proof from its conclusion through shifted naturality
   and the endpoint comparison on single complexes. Both imports are needed:
   Ext.Map supplies the public interface; Shift.ExactFunctor supplies the proof's
   shift-compatible comparison instances and is correctly a plain import. Fresh
   grep, Loogle and LeanFinder searches with naturality/isomorphism/composition
   queries found no shorter result in the pinned Mathlib or upstream sources.
   The online `mapExactFunctor_comp_mk₀_natTransApp` result is absent from the pinned
   source. `## No longer needed` is complete: only the alias is retired; no proof
   dependencies or modules become unused. Read `dag/units/sk-thm-p1.json`; its
   realized route is preserved, and no unit step is bypassed.
5. PASS: read the node
   `lem-weil-pbc-ext-exact-functor-composition-comparison` and its dependency records.
   Its canonical Lean declaration and recorded signature agree with the retained
   theorem. Its proof steps, proof_deps and proof_origin describe the actual
   localization-factorization, single-complex and shifted-naturality argument.
   Removing the redundant alias changes none of these records.

Second reading changed only this report: appended the independent review and fresh
verification evidence. No Lean, node or change-record repair was necessary. This is
an interface-duplication repair with zero net holes closed, not new proof progress.
The required dry run additionally checks every original caller against the baseline
and changed dependency, and probes all declarations of the delivered modules before
accepting the delivery.

Second-reader dry run: `deliver3.py G3 Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison --no-push` printed `OK` at commit `3cea7d561d`. All nine delivered-file compiles, all eight baseline/changed-dependency counterfactual checks, all declaration axiom probes and preflight passed. Review class CODEX correctly reflects the recorded alias removal and eight forced adaptations.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition
Original against changed dependencies failed:
```
/tmp/forced-adaptation-avtjsv69/lean/Sheaf/AlgebraicGeometry/Cohomology/InverseImageCohomologyComposition.lean:116:13: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/tmp/forced-adaptation-avtjsv69/lean/Sheaf/AlgebraicGeometry/Cohomology/InverseImageCohomologyComposition.lean:89:77: error: unsolved goals
X Y Z : Scheme
g : Z ⟶ Y
f : Y ⟶ X
F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat
n : ℕ
x : F.H n
hc :
  (constIso g).inv ≫ (invImage g).map (constIso f).inv =
    (constIso (g ≫ f)).inv ≫
      (invImageComp g f).inv.app
        ((constantSheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
⊢ (Sheaf.H.map ((invImageComp g f).hom.app F) n)
      ((Sheaf.H.mapFunctor (invImage g) (constIso g).symm ((invImage f).obj F) n)
        ((Sheaf.H.mapFunctor (invImage f) (constIso f).symm F n) x)) =
    (Sheaf.H.mapFunctor (invImage (g ≫ f)) (constIso (g ≫ f)).symm F n) x

(with the modules compiled into /tmp/forced-adaptation-avtjsv69/.lbuild) [3.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ens9k33e/lean/Sheaf/AlgebraicGeometry/EtaleCohomologyPullbackFunctorial.lean:57:8: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`

(with the modules compiled into /tmp/forced-adaptation-ens9k33e/.lbuild) [2.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural
Original against changed dependencies failed:
```
ntifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/tmp/forced-adaptation-7t278ihx/lean/Sheaf/AlgebraicGeometry/EtaleOpenObjectCohomologyNatural.lean:43:51: error: unsolved goals
X : Scheme
F : Sheaf X.smallEtaleTopology AddCommGrpCat
q : ℕ
U V : X.Opens
h : V ≤ U
L : Sheaf X.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑U).smallEtaleTopology AddCommGrpCat :=
  Etale.upperStar AddCommGrpCat U.ι
G : Sheaf (↑U).smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑V).smallEtaleTopology AddCommGrpCat :=
  Etale.upperStar AddCommGrpCat (X.homOfLE h)
H : Sheaf X.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑V).smallEtaleTopology AddCommGrpCat :=
  Etale.upperStar AddCommGrpCat V.ι
c : Etale.upperStar AddCommGrpCat V.ι ≅
  Etale.upperStar AddCommGrpCat U.ι ⋙ Etale.upperStar AddCommGrpCat (X.homOfLE h) :=
  Etale.upperStarComp AddCommGrpCat (X.homOfLE h) U.ι V.ι ⋯
a : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk V.ι) ⟶ (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι) :=
  (etaleOpenFreeSheaf X).map (MorphismProperty.Over.homMk (X.homOfLE h) ⋯ trivial)
k : (constantSheaf (↑V).smallEtaleTopology AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) ⟶
  (constantSheaf (↑U).smallEtaleTopology AddCommGrpCat ⋙ Etale.upperStar AddCommGrpCat (X.homOfLE h)).obj
    (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) :=
  (Scheme.upperStarConstantSheafIso AddCommGrpCat (X.homOfLE h)).inv.app (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ))
x : Abelian.Ext ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)) F q
⊢ (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit V ≫ H.map a)).comp (Abelian.Ext.mapExactFunctor H x) ⋯ =
    (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit V ≫ H.map a)).comp
      (((Abelian.Ext.mk₀ (c.hom.app ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)))).comp
            (Abelian.Ext.mapExactFunctor G (Abelian.Ext.mapExactFunctor L x)) ⋯).comp
        (Abelian.Ext.mk₀ (c.inv.app F)) ⋯)
      ⋯

(with the modules compiled into /tmp/forced-adaptation-7t278ihx/.lbuild) [34.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback
Original against changed dependencies failed:
```
 Sheaf Y.smallEtaleTopology AddCommGrpCat := (g)^*[AddCommGrpCat]
R : Sheaf Y.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑(g ⁻¹ᵁ W)).smallEtaleTopology AddCommGrpCat :=
  ((g ⁻¹ᵁ W).ι)^*[AddCommGrpCat]
L : Sheaf X.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑W).smallEtaleTopology AddCommGrpCat := (W.ι)^*[AddCommGrpCat]
T : Sheaf (↑W).smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑(g ⁻¹ᵁ W)).smallEtaleTopology AddCommGrpCat :=
  (g ∣_ W)^*[AddCommGrpCat]
H : Sheaf X.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑(g ⁻¹ᵁ W)).smallEtaleTopology AddCommGrpCat :=
  ((g ⁻¹ᵁ W).ι ≫ g)^*[AddCommGrpCat]
e₁ : ((g ⁻¹ᵁ W).ι ≫ g)^*[AddCommGrpCat] ≅ (W.ι)^*[AddCommGrpCat] ⋙ (g ∣_ W)^*[AddCommGrpCat] :=
  upperStarComp AddCommGrpCat (g ∣_ W) W.ι ((g ⁻¹ᵁ W).ι ≫ g) ⋯
e₂ : ((g ⁻¹ᵁ W).ι ≫ g)^*[AddCommGrpCat] ≅ (g)^*[AddCommGrpCat] ⋙ ((g ⁻¹ᵁ W).ι)^*[AddCommGrpCat] :=
  upperStarComp AddCommGrpCat (g ⁻¹ᵁ W).ι g ((g ⁻¹ᵁ W).ι ≫ g) ⋯
k : (constantSheaf (↑(g ⁻¹ᵁ W)).smallEtaleTopology AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) ⟶
  (constantSheaf (↑W).smallEtaleTopology AddCommGrpCat ⋙ (g ∣_ W)^*[AddCommGrpCat]).obj
    (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) :=
  (Scheme.upperStarConstantSheafIso AddCommGrpCat (g ∣_ W)).inv.app (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ))
⊢ (Abelian.Ext.mk₀ k).comp
      ((Abelian.Ext.mk₀ (T.map (etaleOpenFreeSheafUnit W))).comp
        ((Abelian.Ext.mk₀ (e₁.inv.app ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)))).comp
          ((Abelian.Ext.mk₀ (e₂.hom.app ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)))).comp
            (Abelian.Ext.mapExactFunctor R (Abelian.Ext.mapExactFunctor P x)) ⋯)
          ⋯)
        ⋯)
      ⋯ =
    ((Abelian.Ext.mk₀ k).comp
          ((Abelian.Ext.mk₀ (T.map (etaleOpenFreeSheafUnit W))).comp
            (Abelian.Ext.mapExactFunctor T (Abelian.Ext.mapExactFunctor L x)) ⋯)
          ⋯).comp
      (Abelian.Ext.mk₀ ((e₁.inv ≫ e₂.hom).app G)) ⋯

(with the modules compiled into /tmp/forced-adaptation-1gcga02v/.lbuild) [20.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle
Original against changed dependencies failed:
```
mplex (ComplexShape.up ℕ)).obj I.cocomplex :=
  etaleSectionMap a I.cocomplex
f : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).obj
    (uliftYoneda.{u + 1, u, u + 1}.obj (Scheme.Etale.mk B.ι) ⋙ AddCommGrpCat.free) ⟶
  I.cocomplex.X q :=
  (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk B.ι) (I.cocomplex.X q)).symm
    ((ConcreteCategory.hom (L.iCycles q)) z)
hf : f ≫ I.cocomplex.d q (q + 1) = 0
hfa : ((etaleOpenFreeSheaf X).map a ≫ f) ≫ I.cocomplex.d q (q + 1) = 0
hz :
  (ConcreteCategory.hom (K.iCycles q)) ((ConcreteCategory.hom (HomologicalComplex.cyclesMap φ q)) z) =
    (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk A.ι) (I.cocomplex.X q))
      ((etaleOpenFreeSheaf X).map a ≫ f)
x : Abelian.Ext
  ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat).obj
    (uliftYoneda.{u + 1, u, u + 1}.obj (Scheme.Etale.mk B.ι) ⋙ AddCommGrpCat.free))
  G q :=
  I.extMk f (q + 1) ⋯ hf
FA : Sheaf X.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑A).smallEtaleTopology AddCommGrpCat := (A.ι)^*[AddCommGrpCat]
FB : Sheaf X.smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑B).smallEtaleTopology AddCommGrpCat := (B.ι)^*[AddCommGrpCat]
T : Sheaf (↑B).smallEtaleTopology AddCommGrpCat ⥤ Sheaf (↑A).smallEtaleTopology AddCommGrpCat :=
  (X.homOfLE h)^*[AddCommGrpCat]
e : (A.ι)^*[AddCommGrpCat] ≅ (B.ι)^*[AddCommGrpCat] ⋙ (X.homOfLE h)^*[AddCommGrpCat] :=
  upperStarComp AddCommGrpCat (X.homOfLE h) B.ι A.ι ⋯
⊢ (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit A ≫ FA.map ((etaleOpenFreeSheaf X).map a))).comp
      (Abelian.Ext.mapExactFunctor FA x) ⋯ =
    (Abelian.Ext.mk₀
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat (X.homOfLE h)).inv.app
              (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) ≫
            T.map (etaleOpenFreeSheafUnit B))).comp
      ((Abelian.Ext.mapExactFunctor T (Abelian.Ext.mapExactFunctor FB x)).comp (Abelian.Ext.mk₀ (e.inv.app G)) ⋯) ⋯

(with the modules compiled into /tmp/forced-adaptation-c5ssj6l1/.lbuild) [12.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition
Original against changed dependencies failed:
```
: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`
/tmp/forced-adaptation-alscrsdj/lean/Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackComposition.lean:71:87: error: unsolved goals
k : Type w
inst✝ : Field k
A B C : Scheme
fA : A ⟶ Spec (CommRingCat.of k)
fB : B ⟶ Spec (CommRingCat.of k)
fC : C ⟶ Spec (CommRingCat.of k)
a : A ⟶ B
b : B ⟶ C
ha : a ≫ fB = fA
hb : b ≫ fC = fB
F : C.Modules
n : ℕ
x : ↑(scalarCohomology fC F n)
hc :
  (scalarInverseUnitIso (a ≫ b)).inv ≫
        (scalarInverseImageCompIso k a b).hom.app (MonoidalCategoryStruct.tensorUnit (KSheaf C k)) =
      (scalarInverseUnitIso a).inv ≫ (scalarInverseImage a).map (scalarInverseUnitIso b).inv ∧
    (scalarInverseImageCompIso k a b).hom.app (scalarSheaf fC F) ≫
        (scalarInverseImage a).map (scalarPullbackCoefficient fC fB b hb F) ≫
          scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F) ≫
            scalarHom fA ((scalarPullbackCompIso a b).app F).inv =
      scalarPullbackCoefficient fC fA (a ≫ b) ⋯ F
⊢ (((Abelian.Ext.mk₀ (scalarInverseUnitIso a).inv).comp
              (Abelian.Ext.mapExactFunctor (scalarInverseImage a)
                (((Abelian.Ext.mk₀ (scalarInverseUnitIso b).inv).comp
                      (Abelian.Ext.mapExactFunctor (scalarInverseImage b) ((scalarCohomologyExtEquiv fC F n) x)) ⋯).comp
                  (Abelian.Ext.mk₀ (scalarPullbackCoefficient fC fB b hb F)) ⋯))
              ⋯).comp
          (Abelian.Ext.mk₀ (scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F))) ⋯).comp
      (Abelian.Ext.mk₀ (scalarHom fA ((scalarPullbackCompIso a b).app F).inv)) ⋯ =
    ((Abelian.Ext.mk₀ (scalarInverseUnitIso (a ≫ b)).inv).comp
          (Abelian.Ext.mapExactFunctor (scalarInverseImage (a ≫ b)) ((scalarCohomologyExtEquiv fC F n) x)) ⋯).comp
      (Abelian.Ext.mk₀ (scalarPullbackCoefficient fC fA (a ≫ b) ⋯ F)) ⋯

(with the modules compiled into /tmp/forced-adaptation-alscrsdj/.lbuild) [2.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond
Original against changed dependencies failed:
```
/tmp/forced-adaptation-2p3otws4/lean/Sheaf/AlgebraicGeometry/ScalarExtCupInverseImageSecond.lean:76:14: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`

(with the modules compiled into /tmp/forced-adaptation-2p3otws4/.lbuild) [28.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise
Original against changed dependencies failed:
```
Z JX Limits.isTerminalTop Limits.isTerminalTop
cz : constantSheaf JZ AddCommGrpCat ⊣ (sheafSections JZ AddCommGrpCat).obj (Opposite.op ⊤) :=
  constantSheafAdj JZ AddCommGrpCat Limits.isTerminalTop
cy : constantSheaf JY AddCommGrpCat ⊣ (sheafSections JY AddCommGrpCat).obj (Opposite.op ⊤) :=
  constantSheafAdj JY AddCommGrpCat Limits.isTerminalTop
cx : constantSheaf JX AddCommGrpCat ⊣ (sheafSections JX AddCommGrpCat).obj (Opposite.op ⊤) :=
  constantSheafAdj JX AddCommGrpCat Limits.isTerminalTop
hg : ((cz.comp adjg).homEquiv A ZY) (eg.hom.app A) = cy.unit.app A
hf : ((cy.comp adjf).homEquiv A ZX) (ef.hom.app A) = cx.unit.app A
hfg : ((cz.comp adjfg).homEquiv A ZX) (efg.hom.app A) = cx.unit.app A
hc : efg.hom.app A = α.hom.app ZZ ≫ Lf.map (eg.hom.app A) ≫ ef.hom.app A
hconstant : efg.inv.app A ≫ α.hom.app ZZ = ef.inv.app A ≫ Lf.map (eg.inv.app A)
this✝¹³ : Limits.PreservesFiniteLimits F.op.lan
this✝¹² : Limits.PreservesFiniteLimits G.op.lan
this✝¹¹ : Limits.PreservesFiniteLimits FG.op.lan
this✝¹⁰ : Limits.PreservesFiniteLimits Lf
this✝⁹ : Limits.PreservesFiniteLimits Lg
this✝⁸ : Limits.PreservesFiniteLimits Lfg
this✝⁷ : Limits.PreservesColimits Lf
this✝⁶ : Limits.PreservesColimits Lg
this✝⁵ : Limits.PreservesColimits Lfg
this✝⁴ : Limits.PreservesBinaryBiproducts Lf
this✝³ : Limits.PreservesBinaryBiproducts Lg
this✝² : Limits.PreservesBinaryBiproducts Lfg
this✝¹ : Lf.Additive
this✝ : Lg.Additive
this : Lfg.Additive
⊢ (Abelian.Ext.mk₀ (efg.inv.app A)).comp
      (((Abelian.Ext.mapExactFunctor Lfg x).comp (Abelian.Ext.mk₀ (α.hom.app OZ)) ⋯).comp
        ((Abelian.Ext.mk₀ (Lf.map ag)).comp (Abelian.Ext.mk₀ af) ⋯) ⋯)
      ⋯ =
    (Abelian.Ext.mk₀ (ef.inv.app A)).comp
      ((Abelian.Ext.mk₀ (Lf.map (eg.inv.app A))).comp
        ((Abelian.Ext.mapExactFunctor Lf (Abelian.Ext.mapExactFunctor Lg x)).comp
          ((Abelian.Ext.mk₀ (Lf.map ag)).comp (Abelian.Ext.mk₀ af) ⋯) ⋯)
        ⋯)
      ⋯

(with the modules compiled into /tmp/forced-adaptation-jd5tuqm9/.lbuild) [27.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
