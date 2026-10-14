## What changed

Proved the unchanged, repaired signature of
`AlgebraicGeometry.standardSingleFlatCounit_localization_homology` in
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology` from two
strictly separate comparison lemmas. The proof constructs exactly the complex
specified in the statement, rather than choosing an unrelated flat complex.
It proves its bound by zero-morphism preservation and its termwise flatness by
`RingedSpace.flat_stalk_of_isFlat`, flatness of bijective ring maps, and
`Module.Flat.trans`. The private, proved helper `flat_restrict_iso` transports
flatness along the inverse open-stalk isomorphism. The existing localization-pair
theorem supplies the universal pair. The final proof maps and composes the actual
presentation isomorphisms and proves the equation by functoriality and associativity.

Added proof-only imports of `FlatSheafStalk`,
`StandardSingleFlatCounitLocalizationPair`, `Mathlib.RingTheory.RingHom.Flat`,
`StandardSingleOpenStalkArrow`, and `OpenFlatComplexStalkCounit`.
The original public import and every existing signature and docstring are preserved.
No definitions, callers, or targets are changed.

Validation: all three delivered modules compile cleanly via `lcompile.py --all`;
the main theorem compiles in approximately 20 seconds, below the 60-second limit.
The first deliver3.py --no-push run printed OK and required only the independent
second reading; nothing was pushed. A final run follows the source-label cleanup.
The larger scoped heartbeat budget concerns elaboration of the fixed transport
expressions, without changing the wall-clock limit. The unused-variable linter is
scoped off for the existing theorem because its unchanged signature contains
unused affineness assumptions and an existential proof binder `hLF`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.standardSingleFlatCounit_localization_homology`
(node `lem-pc-standard-single-flat-counit-localization-homology`).
The private helper `AlgebraicGeometry.flat_restrict_iso` is fully proved.
There are no sorries in the item's module.

Added exactly two holes, each in a separate new module:

- `AlgebraicGeometry.standardSingle_open_stalk_arrow`, node
  `lem-pc-standard-single-open-stalk-arrow`, module
  `Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow`.
- `AlgebraicGeometry.openFlatComplex_stalk_counit`, node
  `lem-pc-open-flat-complex-stalk-counit`, module
  `Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit`.

This is a decomposition: one upper hole closed and two lower holes added, net -1.
The first comparison has no flatness or representative hypothesis; the second
involves only a local flat sheaf complex and has no direct image or coefficient
module. Neither restates the item's proposition. Combining them with the supplied
presentation isomorphisms is real Lean code in the item's module.
The existing imported localization-pair theorem is already proved; no hole is
added there. No arbitrary data is chosen in a definition.

## No longer needed

No imports were removed from the repaired base module: its sole public import is
needed by its statement. No existing planned proof-dependency node was bypassed:
the base node listed no proof dependencies. No unit statement or unit proof step
is pruned, and no whole existing module becomes newly unreachable by this delivery.
In particular this proof never uses `StandardSingleFlatCounitLocalizationData` or
its zero-complex witness; that import had already been removed by the interface
repair. No additional pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The checkout refreshed during initial reading. Its initial version quantified over
arbitrary P and was false for identity maps on Spec(k), M=O and P=0. The newly landed
A3 repair (record `coord/changes/standardSingleFlatCounit_localization_homology.md`)
fixed the signature and caller before this proof was written. This delivery uses
and preserves that repaired version, so it makes no statement correction.

The repaired node's one proof step named no declarations. This delivery makes its
route explicit: actual stalk boundedness/flatness, existing universal pair,
open-arrow transport, local counit comparison, and composition of presentation
isomorphisms. The unit record has no realized statement/steps yet; its route is
preserved, and no route is replaced.

The local checkout omits the obtained Stacks .tex files. Read the official pages
for Tags 0DJ9, 0DJ7, 06YB and 0D5S and obtained perfect.tex and cohomology.tex in the
sandbox scratchpad to verify labels and proof paragraphs. The source for 0DJ9 is
`lemma-single-complex-base-change`; 0D5S is
`lemma-derived-pullback-composition`, not `lemma-derived-base-change`.
The LeanSearch service returned HTTP 500, recorded as unavailable. LeanFinder and
actual grep searches ran; their results are in searches.jsonl. Repository searches
also read the derived open-restriction, module-base-change open-restriction, pinned
open-counit, and derived stalk-extension interfaces. None states either new
comparison with these precise endpoints and original-ring transports.

Edge checks for the new statements: top opens and identity morphisms yield the
usual stalk and counit comparisons; K=0 gives zero on both sides of the local
complex statement; no nonzero-ring hypothesis is needed. Empty V has no witness
a∈V, and all degrees including negative degrees are allowed. Open-arrow transport
is valid without quasi-coherence because exact open restriction preserves the
K-injective direct-image calculation; qcqs is retained from the item. The flat
complex lemma assumes neither flatness of g nor affineness of S or V.

## New nodes

`lem-pc-standard-single-open-stalk-arrow` isolates transport of the canonical
base-change arrow to S,V and back to the original target stalk ring. Its proof in
words names exact direct-image restriction, the ordinary mate restriction square,
pinned counit compatibility, and the linear open-stalk comparison. Its module
is `lean/Sheaf/AlgebraicGeometry/StandardSingleOpenStalkArrow.lean`.

`lem-pc-open-flat-complex-stalk-counit` isolates the scalar-extension counit
comparison for a bounded-above flat complex K on S. Its constructed P agrees
literally with the construction in the item when K=Classical.choose hpres.
The universal derived pair is supplied, so no pair existence or direct image is
hidden here. Its proof in words names the existing K-flat and derived stalk
comparisons and the open transport factors. Its module is
`lean/Sheaf/AlgebraicGeometry/OpenFlatComplexStalkCounit.lean`.

Both new nodes inherit chapter sec-picard-framework and unit sk-thm-picard-coherence,
and identify the same original model proof Step 4 under lem-pc-coherent-hi. Searches
of the full imported blueprint for counit stalk and base change open restriction
found no matching blueprint node. No change record or forced adaptation is needed.

## Second reading by M3

1. Compared every delivered module with the read-only repository. The two comparison
   modules are new. The existing theorem signature and docstring are byte-for-byte
   unchanged; its only edits are proof-only imports, a proved private helper, local
   options, and the proof. No definition, target, or caller changes. Verdict: pass.
2. Compiled all three modules in dependency order with lcompile.py. Scanned every
   delivered source: exactly the two reported named theorem sorries remain, with
   no forbidden declarations or hollow definitions. Explicit #print axioms scratch
   copies check the main theorem, the helper, and both new comparisons; their
   results show only propext, Classical.choice and Quot.sound for flat_restrict_iso,
   and those three plus sorryAx for the main theorem and both open comparisons.
   The delivery tool additionally probes every declaration.
   The result is a conditional reduction, not an axiom-free proof of the item.
   Verdict: pass subject to the two documented open comparisons.
3. Read both new statements, their full proof docstrings and their nodes. Checked
   identity maps, top opens, zero complexes, arbitrary integer degrees, and empty
   opens (the point-membership hypotheses preclude a point in an empty open).
   The open-arrow comparison needs neither flatness nor quasi-coherence, since
   open restriction of K-injectives computes the direct-image comparison. The
   local-flat-complex comparison uses bounded-above flatness and counit-compatible
   uniqueness for any supplied universal derived pair. Neither is a restatement:
   one has no presentation or scalar-extension pair; the other has no direct image
   or coefficient module. Searched again using Loogle stalkPullbackIso, LeanFinder
   natural isomorphism derived pullback stalk tensor product local ring, Mathlib
   mapDerivedCategoryFactors, and repository stalk/counit/open comparisons. Read
   restricted_base_change_compatibility, exists_stalkDerivedExtensionComparisonIso,
   exists_comparisonSourceIso, and the open linear stalk restriction theorem.
   These supply ingredients, but still need the open-ring and homology transports;
   neither hole closes by an immediate application. Verdict: valid decomposition.
4. Read the main proof from its conclusion backward. Its complex is the literal
   transported stalk of Classical.choose hpres, with equality rfl. The bound and
   flatness are proved; the universal pair is obtained from the existing theorem.
   The mapped presentation equation and the two comparison equations compose to
   the required equality. Checked the prior proof_deps (empty), the unit's realized
   record (empty statement and step lists), and the cited Stacks source paragraphs
   in the scratchpad. No prior unit step or dependency was bypassed. Narrowed the
   public imports of the two new modules to declarations used in their statements.
   No whole existing module is claimed pruned. Verdict: pass.
5. Checked all three node files, declaration endpoints, source labels, provenance,
   chapter/unit membership, and that each proof_deps is exactly the union of uses.
   All dependency IDs exist. Corrected the open-arrow plan: derivedPlus is a bounded
   adjunction and is not the appropriate unbounded comparison here. The plan now
   names lem-pc-canonical-module-base-change-open-comparison-compat and explains
   the cancellation identifying its pinned single comparisons with the actual
   picardTermwiseSingleMap. Verdict: pass after correction.

Second reading changed only the new modules' imports, the open-arrow proof docstring
and node plan, and this report. StandardSingleOpenStalkArrow now publicly imports
StandardSingleBaseChangeMap and ModuleStalkFunctor; OpenFlatComplexStalkCounit now
publicly imports SingleComplexBaseChangeStalkCondition and Sheaf.Flat. Both shed the
unneeded StandardSingleFlatCounitPresentation umbrella. Existing signatures and
proofs were preserved. Holes closed: one original theorem; holes added: the two
named comparisons above; net -1, with no extra hole closed during second reading.
