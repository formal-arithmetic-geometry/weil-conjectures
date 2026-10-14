## What changed

Repaired `StandardSingleBaseChangeTopRestrictionAux` after returns X-790d9 and X-84fb1.
The latter repair corrects the DAG proof records, records full old/new signatures
and the unclaimed parent holder, and expands the compatibility construction and
adjoint-transpose calculation without changing its delivered statement. Added the
public noncomputable definition
`standardSingleBaseChange_topRestriction_sourceIso`, using the explicit derived
unit, direct-image composition, and single-complex restriction isomorphisms from
the prior proof. Promoted the unit-invertibility helper to the public theorem
`standardSingleBaseChange_topRestriction_iso_pullback_unit`, with matching nodes.
The existing source-existence theorem now packages the canonical definition.

Changed `standardSingleBaseChange_topRestriction_compatibility` to require
`e = standardSingleBaseChange_topRestriction_sourceIso p M` before producing `t`.
The parent module is included as a forced adaptation: it now lets `e` be the
canonical definition and supplies `rfl`; its theorem signature is unchanged.
Both affected modules compile in the sandbox overlay.

## Proved and sorry left

Closed the existing hole `AlgebraicGeometry.standardSingleBaseChange_topRestriction_source`.
Added no holes: the compatibility hole remains open with its documented corrected
interface, and is not counted as proved. The source comparison theorem and the new
canonical source definition are proved,
as is `standardSingleBaseChange_topRestriction_iso_pullback_unit`.
The repaired canonical compatibility theorem remains a single named `sorry`:
`AlgebraicGeometry.standardSingleBaseChange_topRestriction_compatibility`, node
`lem-pc-standard-single-base-change-top-restriction-compatibility`. Its docstring
contains the complete canonical-unit/naturality proof argument. No hollow
definition and no new anonymous sorry were added.

## No longer needed

No imports were removed. The compatibility node no longer uses its old proof
dependency `lem-pc-standard-single-base-change-top-restriction-source`; it uses
the canonical sourceIso construction instead. The compatibility proof no longer
needs arbitrary source isomorphism data; the old source theorem remains as the existential interface and
is used by its existing callers. No target-reachable module was pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery incorrectly retained a false universal compatibility claim.
The reported dual-number/projective-line example swaps the two source summands and
contradicts the asserted factorization. The repair keeps only the canonical source
comparison used by the parent theorem. The previous `STATEMENT-DISPUTED` marker is
removed because the repaired implication is the intended canonical statement.

## Forced adaptations

`Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction` (`StandardSingleBaseChangeTopRestriction.lean`) originally failed after the
compatibility interface change because its call supplied only `e` and no equality
hypothesis. The exact changed lines replace
`obtain ⟨e⟩ := standardSingleBaseChange_topRestriction_source p M g` and
`standardSingleBaseChange_topRestriction_compatibility p M g e` with
`let e := standardSingleBaseChange_topRestriction_sourceIso p M` and
`standardSingleBaseChange_topRestriction_compatibility p M g e rfl`.
The parent theorem signature and conclusion are unchanged; this is the minimal
forced adaptation and the parent is unclaimed.

## Earlier second reading (a previous round; superseded)

1. **Statements and accidental changes.** I diffed both delivered modules against
the repository versions. Existing declarations retain their signatures except for
the compatibility interface explicitly documented in the change record; the parent
adaptation keeps its public theorem signature unchanged. Verdict: pass.
2. **Proof hygiene.** Both modules compile with `lcompile.py`; the only remaining
`sorry` is the named compatibility theorem, and there are no hollow definitions,
axioms, unsafe declarations, or forbidden implementation directives. Verdict: pass.
3. **Split statements.** I checked the sourceIso definition and pullback-unit
theorem against their node statements and searched the library for duplicates. They
are needed by the canonical construction and are strictly below the repaired
compatibility statement. Verdict: pass.
4. **Route and pruning.** The canonical sourceIso directly composes the existing
derived-unit, image-composition, and single-complex restriction comparisons; the
top-open unit route is preserved. The old source-existence interface remains used
where required, and no unused import or reachable proof dependency was identified.
Verdict: pass.
5. **DAG agreement after X-84fb1.** The pullback-unit node now records the
identity comparison, both composite functors, faithfulness, fullness, and the
fully faithful adjunction unit, citing derived pullback composition and RelativeMVMaps.
The sourceIso node cites that helper, RelativeMVMaps, and SingleComplexOpenRestrictionData.
The source-existence node now records only packaging sourceIso as its witness.
The compatibility node has G1 as its proof origin and repeats the expanded
construction of k, b, d, F, t and the coefficient and transpose equations from
the docstring. Its dependencies include sourceIso, the pinned composition and
adjunction data, the single restriction data, the single-map composition theorem,
the unit-invertibility helper, tensor-pullback composition, and the standard and
derived base-change map definitions. Verdict: pass.
6. **Returned documentation points.** Both change-record fences contain the full
clone/delivered compatibility signatures, including every binder and the full target
isomorphism type, with no proof body or ellipsis. The parent is recorded as
unclaimed in the change record and first forced-adaptation section. The compatibility
statement is unchanged by this repair. The calculation explicitly uses the two
triangle identities and never inverts the comparison for g. Verdict: pass.

This is the repair author's updated second-reading record requested by X-84fb1;
independent reading remains the dispatcher's next step.

## New nodes

`def-pc-standard-single-base-change-top-restriction-source-iso` records the public
canonical source definition. `lem-pc-standard-single-base-change-top-restriction-iso-pullback-unit`
records the public helper required by that definition. The interface change record
is `coord/changes/standardSingleBaseChange_topRestriction_compatibility.md`.

## Forced adaptations

### Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction
Original against changed dependencies failed:
```
/tmp/forced-adaptation-xa3px3ep/lean/Sheaf/AlgebraicGeometry/StandardSingleBaseChangeTopRestriction.lean:72:12: error: Application type mismatch: The argument
  standardSingleBaseChange_topRestriction_compatibility p M g e
has type
  e = standardSingleBaseChange_topRestriction_sourceIso p M →
    ∃ t,
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫ standardSingleBaseChangeMap (⊤.ι ≫ p) (M.restrict ⊤.ι) g ≫ t.hom
but is expected to have type
  ∃ t,
    standardSingleBaseChangeMap p M g =
      (derivedPullback g).map e.hom ≫ standardSingleBaseChangeMap (⊤.ι ≫ p) (M.restrict ⊤.ι) g ≫ t.hom
in the application
  Exists.intro e (standardSingleBaseChange_topRestriction_compatibility p M g e)

(with the modules compiled into /tmp/forced-adaptation-xa3px3ep/.lbuild) [4.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by G1

1. Compared both delivered modules with the read-only repository using `diff -u`.
   The source theorem and parent theorem signatures are byte-for-byte unchanged.
   The sole existing interface change is the canonical-equality hypothesis of
   compatibility, recorded with complete old/new signatures in the change record.
   The parent changes exactly the two forced proof lines. Verdict: pass.
2. Compiled both delivered files in import order with `lcompile.py --all`.
   Inspected every declaration for forbidden directives and hollow definitions;
   the only local sorry is the named compatibility theorem. Checked all four
   auxiliary declarations with `#print axioms` in a scratch copy. The sourceIso
   is an explicit composite, not a witness chosen from source existence.
   The unit helper, sourceIso and source theorem use only propext, Classical.choice
   and Quot.sound; compatibility additionally uses sorryAx. Verdict: pass.
3. Read the remaining compatibility docstring, its coefficient-composition
   equation, mate transposes, and construction of the inverse target comparison.
   These use the same pinned adjunctions as schemeDerivedBaseChangeMap; no
   invertibility of the base-change map or of g's single comparison is assumed.
   Empty schemes and zero modules introduce no exception, since only functorial
   isomorphisms and triangle identities are used. New unit/source helpers are
   proved, strictly below compatibility, and not restatements of it. Fresh
   LeanFinder, Loogle and grep searches found Mathlib's fully-faithful-unit
   instance and composition faithfulness/fullness facts already used here,
   rather than an existing project-level sourceIso or compatibility theorem.
   Verdict: pass; compatibility remains unformalized.
4. Reviewed the top-down route and all three imports. StandardSingleBaseChangeMap
   occurs in the public compatibility signature; RelativeMVMaps occurs in the
   public unit signature and source construction; SingleComplexOpenRestrictionData
   supplies the public sourceIso definition's canonical comparison. Retained these
   imports. The existential source node is no longer a compatibility proof
   dependency and is now explicitly listed above. The unit
   sk-thm-picard-coherence has empty realized lists; none is bypassed or changed.
   Verdict: pass.
5. Read all four delivered nodes against the declarations, comparing the revised
   proof uses with proof_deps. Unit invertibility uses the two inverse pullback
   composites and Mathlib's fully faithful adjunction result; sourceIso composes
   the unit, image composition and exact single restriction; source existence
   packages that definition. Compatibility records its corrected statement and
   explicit remaining natural-language proof, with G1 proof origin and matching
   dependencies. Checked the forced original parent against the changed overlay:
   it fails for the missing equality argument; the delivered parent compiles.
   Verdict: pass.

Second reading changed documentation only: made the closed/added-hole accounting
explicit and listed the removed existential-source proof dependency. The proof
and statement repair already present in the sandbox were retained.

For the new definition, searched STATE's DERIVED PULLBACK and DATA FROM SORRIED
EXISTENCE entries, RelativeMVMaps, SingleComplexOpenRestrictionData, the existing
source theorem and the top-restriction users. This definition names the explicit
canonical composite needed in the equality hypothesis; it introduces neither a
second pullback functor nor arbitrary existence-selected coefficient data.

## Forced adaptations

### Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction
Original against changed dependencies failed:
```
/tmp/forced-adaptation-dr16eoii/lean/Sheaf/AlgebraicGeometry/StandardSingleBaseChangeTopRestriction.lean:72:12: error: Application type mismatch: The argument
  standardSingleBaseChange_topRestriction_compatibility p M g e
has type
  e = standardSingleBaseChange_topRestriction_sourceIso p M →
    ∃ t,
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫ standardSingleBaseChangeMap (⊤.ι ≫ p) (M.restrict ⊤.ι) g ≫ t.hom
but is expected to have type
  ∃ t,
    standardSingleBaseChangeMap p M g =
      (derivedPullback g).map e.hom ≫ standardSingleBaseChangeMap (⊤.ι ≫ p) (M.restrict ⊤.ι) g ≫ t.hom
in the application
  Exists.intro e (standardSingleBaseChange_topRestriction_compatibility p M g e)

(with the modules compiled into /tmp/forced-adaptation-dr16eoii/.lbuild) [3.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
