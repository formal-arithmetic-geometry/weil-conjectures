## What changed

Repaired return X-80797: the corrected quotient claim was already stated by
`HomologicalComplex₂.finiteStripGradedMap_epi`. Its existing module now contains
the complete joint-image and cokernel cancellation proof. Its exact statement
and visibility are unchanged. The proof uses four fully proved private helpers.

`finiteStripGradedMap_factorThru_epi` imports and uses the existing theorem by
one application, retaining the corrected quotient meaning as a compatibility
name. Its category and instance binders are explicit. It contains no duplicate
substantive proof. The old false prequotient claim remains corrected under the
existing change record. The proof dependency is reversed, so the Epi module's
proof-only import of SplitEpi is removed to avoid a cycle. Both node copies
now describe this route.

Change record: coord/changes/finiteStripGradedMap_factorThru_epi.md.

## Proved and sorry left

The original single hole in `HomologicalComplex₂.finiteStripGradedMap_factorThru_epi`
(node `lem-sc-finite-strip-cone-graded-map-split-epi`) is removed by correcting
its false conclusion and reusing the existing quotient theorem. This is a
statement correction, not a proof of the original false assertion.

`HomologicalComplex₂.finiteStripGradedMap_epi` has the complete direct proof.
No holes are added, no statements are split off, and no sorry remains in either
delivered module. All four private helpers are proved.

## No longer needed

Removed the proof-only import
`Sheaf.Algebra.Homology.FiniteStripConeGradedMapSplitEpi` from
`Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi`. The false prequotient
row-to-tail epimorphism is no longer a dependency of the existing quotient
result. Node `lem-sc-finite-strip-cone-graded-map-split-epi` is no longer needed
below `lem-sc-finite-strip-cone-graded-map-epi`; its module is retained only as
a compatibility entry point. No public imports are removed and no new nodes
or modules are added.

## Statement corrected

STATEMENT-DISPUTED (original): a single row does not cover the entire current
filtration tail. For K=0, r=0, A concentrated in degree 1 with nonzero A.X(1),
b=f=0 and p=n=0, the row term is zero while the current tail is A.X(1).
The associated graded quotient is zero, as the corrected theorem requires.

## Where the brief, the DAG or earlier work was wrong

Return X-80797 correctly identified the earlier delivery's duplicate proof.
The repair puts the proof in the already-stated quotient theorem and imports
and applies it from the corrected compatibility name. Explicit category and
instance binders make the alias independent of ambient section variables;
its proof is visibly reuse, not a fresh derivation of the same fact.
The unit's route and every target statement remain unchanged.

## Forced adaptations

`Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi` is unclaimed in the base.
The original caller fails at line 51 against the corrected dependency:

```text
Type mismatch
  finiteStripGradedMap_factorThru_epi K r hsupport A b f F hsteps p n
has type
  Epi (K.finiteStripGradedMap r hsupport A b f F hsteps p n)
but is expected to have type
  Epi ((F.complexStep p n).factorThru (K.finiteStripRowInclusion A b f p n) ...)
```

Necessary edits: remove the proof-only SplitEpi import; insert the four proved
private helpers before the existing declaration; replace the original proof
body (lines 48–66) with the complete joint-image and cokernel proof. Remove the
haveILetI linter override, whose original proof-local letI declarations have
been removed. The existing theorem signature, docstring and visibility stay
identical. The dependency reversal is required to import and reuse the existing
theorem as the return requests. deliver3.py checks that the original fails
against the changed dependency and the adapted module compiles.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations and statements.** Compared both delivered Lean modules with the repository versions. The
   existing `finiteStripGradedMap_epi` signature and visibility are unchanged. The split-epi declaration has the
   documented statement correction from the false prequotient claim to the graded-quotient epimorphism; the change
   record and both DAG node copies record this correction and its forced adaptation.
2. **Proof validity.** Compiled the two modules with `lcompile.py --all`; both compile without errors or warnings.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the delivered
   modules. The compatibility theorem is a direct application of `finiteStripGradedMap_epi`; the latter's complete
   proof is present in the adapted module. Its `sorryAx` dependency is only from still-open imported library
   statements.
3. **New or split statements.** No new split-off theorem was added. The corrected compatibility statement is true
   by direct reuse of the existing quotient theorem and is strictly the intended quotient conclusion. A search of
   the library found no duplicate declaration needed by this delivery.
4. **Pruning and route.** The split module has only the public definition import and one proof-only import of the
   quotient theorem. The quotient module no longer imports the split module, removing the cycle and retaining only
   the imports used by its direct proof. The DAG proof and `proof_deps` follow this reversed route; the unit route is
   retained.
5. **Nodes and records.** The split node's statement change, proof, dependency, origin, and review metadata agree
   with the Lean declaration. The quotient node records the unchanged public statement, its complete proof steps,
   and the adapted proof route. The change record names the forced adaptation and its original compiler failure.

I changed only the delivered module proofs/imports, the forced adapted quotient module and its DAG metadata, and the
change/report records described above; no additional theorem or definition was introduced.

## Forced adaptations

### Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi
Original against changed dependencies failed:
```
/tmp/forced-adaptation-tme600x4/lean/Sheaf/Algebra/Homology/FiniteStripConeGradedMapEpi.lean:51:4: error: Type mismatch
  finiteStripGradedMap_factorThru_epi K r hsupport A b f F hsteps p n
has type
  Epi (K.finiteStripGradedMap r hsupport A b f F hsteps p n)
but is expected to have type
  Epi ((F.complexStep p n).factorThru (K.finiteStripRowInclusion A b f p n) ⋯)

(with the modules compiled into /tmp/forced-adaptation-tme600x4/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.


## Second reading by M1

1. **Visible declarations and statements.** I diffed both delivered modules against the repository. The existing `finiteStripGradedMap_epi` declaration keeps its signature and visibility. The compatibility declaration has the documented correction from the false prequotient epimorphism to epimorphy of the graded quotient map; the change record and DAG node record this statement correction and the forced adaptation.
2. **Proof validity.** Both modules compile with `lcompile.py --all`. An axioms probe for the public declarations and all private helpers reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in delivered Lean files.
3. **New or split statements.** No split-off theorem was added. The corrected compatibility declaration is true by direct application of `finiteStripGradedMap_epi`, and the complete proof of that theorem is in the adapted quotient module. The obstruction scratch proof and mathlib searches support the original statement correction; no duplicate library declaration was introduced.
4. **Pruning and route.** The compatibility module has one public definition import and one proof-only import of the quotient theorem. The quotient module removes the reverse proof import and contains the direct joint-image/cokernel cancellation proof, so the import cycle is gone. The DAG proof and dependencies follow this route; the unit route metadata is unchanged.
5. **Nodes and records.** The two node files, the change record, and the Lean declarations agree on the corrected statement, proof dependency, origin, and forced adaptation. Existing target statements and definitions are unchanged.

I changed the report to include this second-reading record and corrected the change record's `Old` block to reproduce the repository declaration exactly. No Lean proof or interface change was needed during this reading.

## Forced adaptations

### Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi
Original against changed dependencies failed:
```
/tmp/forced-adaptation-e6jux6f_/lean/Sheaf/Algebra/Homology/FiniteStripConeGradedMapEpi.lean:51:4: error: Type mismatch
  finiteStripGradedMap_factorThru_epi K r hsupport A b f F hsteps p n
has type
  Epi (K.finiteStripGradedMap r hsupport A b f F hsteps p n)
but is expected to have type
  Epi ((F.complexStep p n).factorThru (K.finiteStripRowInclusion A b f p n) ⋯)

(with the modules compiled into /tmp/forced-adaptation-e6jux6f_/.lbuild) [2.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
