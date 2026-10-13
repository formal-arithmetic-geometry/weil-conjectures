## What changed

Corrected the false intermediate `AlgebraicGeometry.chow_algebraization_candidate_support`
to Stacks 088E's actual support argument: a coherent restriction from a proper locally
Noetherian compactification whose support on the adic closed fibre is inside the open
subscheme has proper support. Its proof closes the boundary argument using proper closedness,
maximal ideals and `IsAdicComplete.le_jacobson_bot`; then it lifts the reduced closed support
through the open immersion and applies the pullback-support and closed-subset properness
criteria. Both private helpers are proved. No definitions or target statements changed.

The sole caller, `Sheaf.AlgebraicGeometry.ChowAlgebraizationCore`, retains its exact signature
and visibility. Its candidate import and final proof must change to obtain compactification
data. The new module `ChowAlgebraizationCompactificationData` contains one named intermediate
construction theorem: it returns the chosen restriction algebraization, completion comparison,
and support containment only on the closed fibre. Boundary removal and proper support are
proved in the held item, rather than assumed in this new theorem.

## Proved and sorry left

The corrected `AlgebraicGeometry.chow_algebraization_candidate_support` is proved with no
`sorry`, together with its private support-transfer and boundary helpers. This is a correction
and proof of the true source statement, NOT a proof of the old false arbitrary-candidate
statement. The existing `AlgebraicGeometry.exists_chow_algebraization_core` stays proved with
unchanged signature, reduced to the construction and proved support argument.

Added one hole: `AlgebraicGeometry.exists_chow_algebraization_compactification_data`, node
`new-chow-algebraization-core-support-data`. Its missing argument is strictly the projective
compactification, formal extension, projective existence, and closed-fibre Nakayama comparison;
it assumes neither boundary avoidance nor proper support. No other sorry is left in any
delivered module. Closing one corrected upper hole and adding one lower construction hole
is a decomposition, with net zero holes, not a net proof gain.

## No longer needed

The adapted core no longer imports `Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreCandidate`
or uses node `new-chow-algebraization-core-candidate`. Source search found no other importer
of that module: the old candidate-only abstraction can be pruned from this route. The new
construction retains the compactification information that the old abstraction discarded.

The held item's two original proof dependency nodes, support-pullback-finite-type and
closed-subset-proper-over-base-properties, are used in the proof and retained. The additional
adic-complete-jacobson-radical node supplies boundary avoidance. No unit statement or realized
unit step is bypassed. Original public imports are retained; OpenImmersion is newly public
because the corrected statement uses its predicate. All proof-only imports are nonpublic.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement): Completion detects support only along V(I). The example
A=Q[[t]], I=(t), Z=Y=Spec Q((t)), q=identity, G=0, F=O_Y satisfies every old hypothesis;
its completion vanishes, while Y's image D(t) in Spec A is not closed. Therefore a true
lemma cannot complete the old plan as written. The repair follows the expressly authorized
intermediate-statement correction procedure, and preserves the core existence statement
that targets use. Its construction must choose F with compactification data, rather than
assert the support conclusion for every module sharing its completion.

Edge cases for the new construction and support statement: the zero module has empty
support; empty Y gives an empty candidate; I=0 makes the fibre support condition precisely
full support containment; for I=top completeness forces the zero base ring. The earlier
generic-locus counterexample is excluded by the retained compactification closed-fibre
containment and restriction data, not by excluding any case of the core existence statement.
A proper q and the supplied immersion ensure Y is quasi-compact of finite type over A;
its compactification is the closed scheme-theoretic image in the given projective space.
The new construction theorem is independent of the support theorem, and does not import
or cite the held item. Blueprint searches for algebraization and compactification were read;
no imported blueprint statement duplicates this intermediate construction.

## New nodes

`new-chow-algebraization-core-support-data`, in
`lean/Sheaf/AlgebraicGeometry/ChowAlgebraizationCompactificationData.lean`, states the
compactification algebraization data through the displayed closed-fibre support equation
of Stacks 088E. Its docstring supplies the complete construction and the node cites the
existing formal pullback, constant support, open coherent pushforward and projective
existence lemmas. LeanSearch returned HTTP 500 (recorded unavailable); Loogle and grep
returned no matching compactification-data theorem. All records use searches actually run.

Change record: `coord/changes/chow_algebraization_candidate_support.md`. The support node
has a complete statement_change record and its only DAG citer is
`new-chow-algebraization-core`, whose statement stays true and unchanged.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ChowAlgebraizationCore` is unclaimed in the local claim inventory.
Its original final application fails against the corrected support interface:
`Q` is expected to be a morphism, and `hQ` is expected to be a coherent module. Its original
compiles against the baseline; the changed version compiles against the delivered dependencies.
The forced edits replace the proof-only candidate import with the compactification-data
import and replace the final four proof lines with elimination of the construction data,
application of the proved support theorem, and rewriting of the map equality. Every existing
signature and visibility is identical; there are no added declarations or unrelated edits.


## Second reading by G1

1. Compared every existing delivered module against the repository with diff. The sole
   existing signature change is the explicitly declared and recorded repair of
   `AlgebraicGeometry.chow_algebraization_candidate_support`. The core theorem signature
   and visibility are byte-for-byte unchanged; its import and final proof edits are
   forced by that interface repair. No definition or target statement changes. PASS.
2. Compiled all three delivered modules locally in import order. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound` for the support
   theorem and both private helpers. The construction theorem and core theorem additionally
   use `sorryAx`, exactly from the reported construction hole. Scanned every delivered
   module: one named theorem sorry, no forbidden declarations, no data definitions or
   arbitrary witness definitions. The construction witnesses are eliminated in a proof
   of an existential proposition only. PASS.
3. Read the new construction theorem, its full proof docstring and matching node. Checked
   zero modules, empty Y, I=0, and I=top; none gives a counterexample. Checked Stacks 088E
   directly at https://stacks.math.columbia.edu/tag/088E: its compactification, coherent
   extension, projective existence, and closed-fibre support calculation give exactly the
   retained data. This splits the construction from a genuinely proved boundary-removal
   and support-transfer argument, rather than renaming the whole support assertion.
   Independent LeanFinder search for coherent algebraization on a projective closure
   returned eight unrelated Proj results; Loogle on IsOpenImmersion and CoherentModules
   returned no hits; grep on formal support/compactification/algebraization supplied no
   matching Mathlib result. Also read the current repository candidate proof and
   ChowFormalSystemExtension: the latter permits arbitrary extensions with the right
   restriction and does not supply their boundary support, so it cannot close the new
   hole as stated. The new hole is true and needed, but remains a net-zero decomposition.
   PASS.
4. Read the proof from its conclusion backwards. Closed support, proper closed image,
   maximal ideals and the adic Jacobson bound suffice for boundary avoidance; the support
   lift and finite-type pullback formula give proper support. No shorter existing theorem
   found. Public imports supply signature symbols (including CoherentModules from
   CoherentFormalModule); added proof imports are nonpublic. The new holed construction
   retains its planned proof-dependency imports. No longer needed names the retired
   candidate node and module; both old support proof dependencies remain genuinely used.
   Checked dag/units/sk-thm-p1.json realized: neither changed support/core node realizes a
   unit statement or step, and no realized node is bypassed. PASS.
5. Read all three delivered node files and compared existing nodes with the repository.
   Their proof steps, proof_deps and proof_origin match the written reduction; the new
   node has its source, searches, blueprint origin, creation record, unit/chapter, and
   matching Lean statement. The support statement_change lists the sole citer and the
   change record accounts for the forced caller adaptation. PASS.

Second reading changed the report to record the independent checks and the newer
candidate/extension proof inspected. No Lean proof repair was necessary and no additional
hole was closed or added. Added independent search evidence to the new node's searches.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ChowAlgebraizationCore
Original against changed dependencies failed:
```
/tmp/forced-adaptation-pwsmtljv/lean/Sheaf/AlgebraicGeometry/ChowAlgebraizationCore.lean:63:54: error: Application type mismatch: The argument
  hQ
has type
  Q =
    (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) I)).comap
      f
of sort `Prop` but is expected to have type
  CoherentModules Z
of sort `Type (u + 1)` in the application
  chow_algebraization_candidate_support A I f ?m.149 hQ
/tmp/forced-adaptation-pwsmtljv/lean/Sheaf/AlgebraicGeometry/ChowAlgebraizationCore.lean:63:52: error: Application type mismatch: The argument
  Q
has type
  Z.IdealSheafData
but is expected to have type
  ?m.146 ⟶ Z
in the application
  @chow_algebraization_candidate_support A inst✝⁸ I inst✝⁶ Z ?m.146 inst✝⁵.toIsLocallyNoetherian f ?m.148 Q

(with the modules compiled into /tmp/forced-adaptation-pwsmtljv/.lbuild) [1.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
