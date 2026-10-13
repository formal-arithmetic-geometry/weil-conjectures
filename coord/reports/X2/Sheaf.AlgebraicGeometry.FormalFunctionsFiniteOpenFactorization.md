## What changed

Repair H10 (reviewer X-57980, head 57980ffac): added the exact requested
`attribute [local irreducible] Scheme.Modules.moduleCohomologyFMap` immediately
after `namespace AlgebraicGeometry`. This prevents expensive unfolding during
elaboration of this module; it changes no declaration signature or proof route.

Replaced the sorry in `AlgebraicGeometry.formalFunctions_finite_open_factorization`
with a Lean proof of its unchanged signature. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial` and
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting`.
The public import and all existing declaration signatures are unchanged.

The proof derives the equality of inverse-image opens from
`formalFunctionsFiniteι_snd`, restricts the finite coefficient h-map using the
existing cohomology restriction theorem, and takes its cohomology map as the
required additive map. The restriction square proves the first clause. A new
coefficient sheaf-map identity, followed by the existing cohomology composition
lemma and equality transport, proves the second clause. Private helpers prove
transport and composition on cohomology, and transport the restriction theorem
to an equal open. No definition or dependent module is changed.

Updated the item's DAG proof and added one new module/node for the coefficient
identity. The unit `sk-thm-p1` and its realized route are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.formalFunctions_finite_open_factorization`
(node `lem-weil-pbc-formal-functions-finite-open-factorization`). Its proof is
complete from the existing restriction/composition declarations and the new
coefficient identity. No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.formalFunctions_finite_open_unit_pasting`
(node `lem-weil-pbc-formal-functions-finite-open-unit-pasting`, module
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting`). Its proof is
exactly `by sorry`. This is a decomposition: one hole closed, one added, net zero.
It states only the restricted coefficient-map composition identity, with no
cohomology degree, no classes, and no existential additive map. The target's
restriction/existence argument and passage to cohomology are proved here.

The new statement was checked on empty opens, zero modules and n=0: it remains
an equality of the same restriction-unit composites. It does not require V to
contain y, and adds no flatness, properness, coherence or Noetherian assumption.
The intermediate map is obtained existentially inside a proposition proof; no
definition chooses an arbitrary witness from an unproved existence theorem.

## No longer needed

No original import is removed, and no module is globally pruned.
`lem-pc-module-pullback-adjunction` is removed from the upper node’s direct
`proof_deps`: the completed upper proof does not invoke it. It remains a
dependency of `lem-weil-pbc-formal-functions-finite-open-unit-pasting`, so it
is still needed transitively and is not globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned "naturality" step covers a substantial
pushforward coherence calculation. It is now a separate coefficient-level item,
with explicit restriction squares and a componentwise proof in its docstring
and node. The source literature directory named in the original node was not
present on this machine, so the Stacks pages were read directly:
[02OD](https://stacks.math.columbia.edu/tag/02OD),
[01F7](https://stacks.math.columbia.edu/tag/01F7), and
[01FB](https://stacks.math.columbia.edu/tag/01FB).
The new proof in words is explicitly marked as an agent's expansion of the
omitted finite-neighbourhood compatibility, not a verbatim Stacks statement.

Searches: LeanFinder found scheme restriction identities, and Loogle found
`Scheme.Hom.resLE_comp_ι` and `Scheme.Hom.resLE_comp_resLE`; neither states the
coefficient identity. LeanSearch returned Internal Server Error. Source and
DAG/blueprint searches found separate cohomology restriction/composition tools
but no existing statement of the required finite coefficient unit pasting.

## New nodes

`lem-weil-pbc-formal-functions-finite-open-unit-pasting` records exactly the
remaining coefficient identity in the new module
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting`. Its proof in words
transposes the defining finite h-map, rewrites E/D/tau restriction-unit squares,
checks the pushforward coherence on opens, and cancels the comparison isomorphism
and restriction adjunction. The change record is
`coord/changes/x2-finite-open-elaboration-options.md`: the checker flags the
changed elaboration-option commands, although no existing signature or
definition changed. No forced adaptation is included.

Validation: the preserved reduction was rechecked against the declarations,
source pages and unit record. Import-order compilation passed (2.6 seconds for
the helper, 54.0 seconds for the upper theorem). Profiling identified expensive
definitional equality in concrete scheme-map congruence and a final `change`;
these were replaced by open-inclusion cancellation and direct evaluation of
the cohomology equality. No definition or signature was changed. The delivery
dry run printed OK: compilation and preflight passed except for the second
reading, which is reserved for the independent reader. Nothing was pushed.

H10 repair validation: import-order compilation with `lcompile.py --all` passed
with exit code 0 and no diagnostics: 3.0 seconds for the coefficient helper and
30.8 seconds for the upper theorem. Both are below the 60-second per-file limit.
The requested local irreducibility attribute is the only Lean change in this
repair; the independent second reading below is preserved.

The first successful dry-run compilation reached preflight, which requested a
change record for the two transparency-option commands. That record is now
included. The second-reading section is intentionally reserved for the reader.


## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Read both delivered modules and diffed the upper module
   and its node against the repository. The existing theorem signature is byte
   for byte identical, as is its docstring. Its sole public import is unchanged;
   both added imports are proof-only. The two changed elaboration options have
   the supplied change record and do not change any object or imported interface.
   There are no forced adaptations or changed definitions.
2. **Proof and trust: pass, conditional on the recorded hole.** Compiled both
   modules in import order with lcompile.py (2.5 and 48.6 seconds). The upper proof
   has no sorry; the only added sorry is the named coefficient-pasting theorem.
   Scanned both files for forbidden declarations and kernel bypasses: none.
   Scratch copies with #print axioms report only propext, Classical.choice,
   Quot.sound and sorryAx. The upper theorem still depends on the helper’s hole
   and is not an axiom-free completion. No arbitrary data is chosen in a new
   definition: tau is eliminated existentially inside this proposition proof.
3. **Split statement: pass.** Read formalFunctionsFiniteFMap’s adjunction formula,
   FlatBaseChangeOpenChoices.unit_square, the restriction theorem and Mathlib’s
   pushforwardComp/pushforwardCongr section formulas (Modules/Sheaf.lean,
   lines 231–257). The new lemma is the coefficient identity required by hs;
   it has no cohomology degree, no additive-map existence and no global classes,
   and is strictly one part of the upper argument. Its hτ assumption pins tau
   by the restriction adjunction; the E/D unit squares pin their maps similarly.
   Transposing, substituting these three squares, using the global adjunct
   equation, and cancelling the invertible comparisons gives its conclusion.
   The node spells out the coherence calculation on opens and the docstring
   gives the full argument. Checked empty opens, zero coefficients and n=0;
   none requires y in V or any flatness/properness assumption. Read Stacks
   02OD, 01F7 and 01FB directly: the source supplies the factorization and
   functoriality; the node correctly labels this expansion as an agent’s proof.
   Independent Loogle search for pushforwardComp naturality returned no hits;
   LeanFinder search for restriction-adjunction uniqueness returned
   restrictAdjunction and restrictAdjunction_unit_app_app, not this identity.
   rg searches in Sheaf, WeilConjectures and upstream found composition/unit
   tools, but no matching finite restricted coefficient theorem. These tools
   do not close the remaining coherence argument in a few minutes.
4. **Route and pruning: pass after report repair.** hw uses the proved finite
   projection identity; hrs cancels the open inclusion and uses resLE_comp_ι.
   restriction_data transports the existing restriction theorem by equality
   elimination, yielding tau and the first cohomology square. The helper gives
   hs, and cohomology_comp_congr composes and transports the existing cohomology
   maps to give the second clause. Each private helper has a complete proof.
   The original public import is needed by the signature; the two new imports
   supply the proof tools, so none can be removed. Read sk-thm-p1.realized:
   this is below the unit’s recorded steps, which remain intact. The report
   now explicitly lists lem-pc-module-pullback-adjunction as removed from the
   upper node’s direct proof_deps, while still used transitively by the helper.
5. **DAG: pass.** Existing node changes are confined to proof, proof_deps and
   proof_origin. The three upper steps match hw/hrs, restriction_data and
   coefficient-pasting/cohomology composition respectively. Both lean.statement
   fields exactly match their modules. The new node has source, complete proof
   steps, the union of their cited dependencies, agent proof_origin, actual
   search records (including the failed service), split status, creator,
   blueprint provenance, chapter/unit and its own new Lean module. No target
   or unit statement is changed.

Changed only the No longer needed report to name the removed direct dependency,
and added this independent reading. Preserved the Lean proof and helper statement.
One original hole is closed and one strictly smaller hole added: decomposition,
net zero holes closed; no module is globally pruned.

## Second reading by X2

1. **Interfaces: pass.** Independently diffed the delivered upper module and DAG
   node against the read-only repository. Compared the existing public theorem
   signature byte for byte with a script: identical. Its docstring and public
   import are unchanged. Both new imports are proof-only. No existing definition
   is edited. The transparency options have the supplied change record; the local
   irreducibility attribute is exactly the H10 repair requested in the return for
   head 57980ffacf and changes only this module's elaboration.
2. **Proof and trust: pass with the reported hole.** Independently compiled both
   delivered modules in import order: helper 3.2 seconds, upper theorem 34.6
   seconds, exit 0. Fresh scratch copies with `#print axioms` compiled in 2.5 and
   17.2 seconds and reported exactly `propext`, `Classical.choice`, `Quot.sound`,
   `sorryAx` for both public theorems. Scanned the delivered Lean for forbidden
   declarations and kernel bypasses: none. The only delivered sorry is the named
   `formalFunctions_finite_open_unit_pasting`, exactly `by sorry`. No definition
   chooses data. The upper proof eliminates the restriction existence inside a
   proposition proof, retaining its square, rather than defining an arbitrary
   witness.
3. **Split statement: pass.** Read the definition of formalFunctionsFiniteFMap,
   the complete E/D `unit_square` fields, and Mathlib Modules/Sheaf.lean's
   pushforwardComp and pushforwardCongr component formulas (lines 231–257).
   The chosen tensor-pullback adjunction in the finite map is the same chosen
   adjunction used in each unit square. Its homEquiv equation supplies the global
   unit identity in step 1. Transposing the restricted composite under the
   U-restriction adjunction and substituting the E, tau and D squares gives the
   required equality: naturality moves tau across the comparisons, and the two
   comparison paths agree componentwise by presheaf composition and proof
   irrelevance. The node spells out both comparison paths. Empty opens and zero
   coefficients give the unique zero maps; n=0 changes none of these identities.
   No assumption that V contains y, or flatness, properness or coherence, is used.
   Read Stacks [02OD](https://stacks.math.columbia.edu/tag/02OD),
   [01F7](https://stacks.math.columbia.edu/tag/01F7) and
   [01FB](https://stacks.math.columbia.edu/tag/01FB): these motivate factorization
   and h-map functoriality, while the recorded diagram chase is explicitly an
   agent's expansion. Independent Loogle query `"pushforwardComp", "naturality"`
   returned no hits; LeanFinder query about uniqueness of restricted sheaf maps
   returned general sheaf restriction/Hom equivalences, not this coefficient
   identity. Source searches in Sheaf and upstream also found no duplicate.
   Read EtaleTensorUnitRestrictionEquation as a nearby candidate: its theorem
   concerns the structure module's top sections, not these arbitrary module
   h-maps. No few-minute replacement closes the remaining coherence calculation.
   The helper is strictly the coefficient compatibility part, with neither
   cohomology nor an existential additive map; it does not restate the item.
4. **Route and pruning: pass.** Read each private proof. `hw` follows from the
   finite projection identity; `hrs` cancels the open inclusion. `restriction_data`
   transports moduleCohomologyFMap_restriction by equality elimination and supplies
   the additive map and first clause. The new coefficient identity supplies `hs`;
   moduleCohomologyFMap_comp, equality transport and evaluation prove the second
   clause. The public import is needed by the signature, and each added import
   supplies an invoked theorem. The old direct dependency
   `lem-pc-module-pullback-adjunction` is explicitly listed as no longer directly
   used, while still used by the new helper. No modules are globally pruned.
   Read sk-thm-p1.realized: no recorded unit statement or step is bypassed or
   changed by this reduction below the unit level.
5. **DAG: pass.** Existing node edits are confined to proof, proof_deps and
   proof_origin. Its three steps match the open/projection equalities,
   restriction construction, and coefficient/cohomology composition in Lean.
   Script comparisons verified both node lean.statement strings against their
   actual theorem signatures. The new node records its source, complete proof
   steps and their dependency union, agent origin, searches, split status,
   creator, blueprint ancestry, chapter/unit and new module. Its dependency on
   pullback adjunction is justified by transposing the finite map's definition.

Changed only this report by adding the current independent reading and validation.
Preserved the requested H10 repair and the mathematical proof. One original hole
closed, one strictly smaller hole added: decomposition, net zero; no module pruned.
