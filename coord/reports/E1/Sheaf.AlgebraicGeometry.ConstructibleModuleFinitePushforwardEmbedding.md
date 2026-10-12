## What changed

Repaired the Noetherian step. The target module now imports
`Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian` and applies
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule`, whose
hypothesis retains `Scheme.IsConstructibleEtaleModuleSheaf`. The target statement and its
remaining descent and base-change steps are unchanged. The existing Noetherian node's Lean
record and proof dependencies now point to this corrected realization.

## Proved and sorry left

`finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf` now has a complete
Lean proof body, conditional on two open statements: the existing imported
`exists_noetherian_descent` (node `lem-weil-pbc-constructible-module-noetherian-descent`)
and the newly stated `exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule`
(existing node `lem-weil-pbc-constructible-module-finite-pushforward-noetherian`).
The latter is the sole `sorry` in this delivery. The embedding is not yet axiom-free:
its axioms are `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The pullback theorem `exists_mono_biproduct_lowerStar_upperStar` uses only the three
allowed axioms.

## No longer needed

None relative to the repository version: every old `proof_deps` entry remains used,
and no existing import is removed. The invalid source-theorem invocation, the bridge
through `Scheme.IsConstructibleSheaf`, and the finite-module-values dependency were
removed from an earlier attempted proof; they are not pruning in this delivery.

## Where the brief, the DAG or earlier work was wrong

The prior delivery applied the source Noetherian theorem for `IsConstructibleSheaf` after
constructing a stratification, but that theorem's predicate does not retain the required
constructible-strata condition and was explicitly rejected as false for this use. The
Noetherian theorem must instead be stated with `Scheme.IsConstructibleEtaleModuleSheaf`.
The repaired node and Lean record now state that theorem and the target node cites it.

## Earlier second reading (a previous round; superseded)

The repaired target compiles together with the corrected Noetherian module. Its theorem
signature is unchanged, and the Noetherian invocation has the exact module-valued
constructibility hypothesis supplied by descent. No target statement or definition was
changed; the only remaining `sorry` is the named Noetherian dependency above.

## Second reading by E1

1. Compared the item module with the repository byte for byte: only two plain proof
   imports and the proof body change. Its existing signature and docstring are identical;
   no definition or target statement changes. The second module is new, and attaches a
   corrected realization to an existing mathematical node, without changing that node's
   mathematical statement. No change record is needed for an existing Lean signature.
2. Both delivered modules compile through `lcompile.py --all`. The sole local `sorry`
   is the named Noetherian theorem reported above; no forbidden declaration or hollow
   definition occurs. A scratch axiom audit confirms only the three allowed axioms and
   `sorryAx` for the item and the two open dependencies; the pullback theorem has no
   `sorryAx`. Thus “proved” here means the item's proof body is filled, not that its
   transitive dependencies are finished.
3. Read the new Noetherian theorem against Stacks 09Z6(3), including the partition
   alternative in its proof: https://stacks.math.columbia.edu/tag/09Z6 . The finite ring
   is Noetherian and finite generation over it gives finite underlying module values.
   The empty scheme and zero sheaf admit the empty sum; the one-point case reduces to
   a finite monodromy representation. The statement is a genuine Noetherian special
   case, omitting the finite-presentation conclusion of the qcqs item, rather than a
   renamed copy of that item. Its source and complete proof outline are in its docstring.
   Fresh leanfinder, loogle and grep searches, plus `rg` over `lean/Sheaf`, found no
   replacement. The source `IsConstructibleSheaf` theorem was considered but is not
   invoked: the delivery retains the corrected module-valued constructibility predicate.
4. Read Stacks 09Z7's proof: https://stacks.math.columbia.edu/tag/09Z7 . Descent supplies
   exactly the Noetherian scheme, constructible descended sheaf, and pullback isomorphism
   needed. Finiteness supplies local finite presentation over that base, and the proved
   pullback lemma preserves the finite module values. Composing with the inverse descent
   isomorphism has the correct direction and remains mono. Both added imports are plain
   imports used by the proof. The public source import supplies the biproduct instance
   needed by the signature. No old dependency is pruned; `sk-thm-p1.realized` and the
   unit route stay unchanged.
5. Compared both delivered JSON files to the repository: the item changes only `proof`,
   `proof_deps`, and `proof_origin`; the Noetherian node changes only its `lean` record.
   The item's dependencies match descent, the corrected Noetherian statement, finite
   presentation, and pullback. The Noetherian node retains its detailed source proof plan
   for the remaining named `sorry`. No new node is introduced or duplicate node created.

Second reading changed the report only: corrected the list of open dependencies and the
meaning of “proved”, distinguished earlier attempted-route removal from actual pruning,
and added this review. No Lean proof or statement repair was necessary.
