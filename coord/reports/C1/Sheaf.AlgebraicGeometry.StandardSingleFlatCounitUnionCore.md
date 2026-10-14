## What changed

Added two proof-only intermediate modules and imported them into
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionCore`. The target theorem now
combines the bounded-above union model with the generic flat replacement theorem.
The two intermediate theorem proofs remain named `sorry`s with their own DAG nodes.

Repair of return X-7ffa6: added the proof-only import
`Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation` to
`UnionBoundedAboveModel.lean`, as requested. This supplies the declaration of its
recorded dependency `lem-pc-kinjective-mayer-vietoris-presentation` without changing
any statement or public import.

## Proved and sorry left

The target declaration `AlgebraicGeometry.standardSingleFlatCounitUnionCore` is proved
by applying the two intermediate declarations and returning their data. Sorries remain
in `AlgebraicGeometry.exists_boundedAbove_union_model` (node
`new-pc-standard-single-flat-counit-union-bounded-model`) and
`AlgebraicGeometry.exists_flat_model_of_boundedAbove_model` (node
`new-pc-bounded-above-model-flat-replacement`). Holes closed: 1; holes added: 2.

## No longer needed

The direct K-injective Mayer--Vietoris and bounded-flat-replacement imports were removed from the target module because its proof now uses the two intermediate declarations; their supporting imports remain in the corresponding intermediate modules.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted named statements for the truncation/representative glue and
for converting a bounded-above representative to a flat one. Those two strictly
smaller intermediate statements were added so the final proof is a genuine composition.

The returned delivery omitted the Mayer--Vietoris presentation import from the
bounded union model despite listing its node as a proof dependency. The repair
restores that import; the existing node record already lists the correct dependency.

## New nodes

`new-pc-standard-single-flat-counit-union-bounded-model` and
`new-pc-bounded-above-model-flat-replacement` are the two intermediate theorem nodes.
Change records: `coord/changes/new-pc-standard-single-flat-counit-union-bounded-model.md` and
`coord/changes/new-pc-bounded-above-model-flat-replacement.md`.

## Earlier second reading (a previous round; superseded)
A second C1 worker should check the unchanged target signature, the two strictly smaller
intermediate statements, and that the Mayer--Vietoris unit route remains represented.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interfaces.** Compared each delivered module with the repository version. The
signature of `AlgebraicGeometry.standardSingleFlatCounitUnionCore` is byte-for-byte unchanged;
the only change is its proof and proof-only imports/options. The two added modules contain new
intermediate declarations recorded by their nodes.

2. **Compilation and proof status.** Compiled all three sandbox modules with `lcompile.py --all`.
They compile without errors. The target has no `sorry`; the two intermediate declarations retain
exactly the named `sorry`s listed above, with no `sorry` in definitions and no forbidden axioms or
unsafe declarations introduced. The intermediate declarations are strictly weaker than the target:
one supplies only a bounded representative and the other adds termwise flatness.

3. **Statement review.** Checked both split-off statements against their hypotheses and conclusions.
`exists_boundedAbove_union_model` asserts only boundedness and the derived-category isomorphism;
`exists_flat_model_of_boundedAbove_model` takes such a witness and adds termwise flatness while
preserving the same object and bound. Neither restates the target, and both are true consequences
of the cited Mayer--Vietoris/truncation and bounded-flat-replacement arguments.

4. **Route and pruning.** The target proof follows the unit route: first the union bounded model,
then bounded-above flat replacement. The Mayer--Vietoris presentation and bounded-flat-replacement
imports remain in the route; no prior proof dependency was removed because both are used by the
intermediate construction modules.

5. **DAG agreement.** Verified that the three node records match the declarations, including
`proof`, `proof_deps`, `proof_origin`, source references, and the unit `sk-thm-picard-coherence`.
The two new node records and their change records are included in this delivery.

**Changes made during second reading:** added this review section only; no Lean statements or
proofs required repair.

## Earlier second reading (a previous round; superseded)

1. **Interfaces.** I compared the delivered target module with the repository version. The
`standardSingleFlatCounitUnionCore` signature is unchanged byte for byte; its proof-only imports
and proof body are the only existing-module changes. The two additional modules and declarations
are recorded by the two new split nodes.

2. **Compilation and axioms.** I compiled all three sandbox modules with `lcompile.py --all`.
They compile without errors. The target theorem has no `sorry`; the only remaining `sorry`s are
the two named intermediate theorems, and no definition contains a `sorry` or forbidden command.

3. **Statements.** The bounded-model theorem supplies only a bounded-above representative and
the required derived isomorphism. The flat-replacement theorem takes precisely that witness and
adds termwise flatness while preserving the bound and isomorphism. These are strictly smaller
than the target and are true consequences of the cited Mayer--Vietoris/truncation and flat
replacement constructions.

4. **Route and pruning.** The target applies the bounded union model and then flat replacement,
so the unit route through Mayer--Vietoris and bounded flat replacement remains represented. The
removed direct imports are retained by the intermediate modules that use them.

5. **DAG agreement.** I checked that each node's Lean declaration, statement, proof dependencies,
proof origin, unit, and source agree with the delivered modules. The two new declarations have
matching nodes and change records; no existing target statement was changed.

**Changes made during this second reading:** added this independent review section only; no Lean
statements or proofs required repair.

## Earlier second reading (a previous round; superseded)

1. **Interfaces.** Compared the delivered target module against the repository version. The
   `standardSingleFlatCounitUnionCore` declaration has the identical signature; only its proof,
   proof-only imports, and a linter option changed. The two intermediate declarations are new
   and their node records match their Lean signatures.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`. The target
   has no `sorry`; the only remaining holes are the two named split-off theorems. An axiom probe
   reports only the permitted foundations together with `sorryAx` inherited by those holes.
   No forbidden commands or `sorry` in definitions occur.

3. **Statements.** The bounded-union theorem supplies exactly a bounded-above representative
   and its derived-category isomorphism. The flat-replacement theorem takes that witness and
   adds termwise flatness while preserving the bound and isomorphism. Both are strict parts of
   the target argument and retain the target's hypotheses and conclusion unchanged.

4. **Route and pruning.** The target applies the bounded-union construction and then the
   bounded-above flat replacement, preserving the unit route through Mayer--Vietoris and flat
   replacement. The removed direct imports are still used by the corresponding intermediate
   modules, so no required dependency was pruned.

5. **DAG agreement.** Checked the three node records' declarations, statements, proof steps,
   proof dependencies, origins, chapter, and unit against the Lean files. The two new nodes and
   both change records are included, and no target statement changed.

**Changes made during this second reading:** added this independent review section; no Lean
statements or proofs required repair.

## Second reading by C1

1. **Interfaces.** Compared the delivered target module with the repository version. The
   signature of `AlgebraicGeometry.standardSingleFlatCounitUnionCore` is byte-for-byte
   unchanged. The two additional modules contain only the new intermediate declarations
   recorded by their node files.

2. **Compilation and proof status.** Compiled all three sandbox modules with
   `lcompile.py --all`; compilation succeeds. The target theorem has no `sorry`. The only
   remaining holes are the two named intermediate theorems listed above; no definition has
   a `sorry`, and no forbidden command or axiom was introduced.

3. **Statements.** Checked the two split-off statements against their hypotheses and
   conclusions. The first gives only a bounded-above representative and derived-category
   isomorphism. The second takes that witness and adds termwise flatness while preserving
   the bound and isomorphism. Both are strictly smaller than the target and are the exact
   inputs used by its proof.

4. **Route and pruning.** The target applies the bounded union model and then bounded-above
   flat replacement. The Mayer--Vietoris presentation and flat replacement imports remain
   in those intermediate modules, so the unit route is represented. The target's direct
   proof-only imports were pruned because the intermediate modules now use them.

5. **DAG agreement.** Verified that the three node records agree with the Lean declarations,
   including proof steps, proof dependencies, source, chapter, and unit. The two new nodes
   and their change records are included; no existing target statement was changed.

**Changes made during this second reading:** added this review section only; no Lean
statements or proofs required repair.
