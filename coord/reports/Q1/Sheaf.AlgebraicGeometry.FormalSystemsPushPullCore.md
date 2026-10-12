## What changed

Replaced `AlgebraicGeometry.exists_formalSystemsPushPull_core`'s sole sorry with a
compiling reduction following Stacks Lemma 088B and Remark 0888. Its signature,
universe, hypotheses and conclusion are unchanged.

The core now proves coherence of the proper pushforward from the existing
`Scheme.Modules.isFinitePresentation_higherDirectImage` at degree zero. Two private,
fully proved helpers convert coherence to finite presentation using finite affine
sections and the Noetherian affine criterion, and transport the degree-zero derived
image across `rightDerivedZeroIsoSelf`. The proper-image theorem may still have
transitive sorries; this delivery does not claim to close those.

Added two public theorem modules, each containing exactly one named sorry:
`FormalSystemsPushPullComparison` constructs the quotient comparison κ and formal
map α with their defining equations, assuming the already proved coherence;
`FormalSystemsPushPullAffineAnnihilation` proves annihilation of their affine limit
kernels and cokernels. The first theorem has no exceptional ideal or annihilation
conclusion. The second takes actual maps satisfying the quotient and adjunction
equations; it does not assert existence of the comparison. Neither is a renamed
copy of the original existential theorem. The core combines both with the existing
`coherentFormalModule_annihilated_iff` implication from condition (2) to condition (1).

The maps occur only as existential witnesses in a theorem proof; no definition or
arbitrary data construction chooses witnesses from an unproved existence theorem.
New imports used only by the core's proofs are non-public. Updated the core node's
proof, proof dependencies and proof origin, and supplied nodes for both new modules.
No existing definition or statement was changed; no other holder's module was adapted.
The import visibility change is recorded in `coord/changes/formal-systems-push-pull-core-imports.md`.

Read the source online at Stacks Tags 088B and 0888 because the local literature
checkout is absent on this machine. Library and Mathlib searches found no ready-made
canonical formal push-pull comparison. LeanSearch returned HTTP 500 and is recorded
as unavailable; LeanFinder and grep ran successfully. All three modules compile
through the launcher in import order, with no compiler warnings.

## Proved and sorry left

Closed upper hole: `AlgebraicGeometry.exists_formalSystemsPushPull_core`
(node `lem-weil-pbc-formal-systems-push-pull-core`). No sorry remains in the item's
module. Its coherence clause and the assembly proof are implemented in Lean.

Added holes:

- `AlgebraicGeometry.exists_formalSystemsPushPull_comparison`
  (`lem-weil-pbc-formal-systems-push-pull-comparison`), in
  `Sheaf.AlgebraicGeometry.FormalSystemsPushPullComparison`.
- `AlgebraicGeometry.formalSystemsPushPull_affine_annihilation`
  (`lem-weil-pbc-formal-systems-push-pull-affine-annihilation`), in
  `Sheaf.AlgebraicGeometry.FormalSystemsPushPullAffineAnnihilation`.

This is a decomposition: one upper hole closed, two strictly partial lower holes
added, net minus one hole before any import-closure changes. It is not a complete
sorry-free proof of the mathematical result. Both holes have standalone statements,
source citations, full proofs in words and matching DAG nodes.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its module-base-change construction
  is not used by the implemented core proof.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: already publicly available through
  `CoherentFormalModuleAnnihilated`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`: its direct import is redundant;
  the retained public annihilation module publicly imports it, preserving visibility.

Removed `lem-weil-pbc-formal-systems-push-pull` from the core's proof dependencies.
Its Lean theorem depends on this core and cannot prove it. The parent module is still
needed above this item; this is removal of a circular dependency, not global pruning
of that parent. The abelian and formal-module modules remain transitively needed.
No whole-library module removal is claimed, and none of the parent plan's substantive
formal-functions or completion inputs is discarded: they are recorded in the two
intermediate nodes' proof plans. The unit's realized statements and steps are intact.

## Where the brief, the DAG or earlier work was wrong

Delivery-tool failure after successful final compilation: the requested
`deliver3.py Q1 Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore --no-push`
failed before preflight with:

```text
File "/home/ubuntu/weil-launcher/deliver3.py", line 140, in main
  check_import_sources(clone, sb, mods)
File "/home/ubuntu/weil-launcher/deliver3.py", line 65, in check_import_sources
  from import_cycles import refuse_missing, source_roots
ImportError: cannot import name 'refuse_missing' from 'import_cycles'
  (/home/ubuntu/weil-conjectures-sheaf-Q1/tools/import_cycles.py)
```

The launcher script expects helpers not present in this clone's project tool.
No delivery-tool or repository file was edited, and no check was bypassed.
A subsequent unchanged attempt got past the import-helper error but failed the
source check with:

```text
FAILED: missing import source modules:
  FormalSystemsPushPullAffineAnnihilation: Mathlib.Algebra.Category.ModuleCat.Limits
  FormalSystemsPushPullAffineAnnihilation: Mathlib.AlgebraicGeometry.Morphisms.Proper
  FormalSystemsPushPullComparison: Mathlib.AlgebraicGeometry.Morphisms.Proper
  FormalSystemsPushPullCore: Mathlib.AlgebraicGeometry.Morphisms.Proper
```

Both files exist under the designated read-only Mathlib source root
`/home/ubuntu/weil-src-slopmaster2/.lake/packages/mathlib/Mathlib/`, as verified by
listing their exact paths. `Morphisms.Proper` is also an unchanged original import
of the core. The launcher calls its source validator with roots derived from
`/home/ubuntu/weil-lean`, so its source lookup does not recognize these real installed
imports. Removing valid imports to evade this failure would work around the tool,
which the project contract forbids. No OK result was obtained and nothing was pushed. The compiled sandbox and all
node/report files are ready to rerun after the launcher/project tool mismatch is
repaired by its owner. An earlier transient 60-second compile timeout was resolved
by an unchanged retry: final times were 9.1, 3.1 and 10.5 seconds for the affine
annihilation, comparison and core modules respectively, with no warnings.


The original core node has one proof step citing its parent
`lem-weil-pbc-formal-systems-push-pull`. That parent's existing Lean proof invokes
`exists_formalSystemsPushPull_core`, so the stated plan cannot be imported as a proof.
The new core proof replaces that circular edge with the two genuine parts of the
parent's detailed Stacks argument. The pre-existing shorthand natural-language core
statement and its statement dependency on the parent were left unchanged.

The plan's `lem-pc-flat-base-change-cohom` Lean record currently points to
`Scheme.Modules.finrankH_pullback`, which alone does not supply the natural
comparison of section maps used in Stacks 088B. This delivery makes no application
of that finrank theorem. The affine-annihilation hole includes the needed natural
flat-base-change argument; its future worker must use the actual comparison APIs
(or supply their missing compatibility), rather than treating equality of finranks
as a comparison isomorphism.

`blueprint_refs.py ancestor` returns None for this item because its earlier
`created.item` is a module name, not a node id. The new nodes use the genuine
blueprint ancestor `thm-weil-pbc-finite-etale-lifting` recorded in the parent and
its existing siblings, with the intervening node chain and the specific halves of
Lemma 088B they realize. Blueprint searches for 088B and the comparison words
found no duplicate imported blueprint statement.

Edge cases checked in the new statements: on an empty affine all section modules
vanish and exponent 1 works; K=0 has empty isomorphism locus and annihilation is
automatic with exponent 1; K=O_Y forces f to be an isomorphism and the canonical
comparison is invertible. For J=O_Y all formal systems are zero. For J=0 the equations
reduce to the ordinary adjunction comparison. No nonempty, proper-ideal, separated
base, or completeness hypothesis is added to either theorem.

## Earlier second reading (a previous round; superseded)

Pending the independent Q1 reader. The delivered modules compile in import order;
the reader should check the unchanged core signature, the two strictly partial
intermediate statements, and that the unit route remains represented by the new
comparison and affine-annihilation nodes.

## New nodes

`lem-weil-pbc-formal-systems-push-pull-comparison` records the first half of
Stacks Lemma 088B: construct κ from quotient projections and use formal functions
and the affine equivalence to construct and glue α. Coherence is an input, and
exceptional-ideal annihilation is absent. Its two equations make the maps canonical.
The corresponding module is `Sheaf.AlgebraicGeometry.FormalSystemsPushPullComparison`.

`lem-weil-pbc-formal-systems-push-pull-affine-annihilation` records the second half:
base change to an affine completion, algebraize, identify the comparison with the
adjunction map, and use support to annihilate the affine limit kernel and cokernel.
The hypotheses explicitly specify both maps and both equations. It yields local
exponents only; the existing annihilation equivalence supplies the uniform termwise
exponent in the core. The corresponding module is
`Sheaf.AlgebraicGeometry.FormalSystemsPushPullAffineAnnihilation`.

The import change record is `coord/changes/formal-systems-push-pull-core-imports.md`; there are no forced adaptations.

## Earlier second reading (a previous round; superseded)

1. Compared all delivered modules with the repository snapshot. The comparison and
   affine-annihilation modules are new; the existing core theorem's entire signature
   is byte-identical, including universe, `_hV`, `_β`, and all three existential
   conclusions. No existing definition changes. Restored the original core declaration
   docstring; its implemented proof route remains explained in this report and node.
2. Compiled the three modules in import order through lcompile.py: no errors or
   warnings. Exactly two direct sorries remain, in the two reported public theorems;
   no forbidden declaration form or data definition was added. Scratch copies with
   #print axioms checked both private helpers and all three public declarations.
   coherent_isFinitePresentation uses only propext, Classical.choice, Quot.sound;
   the other declarations additionally use sorryAx, as expected from the named
   open comparison/annihilation and existing proper-image theorems. Scratch copies
   and their compiled artifacts were removed. Witnesses occur in theorem proofs,
   never in definitions choosing arbitrary unproved data.
3. Read Stacks 088B and 0888 online and matched each new statement to the respective
   half of the argument. The comparison assumes coherence but omits K and annihilation;
   affine annihilation assumes actual maps and both defining equations but constructs
   none. These are genuine partial statements, not a renamed existential core.
   Quotient epimorphisms determine κ; formal functions and faithful affine limits
   determine α. For an arbitrary supplied adjunction, compare it to the canonical
   one by the natural automorphism relating two adjunctions on the same functors;
   this transports the γ maps and preserves the isomorphism/support argument.
   Checked J=0, J=O, K=0, K=O, zero modules and empty affines: no case requires an
   added hypothesis. K=0 gives automatic annihilation, K=O gives an isomorphism,
   and J=O forces zero systems. Repeated LeanFinder, Loogle and grep searches with
   different queries (recorded in searches.jsonl); results were AdicCompletion
   lift/eval and evaluation-kernel lemmas, not these sheaf comparison statements.
   Read the upstream proper-image theorem and local coherence/affine criteria;
   no existing theorem closes either new hole in a few minutes.
4. Reviewed the proof from its target downward: coherence is obtained from existing
   degree-zero proper higher-direct-image finiteness, then the two strictly partial
   statements are combined using TFAE (affine condition to termwise condition).
   Every core proof import is used; public imports supply signature notions. The
   removed abelian import remains publicly available through the annihilation module.
   The old proof_deps had just the parent push-pull node; its deletion is fully
   reported and removes the circular proof edge. No global module pruning is claimed.
   Opened dag/units/sk-thm-p1.json: its realized statement and all four step lists
   are unchanged, and the parent formal-functions/completion route is preserved
   in the two new nodes. This remains one upper hole closed and two holes added,
   a decomposition with net minus one before import-closure changes.
5. Checked all node dependency ids exist, proof_deps equals the union of step uses,
   and the new nodes have matching verbatim Lean statements, sources, search records,
   created/blueprint/chapter/unit fields and status split. The core proof and origin
   follow the three implemented steps. Updated its lean.statement to the exact
   multiline signature; no mathematical statement changed. Added the sole direct
   importer FormalSystemsPushPull to the import-change users table; no adaptation
   is needed.

Second reading changes: restored the existing docstring, normalized the core node's
Lean signature to verbatim text, completed the import-change users table, and added
this independent review. No proof body or new theorem signature needed repair.

The first dry run of this reading raced a separate --all compile in the same sandbox
and could not find a freshly rewritten sandbox object. The separate compile passed;
subsequent delivery checks are run sequentially to avoid concurrent artifact writes.

## Second reading by Q1

1. I compared the delivered core module with the repository version. The existing
   theorem signature is unchanged byte for byte; the two comparison and annihilation
   modules are new. No unrelated declarations or definitions were altered.
2. I compiled the three modules individually with `lcompile.py`, in dependency order.
   All compiled without errors or warnings. The only remaining `sorry`s are the two
   named public split-off theorems. No forbidden declaration forms or hollow
   definitions were added; witnesses are introduced only inside theorem proofs.
3. I read both split-off statements and their source/proof plans. Each is a strict
   partial result: comparison constructs the maps under coherence, while affine
   annihilation assumes those maps and proves only local annihilation. Their edge
   cases and hypotheses match the stated Stacks argument, and matching DAG nodes
   exist with verbatim Lean statements and proof dependencies.
4. I checked the proof downward. The core uses the coherence helper, the comparison
   node, affine annihilation, and the existing TFAE bridge. Removed imports and the
   circular parent dependency are recorded above; the unit's realized route remains
   represented by the two new intermediate nodes.
5. I checked node metadata, sources, blueprint ancestry, and the import change record.
   The node proof steps follow the implementation, and no duplicate library theorem
   was found by the recorded searches.

Changes made during this reading: none to Lean proofs or statements; this section
records the independent review and the previously documented import pruning.
