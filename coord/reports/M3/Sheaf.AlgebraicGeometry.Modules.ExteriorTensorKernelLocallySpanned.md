## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span` from a new
stalk kernel statement, with its signature and all original public imports unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan`.
The new module constructs the section relation submodule and its stalk span using actual
`Submodule.span` definitions. No data is chosen from an unproved existence theorem.

The item's three proved private helpers give restriction stability of relation spans,
realization of stalk span elements by local sections, and descent of stalk membership
to a neighborhood contained in the original open.
In particular the finite linear combination and final equality-of-germs parts of the plan
are now complete Lean proofs. Both modules compile locally through `lcompile.py`.
Updated the item's DAG proof to this route and added the matching stalk node.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span`
(node `lem-sc-exterior-tensor-kernel-locally-spanned`). The item's module has no remaining
`sorry`. Its private helpers `local_span_realization`, `locally_mem_of_germ_mem_span`,
and `relationSpan_map` are all proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_stalk_kernel_le_relationSpan`
(node `lem-sc-exterior-tensor-stalk-kernel-span`, module
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan`). Its proof is exactly
`:= by sorry`, with a complete proof in words in its docstring and DAG node.
It states only stalk kernel containment, without a prescribed section or a neighborhood
on which that section is a relation combination. The original proof combines this
containment with fully proved finite-span realization and equality-of-germs descent.
This is a decomposition: one hole closed, one hole added, net zero; not an axiom-free
proof of the full stalk algebra. No other holes were added.

Edge cases: the proved descent works for arbitrary submodules and does not require a
nonzero stalk ring, positive first degree, or a nonempty family of generators. The zero
span case uses its zero member; r=0 uses the empty wedge; s=0 is excluded only by the
existing hypothesis of the stalk algebra statement. On an empty open there is no x∈U.
No finite local freeness or splitting hypothesis was introduced.

## No longer needed

Removed the redundant private helper `exterior_section_map`.
No original imports, nodes or modules were pruned. The exterior sheaf definition,
tensor section API, and short exact sequence API all remain necessary. The new stalk
module uses the proved source `FlatPullbackStalk` API for the canonical stalk module
structure and linear stalk map. The determinant callers and the parent kernel criterion
were not imported, since they depend on this item and would form a cycle.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: removed the duplicate `exterior_section_map`
declaration identified by `import_prune_check.py`. The matching theorem in
`ExteriorTensorLiftHomExt` is private and cannot be reused through a normal import.
`relationSpan_map` now applies the existing public `PresheafOfModules.naturality_apply`
and `exteriorSheafRestriction_existsUnique` results directly to each tensor factor,
combining their equalities with `congrArg₂`. No duplicate theorem is declared, no
private name is accessed, and no existing interface or other module is changed.
The relation-span helper uses a documented local heartbeat limit for elaborating
the two sheafification equalities. Both modules compile, and the exact landing
`import_prune_check.py` command passes against the repaired item.
The earlier second reading predates this repair and was removed for a fresh reading.


The original node's single proof step mentions nontrivial exterior quotient algebra and
stalk comparisons, but lists only the exterior sheaf definition as its proof dependency;
that definition supplies none of these kernel assertions. The remaining stalk calculation
is now named explicitly, while the local finite-span and shrinking argument is proved.

LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and source searches
were used. `blueprint_refs.py ancestor` returns None for this module-created item, so the
new node retains the blueprint ancestor already recorded by the item's node, adding the
item to its `via` lineage. No unit step or statement was bypassed. The source blueprint's
original determinant paragraph was read from `blueprint_proof_text` in
`dag/nodes/sec-picard-framework/lem-sc-riemann-roch.json`; the expanded stalk argument
is explicitly marked as written by an agent.

## New nodes

`lem-sc-exterior-tensor-stalk-kernel-span`: the stalk algebra and representation of its
pure relation generators, in the new module `ExteriorTensorStalkKernelSpan`. It retains
the existing Riemann-Roch determinant source and unit, records all search kinds, and
has one public theorem left to prove. There are no interface change records or forced
adaptations of other modules.

## Second reading by M3

1. Interface: read the repository and sandbox modules in full and compared them with
   `diff -u`. The sole existing theorem's signature is byte-for-byte identical, including
   short exactness, arbitrary A, degrees, the formula for q, and the prescribed U,t,x.
   Its docstring and all public imports are unchanged. No existing definition changed;
   no other existing module is adapted. Verdict: pass.

2. Proof and axioms: compiled both delivered modules in import order with `lcompile.py`;
   both compile without errors or warnings (2.7 s and 21.3 s). Scratch copies with
   `#print axioms` confirm that all three private helpers and both new span definitions
   use only propext, Classical.choice and Quot.sound. The original theorem and the new
   stalk theorem additionally use sorryAx, as explicitly reported above. The sole
   delivered sorry is the named stalk theorem. Neither span definition chooses data
   from an existence theorem: both are actual Submodule.span constructions. The
   restriction proof uses the already proved unique exterior restriction property;
   its chosen map is determined on spanning wedges. No forbidden declaration or
   hidden hole is present. Verdict: pass as a decomposition, not a closed proof.

3. Split statement: read ExteriorTensorStalkKernelSpan and its node hypothesis by
   hypothesis. The new theorem leaves only kernel containment on one stalk. The
   substantial extra task of combining representatives, restricting relation spans,
   and shrinking equality of germs to a prescribed section is completely proved in
   the original module. It is a genuine reduction, not application of a renamed local
   conclusion. Checked the arbitrary-ring argument: the quotient exterior module is
   presented by wedges modulo entries in im(f); changing each lift separately expands
   into such relations. Right exactness of tensor, rather than flatness, suffices to
   obtain the tensor kernel as an image. Pure wedges span the first factor. Finite
   representatives and the germ equality criterion turn each stalk relation into a
   section relation. No local splitting or local freeness is assumed. For r=0 the
   empty wedge generates; for s=1 these are ordinary tensor quotient relations; for
   zero modules or a zero stalk ring the kernel containment is trivial. Empty opens
   have no point to check; s=0 remains excluded by the unchanged hypothesis.
   Independently searched LeanFinder for "alternating power surjection relations span
   kernel tensor product", Loogle for `exteriorPower.map, Function.Surjective`, and
   Mathlib and both library roots for alternating/exterior quotient, exactness and
   kernel statements and for germ span descent. The results are the presentation API,
   map_surjective, and unrelated stalk spanning criteria, not a replacement theorem.
   The parent kernel criterion and determinant callers import this item and cannot
   supply an independent proof. Closing the remaining stalk calculation requires
   exterior/stalk comparison and quotient algebra, beyond a few-minute repair.
   Verdict: true, needed and strictly a part of the original argument.

4. Route and pruning: read the determinant paragraph of blueprint_proof_text in
   lem-sc-riemann-roch, and dag/units/sk-thm-picard-rr.json. The source uses determinant
   lift independence; the detailed arbitrary-module stalk argument is an agent
   expansion, explicitly labelled as such. This reduction retains that argument and
   changes no unit or chapter route. The unit's realized arrays were already empty;
   this item is not its key node and no realization is removed. All original
   proof_deps remain used, so the No longer needed list is complete. Public imports
   provide exteriorSheaf, tmulSection, ShortExact, and (in the new module) the stalk
   module structure and stalkLinearMap appearing in signatures. The only added import
   of the original module is proof-only. Verdict: pass; no module pruned.

5. DAG: compared the original node JSON with its repository version; only proof,
   proof_deps and proof_origin differ. Its four steps match respectively the germ
   kernel calculation, relationSpan_map, local_span_realization and germ-equality
   descent. Their dependency union is exactly proof_deps. Read the new node's complete
   statement, source, three proof steps, searches, created, blueprint lineage, unit,
   chapter and verbatim Lean statement. These match the new module and its single
   open theorem. Verdict: pass.

Changes in this second reading: added this independent review and independent search
records for the new node. No mathematical or Lean repair was necessary after the
reported removal of the duplicate exterior_section_map helper. One original hole
closed, one strictly smaller hole added, net zero.
