## What changed

Proved `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` in
`Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling`, leaving its existing signature,
visibility and docstring unchanged. Its final wrapper remains unchanged.

Added the proof-only import `Sheaf.CategoryTheory.Abelian.ExtEpiEffacement` and proved
`CategoryTheory.Abelian.Ext.exists_epi_comp_eq_zero` there directly from Mathlib's derived
fractions and degree-zero cycles. Two proved private helpers in the item establish local
surjectivity of an abelian-sheaf epimorphism via its locally generated image, and construct
the Type v-valued presheaf of pairs lifting free generators. The latter extends the second
projection through the free abelian and sheafification universal properties and proves the
factorization equation. Ext associativity then proves the requested vanishing.

Updated both existing DAG proof routes and added the node of the proved general Ext lemma.
No existing public signatures, definitions, or public imports changed. The unchanged witness
signature binds an unused proof name in `Exists`; a declaration-scoped unused-variable linter
option suppresses that warning without changing any binder.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness`
(node `lem-sc-presheaf-free-ext-local-killing-witness`).

The already-proved `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing` now also has no
reachable sorry. Added and fully proved `CategoryTheory.Abelian.Ext.exists_epi_comp_eq_zero`
(node `lem-sc-ext-epi-effacement`). Both private helpers are fully proved.
No sorry remains in either delivered module; no holes were added or split off.

Both modules compile together with lcompile.py without warnings. The delivery dry run checks
the axioms of all their declarations, including private helpers.

## No longer needed

No original imports were removed and no original dependency modules were pruned. Both original
public Mathlib imports provide the statement vocabulary. The proof uses no Yoneda-extension
representation API, split-extension API or enough-projectives/injectives theory; the fraction
argument proves the final-epimorphism step directly. The general sites/cohomology definition
node remains a statement dependency, but is replaced in the proof dependency lists by the
actual proved Ext lemma and witness lemma respectively.

## Where the brief, the DAG or earlier work was wrong

The witness/True wrapper introduced earlier merely relocated the original hole; this delivery
proves its mathematical content. No statement correction was required.

Mathlib's `Sheaf.isLocallySurjective_iff_epi'` requires
`J.WEqualsLocallyBijective AddCommGrpCat.{v}`, which is not supplied by the item's hypotheses
in the arbitrary object universe u. Adding a hypothesis would change the statement. Instead,
the proved private locally-generated-image argument handles the stated universes unchanged.
The subgroup is constructed explicitly; addition uses intersection of covering image sieves,
and its sheaf property follows from Subfunctor.sheafify_isSheaf on underlying sets.

The local Stacks files are not installed in this clone. Read Tags 06XU and 03F9 directly on
the official Stacks website. LeanSearch returned Internal Server Error; LeanFinder, Loogle,
local Mathlib/source searches and blueprint searches were also attempted.

## New nodes

`lem-sc-ext-epi-effacement` in `dag/nodes/sec-curve-estimates/` records the proved general
positive Ext effacement theorem. It is strictly the categorical step of the local-killing
argument: it has no presheaves, topology, free generators, or local-surjectivity conclusion.
Its proof follows the fraction construction of Tag 06XU and includes the cycle epimorphism,
chain factorization and positive-degree vanishing checks. The q=0 case is deliberately
excluded (nonzero Hom classes cannot be killed by epimorphisms); q=1 and arbitrary positive
degrees are handled uniformly. The lemma is fully proved, so it creates no new worker item.
No change record is needed: all existing signatures and visibility are preserved.

## Second reading by B2

1. **Signatures and visibility.** Compared the delivered item module with the repository
version byte for byte at every existing declaration. The target and witness signatures,
visibility, and public imports are unchanged; the added Ext module is a new proof dependency.
Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules together with `lcompile.py`.
The proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
The new Ext theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Verdict: pass.

3. **Statements and split-off node.** Checked the new Ext theorem against the fraction
construction in Tag 06XU: it is the strictly smaller positive-degree epimorphism
effacement step, with no presheaf or site hypotheses. Its statement is true and exactly
what the item proof needs; no hollow definition or duplicate library theorem was added.
Verdict: pass.

4. **Pruning and route.** The item uses the new Ext node and its local generator-lifting
helpers; no existing import became unnecessary, and the DAG proof dependencies match the
Lean proof. The unit route remains represented by the existing item and witness nodes.
Verdict: pass.

5. **Delivery metadata.** Checked the new node's Lean record, proof steps, source, and
proof dependencies against the declarations and the report. The dry-run preflight found
no issue after this section was added.
Verdict: pass.

The second reading changed only this report by recording the checks above; no Lean proof,
statement, definition, or DAG statement was changed during review.
