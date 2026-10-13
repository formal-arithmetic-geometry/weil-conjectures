## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation`
with a complete reduction to finite cohomology of a single twist over the affine base.
Added proof-only imports for affine localization, clearing denominators, twist sections,
quasi-coherent kernels, coordinate sections, and the new single-twist module.
The second reading removed redundant imports of Charts, TwistSections, and
Mathlib.CategoryTheory.Preadditive.Biproducts; their required declarations are already
available through the retained imports.

The private closed-pushforward proof uses the affine localization criterion, then finite
sections over quotient chart rings and Noetherian finite presentation. The private quotient
construction adapts the source library's clearing-denominators proof directly over T, without
transporting an arbitrary chosen presentation. The private coproduct lemma constructs the
base-linear equivalence between biproduct cohomology and the finite product of cohomology
modules and proves both inverse laws from biproduct identities. All three helpers are proved.
No data is chosen in a definition from an unproved existence theorem.

Both delivered modules compile cleanly through lcompile.py. Read Stacks Tags 01XT and 01Y6
at https://stacks.math.columbia.edu/tag/01XT and https://stacks.math.columbia.edu/tag/01Y6.
The singleton case has rank-one degree-zero cohomology even for negative twists; the empty
coordinate case has zero cohomology. Both are included in the remaining theorem's proof sketch.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.Scheme.Modules.exists_projective_finite_cohomology_presentation`.
No sorry remains in the item module. Added one strictly smaller hole:
`AlgebraicGeometry.ProjectiveSpace.finite_H_twist_affine`, node
`lem-pc-m4-projective-twist-finite-cohomology`. It concerns only one explicit twist and
asserts no presentation, epimorphism, kernel property or general coherent-cohomology
finiteness. This delivery is a decomposition: one upper hole closed and one lower hole added.

## No longer needed

No existing public import was removed. The node's old proof dependencies
`lem-pc-closed-immersion-coherent-cohomology` and
`lem-pc-projective-space-twist-quotient` are replaced by their elementary affine localization
and clearing-denominators proofs, using the explicitly named lower facts in the updated node.
Their recorded modules `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`
and `WeilConjectures.AlgebraicGeometry.Cohomology.Serre` are not imported by this proof.
The third old direct dependency, `lem-pc-projective-space-twist-cohomology`,
is also removed from this node's direct `proof_deps`: it stays needed below the new
ring-valued single-twist item. The second reading additionally removed the proof-only
imports `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections`, and
`Mathlib.CategoryTheory.Preadditive.Biproducts`; these introduce no new DAG pruning
claim for globally unreachable modules.
No claim is made that these source modules are globally unreached: other targets may use them.

## Where the brief, the DAG or earlier work was wrong

The recorded twist-cohomology declarations in Serre require a field, whereas this item
requires an arbitrary Noetherian affine base. The ring-valued single-twist result is missing.
Moreover Serre and Modules.ClosedImmersion already reach this module through downstream
proper/projective cohomology results, so importing them creates a cycle. The cached local
compile accepted such imports, but the dry run correctly rejected the source import cycle.
The final proof imports neither module and reconstructs the needed algebraic arguments using
lower dependencies. The blueprint unit route (projective calculation before descending
induction) is preserved. No existing signature, definition or public import changed.

## New nodes

`lem-pc-m4-projective-twist-finite-cohomology` is the ring-valued affine-base single-twist
finiteness statement, with complete monomial proof in its docstring, Source Stacks Tag 01XT,
label lemma-cohomology-projective-space-over-ring. The existing twist-cohomology blueprint
node was found by blueprint search; its recorded Lean is field-only and cannot supply this
interface. No change record or forced adaptation is needed.

## Second reading by M4

1. Compared the complete delivered item with the repository by diff. The existing
   theorem signature and docstring are byte-for-byte unchanged, as are all existing
   public imports. The additions are private helpers, proof-only imports, a new
   single-twist module, and the replacement proof. No change record or adaptation
   is required. Verdict: pass.
2. Compiled both modules locally in import order through lcompile.py, then compiled
   the item after import pruning. Checked every declaration with explicit #print axioms
   in a scratch copy and the delivery probe. No forbidden declarations or hollow
   definitions occur. The only new sorry is the named single-twist theorem; inherited
   open dependencies may contribute sorryAx. The sections equivalence has explicit
   forward and inverse maps; existential witnesses occur in proposition proofs and
   no definition selects arbitrary data from an unproved existence statement.
   Verdict: pass as a decomposition, not an axiom-free closure.
3. Read the single-twist theorem, its monomial proof docstring, and its new node.
   Checked Stacks Tag 01XT, including the mixed-sign contraction, fixed-degree finite
   exponent sets, one coordinate with negative degree (rank one in degree zero),
   no coordinates (empty scheme), and the zero base ring. The statement is true and
   strictly smaller than the item: it has no coherent quotient, closed pushforward,
   or kernel claim. Repeated LeanFinder, Loogle, and grep searches with different
   wording and searched lean/ for finite cohomology and twist statements. The available
   twist cohomology equivalences are field-specialized; the general coherent-finiteness
   theorem is downstream of this item and would create a cycle. No quick independent
   proof of the remaining ring-valued calculation was found. Verdict: pass.
4. Read the closed-pushforward localization proof, clearing-denominators quotient,
   and finite-biproduct cohomology equivalence from the target downwards. Checked
   the scalar maps use the displayed projective projection and both equivalence
   inverse laws. The source quotient theorem works over a Noetherian ring, but its
   Serre module imports downstream results; the direct adaptation avoids that cycle.
   The finite-biproduct equivalence in Cohomology.Defs is field-specialized, so the
   base-ring version here is necessary. Removed redundant proof-only imports of
   Charts, TwistSections, and Preadditive.Biproducts, and verified compilation.
   Completed No longer needed with all three old direct proof dependencies.
   Inspected sk-thm-picard-coherence's realized record (empty statement and step
   entries): this item changes none of them and retains projective twist calculation
   before descending induction. Verdict: pass after import/report repairs.
5. Compared existing-node changes: only proof, proof_deps, and proof_origin change;
   the replacement steps name the localization criterion, clearing denominators,
   both kernel facts, and the new twist calculation actually used. The new node has
   source, full statement, statement/proof dependencies, proof origin, search records,
   status split, creation record, blueprint provenance, chapter/unit, and a verbatim
   Lean signature with module/file/declaration. Verdict: pass.

Second-reading changes: removed three redundant proof-only imports and completed
pruning documentation. No proof, public signature, definition, or remaining-hole
statement was changed. One original hole closed and one smaller hole added; net zero.
