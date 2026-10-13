## What changed

Closed the body of `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_target`
without changing its signature or visibility. The proof first proves the qcqs flat Ext
cohomology base-change comparison by compact-open induction. It uses the existing separated
and Mayer–Vietoris gluing declarations. The returned duplicate qcqs helper has been replaced by the strictly more general private
`flatCohomologyBaseChange_bijective_of_compact_open`: the ambient scheme need not be compact,
and the conclusion holds over any compact open U and any open immersion with image U,
for all quasi-coherent modules and degrees. The main proof specializes it to U = top and
the identity immersion. Importing the existing private helper in
`FlatBaseChangeResolutionIso` is impossible: that module is downstream, as reconfirmed by
`tools/import_direction.py may`. This takes the return’s generalization option.

The proof then constructs the requested linear equivalence explicitly as
`c.symm.trans (ae.trans (a0.symm.trans (c.trans b0)))`. The normalized source formulas
identify its value on cohomological pullbacks, and the canonical target compatibility
finishes the calculation. Every factor is a B-linear equivalence; in particular the
arbitrary supplied additive eH is never assumed linear.

Added `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons`, carrying the
canonical affine comparisons and their common-section-complex compatibility, steps 1–2
of the original plan. Its statement has no flatness hypotheses and does not assert that
H.baseChange is invertible. The supplied eH and a are absent from this intermediate
statement: it supplies its own compatible canonical coordinates. The flat cohomology
argument and transport to the supplied coordinates are proved in the assigned module.
Updated its DAG proof and proof dependencies to match this decomposition. No interface
was changed and no adaptation of another module was needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_target`
(node `new-flat-base-change-affine-target`), the only original sorry in the assigned module.
The assigned module has no remaining sorry.

Added: `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_canonical_comparisons`
(node `new-flat-base-change-affine-canonical-comparisons`), the only sorry in the new module.
This is a decomposition: one upper hole closed and one independent geometric hole added,
with no claim of a net reduction in holes. The flat cohomology step and change-of-coordinates
step are complete Lean proofs. Existing dependencies retain their own unrelated holes.

## No longer needed

Removed these direct proof imports from the assigned module, moving their geometric role
to the new canonical-comparisons item:

- `Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent`
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `Sheaf.Paper.HigherDirectImagePresheaf`
- `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`

The old proof dependencies no longer used directly by the assigned proof are:
`def-pc-fibre-product`, `def-weil-pbc-flat-base-change-open-choices`,
`def-weil-pbc-module-cohomology-fmap`, `lem-pc-affine-vanishing`,
`lem-pc-leray-degenerate-sections`, `lem-pc-ordinary-higher-image-quasi-coherent`,
`lem-sc-module-abelian-zariski-cohomology`, `lem-sc-module-cohomology-source-comparison`,
`lem-weil-pbc-higher-direct-image-presheaf`, and
`lem-weil-pbc-module-pullback-affine-sections`. They remain dependencies of the new
geometric item (the definitions also remain in the assigned statement/import closure).
None of these modules is claimed globally pruned. The separated and gluing modules remain direct imports
because the proved induction actually uses them. Added the existing Tilde module for its
pullback-preserves-quasi-coherence instance. No module or node is globally no longer needed.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction or statement dispute. The plan's “canonical comparison” steps
contain substantial glue that the available signatures do not directly provide: the
module-derived/Ext comparison, chart comparison, normalized Leray edges, and compatibility
with D.psi must agree on the same section complexes. That work remains explicitly in the
new geometric lemma; neither the dictionary nor the resolution beta is assumed invertible.

The general qcqs flat-cohomology argument already exists as a private helper in the
cyclic downstream module `FlatBaseChangeResolutionIso`, so it cannot be imported here.
The first delivery copied that theorem word for word; the landing checker correctly
refused the duplication. The repair instead proves the compact-open generalization
described above and specializes it in the main proof. This adds no hole and changes no
other module. The Tilde import still supplies pullback quasi-coherence. Both sandbox
modules compile through lcompile.py --all after this repair (10.3 and 25.1 seconds).
The earlier second-reading section below records the previous delivery; the final
second-reading section reviews this repaired delivery independently.

Searches were run with leanfinder, loogle and grep through msearch; LeanSearch returned
Internal Server Error and is recorded as unavailable. Whole-blueprint search for flat base
change found the established base-change theorems, but no separate canonical comparison
without flatness. The automatic ancestor lookup stops at module-valued created.item;
the new node records the existing dictionary's explicit blueprint ancestor and path.

## New nodes

`new-flat-base-change-affine-canonical-comparisons` states the canonical source and target
affine equivalences, with the source unit normalization and target pullback compatibility.
It groups original steps 1–2, without the flat-base-change invertibility of step 3 or the
arbitrary-coordinate transport of step 4. Its docstring contains the full section-complex
argument and citations to Stacks Tags 02KH, 01XJ, 01XK, 01E4 and 03FD. The small cases
checked are empty opens and zero coefficients (all section groups and comparisons are zero),
and degree zero (the normalized edges are augmentation maps). Nonflat base change still
has both affine comparison equivalences: only the map between the two cohomology groups
can fail to be invertible, and that invertibility is deliberately absent from this lemma.
No change records were needed.


## Earlier second reading (a previous round; superseded)

1. **Interface: pass.** Compared the assigned module with the repository using `diff -u`;
   independently compared the complete existing theorem signature as text, byte for byte.
   It is identical, including both flatness instances, the arbitrary additive eH, the
   bijectivity and pure-tensor normalization hypotheses on a, and the target equation.
   Only private proof code, the theorem body and plain proof imports changed. There are
   no changed definitions, target statements, visibility, or change records.

2. **Proof and trust: pass, conditional on the named open comparison.** Compiled both
   modules in import order with lcompile.py (10.1 and 26.3 seconds). Separate scratch-copy
   `#print axioms` probes for both public theorems report exactly propext, Classical.choice,
   Quot.sound and sorryAx. Static inspection finds no forbidden declarations and exactly
   one sorry, in exists_flatBaseChange_affine_canonical_comparisons. The assigned theorem
   has no sorry. The equivalences chosen inside its proof are used to prove a proposition;
   no public definition or arbitrary object is defined from the open existence theorem.
   Checked the induction's empty case, open-chart invariance, compactness of A intersect C,
   and separatedness via its immersion into affine C. Checked each of the five factors
   defining b and each cancellation in the displayed calculation. In particular eH is
   never treated as linear.

3. **Split statement: pass as a decomposition, not a net proof.** Read the new module,
   node and every clause of its docstring against the source pages
   [02KH](https://stacks.math.columbia.edu/tag/02KH),
   [01XJ](https://stacks.math.columbia.edu/tag/01XJ),
   [01XK](https://stacks.math.columbia.edu/tag/01XK),
   [01E4](https://stacks.math.columbia.edu/tag/01E4), and
   [03FD](https://stacks.math.columbia.edu/tag/03FD).
   The qcqs hypotheses give quasi-coherent higher images on both bases; affine vanishing
   makes the edges invertible. These coordinate identifications require no flatness.
   The last equation compares coefficient-unit maps, without claiming their invertibility.
   Read RestrictedResolutionSections.augmentation/components and D.unit_square: they pin
   the choices to the same coefficient map and exclude arbitrary changes of the cocycle
   map. Module inverse image need not be exact here: the exact inverse image used for Ext
   is inverse image of abelian sheaves. Tested identity maps in degree zero (the tensor
   unit formula), empty V or W, zero F, and a nonflat algebra A to A/(t): the coordinate
   equivalences still exist, while baseChange need not be invertible. The new statement
   omits arbitrary eH/a transport and flat invertibility, so is strictly a geometric part
   of the argument. Its complete section-complex proof and sources remain with the hole.
   Independent msearch queries used leanfinder for affine Leray comparison, loogle for
   TensorProduct.congr, and grep for isoRightDerivedObj/moduleCohomologyFMap. They returned
   affine-limit lemmas, tensor congruences and resolution naturality, respectively; none
   supplies the required normalized comparison. Also searched lean/Sheaf and upstream
   DirectImage/Sections and BaseChange: the available section equivalences assume
   separatedness and lack the D-normalization and pullback equation. They do not close
   this hole in a short proof.

4. **Route and pruning: pass after report repair.** Read the separated and gluing theorem
   signatures and the existing private induction in FlatBaseChangeResolutionIso. Reusing
   that induction locally avoids the downstream import cycle. The main proof uses only
   those results and the new geometric comparison. The seven removed proof imports are
   retained in the new module for its stated geometric proof dependencies; public imports
   supply its signature. No declaration of sk-thm-p1.realized is bypassed and that unit's
   route is unchanged. Completed the list above with every removed old proof dependency,
   explicitly distinguishing direct dependency removal from global pruning.

5. **DAG: pass.** Both lean.statement fields equal the corresponding signatures verbatim.
   In each node proof_deps equals the union of the proof steps' uses. The assigned node
   differs from the repository only in proof, proof_deps and proof_origin. Its steps match
   canonical comparison, proved compact-open induction, specialization and linear
   transport. The new node has its source, self-contained statement, search records,
   creation record, blueprint ancestry, chapter/unit, Lean record and complete proof plan.
   The record keeps the geometric comparisons below the unit level.

Second-reading changes: completed the explicit pruned-dependency list and added this
independent review. No Lean or node repair was needed. One original hole is closed and
one geometric hole is added; the net hole reduction is zero and no global module pruning
is claimed.


## Second reading by V2

1. **Unchanged interface: pass.** Read the repository and sandbox modules with `diff -u`.
   Independently extracted and compared the complete existing theorem signature byte for
   byte: identical. Its public imports, visibility, hypotheses (including both flatness
   instances), arbitrary additive eH, normalized linear lift, and conclusion are unchanged.
   There are no definitions added or changed. The existing node changes only proof,
   proof_deps and proof_origin. No change record or forced adaptation is required.

2. **Proof and trust: pass with the reported open comparison.** Compiled both modules in
   import order using lcompile.py --all: 10.1 and 23.7 seconds, no warnings or errors.
   Independently compiled a scratch copy with #print axioms for both public declarations:
   each uses exactly propext, Classical.choice, Quot.sound and sorryAx. Removed the scratch
   copy afterward. Static inspection finds one sorry, solely in the named new comparison
   theorem, and no axiom, unsafe, opaque, implemented_by, extern or hidden data hole.
   The existential comparison is eliminated inside a theorem proof; it defines no public
   data. Read the compact-open induction branch by branch: empty image makes Y empty;
   j identifies the preimage A with the previous compact U; C is affine because it maps
   into the affine chart; quasi-separatedness makes A intersect C compact; its open
   immersion into affine C makes it separated. The induction hypothesis treats all open
   immersion models and every degree, precisely what the gluing theorem needs. The final
   specialization uses top and the identity. Checked all five linear-equivalence factors
   defining b and the cancellations; the supplied eH is never presumed linear.

3. **Split statement: pass as a geometric decomposition.** Read the new theorem and node,
   its entire docstring argument, and Stacks
   [02KH](https://stacks.math.columbia.edu/tag/02KH),
   [01XJ](https://stacks.math.columbia.edu/tag/01XJ),
   [01XK](https://stacks.math.columbia.edu/tag/01XK),
   [01E4](https://stacks.math.columbia.edu/tag/01E4), and
   [03FD](https://stacks.math.columbia.edu/tag/03FD).
   The qcqs hypotheses are exactly those needed for quasi-coherent higher images on
   both affine bases; their affine Leray comparisons do not require flatness. Read
   RestrictedResolutionSections.augmentation/components and D.unit_square: these fix
   the coefficient map and the section coordinates used by sourceClass and targetClass.
   The last clause compares pullback maps without asserting their invertibility; the
   exact inverse image in that comparison is for abelian sheaves, not module pullback.
   Tested empty V/W, zero F, degree zero, identity maps, and the nonflat map A to A/(t):
   affine coordinates still exist, while the map between their cohomologies may fail to
   be invertible. Thus this statement omits the flat invertibility and arbitrary-coordinate
   transport genuinely proved in the assigned module. It is not a renamed target.
   Independent msearch queries: leanfinder for Leray edge/affine higher direct images
   returned Mayer-Vietoris and cohomology-presheaf tools; loogle for
   SheafOfModules.bijective_pushforwardSections returned the ordinary section result;
   grep for resolutionSectionClass/cohomologyIso/sectionsEquiv returned general section
   and cohomology tools. None closes the normalized joint comparison. Also read the
   current AffineCohomologySectionEquiv and the now-proved FlatBaseChangeAffineSource:
   the former is itself open, and neither provides the target chart compatibility.
   The source part is available for later reuse; the complete new hole cannot be closed
   in a few minutes from these declarations.

4. **Route and pruning: pass.** Compared the repaired helper with the private theorem in
   FlatBaseChangeResolutionIso. Its statement now concerns every compact open in a
   possibly noncompact ambient scheme; the assigned proof explicitly specializes it.
   It is no longer the same theorem signature rejected in the return. Importing the
   downstream module would create a cycle. The separated and gluing declarations are
   applied with their actual hypotheses, rather than taking anything from their proofs.
   Read sk-thm-p1.realized: no unit statement or step is bypassed. The seven removed
   direct proof imports and every removed old proof_dep are listed above; those
   geometric dependencies remain in the new module. The new imports are plain proof
   imports. No globally pruned module is claimed.

5. **DAG: pass.** Independently checked both lean.statement strings against the Lean
   signatures and both proof_deps sets against the unions of step uses. The four steps
   of the existing node match the actual comparison, compact-open induction,
   specialization, and transport. The new node includes its source, complete argument,
   self-contained statement, search results (including unavailable LeanSearch), creation
   record, chapter/unit, blueprint ancestry and Lean record. The existing node's
   unchanged fields and the unit's realization are preserved.

Second-reading changes: replaced the stale awaiting-review sentence and appended this
fresh review of the repaired helper. No Lean or DAG change was needed. One original hole
is closed and one strictly geometric hole is added: decomposition, net zero holes; no
module is globally pruned.
