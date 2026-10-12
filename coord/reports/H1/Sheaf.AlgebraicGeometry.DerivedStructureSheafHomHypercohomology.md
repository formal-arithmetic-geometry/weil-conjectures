## What changed

Replaced `AlgebraicGeometry.derivedStructureSheaf_hom_hypercohomology`'s hole with a complete
Lean reduction. The proof composes a structure-sheaf/global-sections additive equivalence
with a free-module/homology additive equivalence and explicitly combines their naturality.
All existing signatures and public imports are unchanged. Added two statement modules.

The free-module theorem is fully proved: maps from a projective degree-zero source into
negative objects vanish; the truncation triangle then reduces arbitrary targets to the
nonnegative case, where zeroth homology is bijective on maps. Evaluation at 1 completes
the additive equivalence. The proof works for arbitrary rings, including the zero ring,
and unbounded complexes. The sheaf comparison was checked for the empty scheme and
arbitrary unbounded complexes: no quasi-coherence or compactness is required, and the
free module on the module side remains K-projective.

Validation: all three modules compiled using `lcompile.py --all`. Sources were read at
https://stacks.math.columbia.edu/tag/09M1 and https://stacks.math.columbia.edu/tag/0B6A;
the local copy of `literature/stacks-project/perfect.tex` is absent on this machine.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.derivedStructureSheaf_hom_hypercohomology`
(node `lem-pc-derived-structure-sheaf-hom-hypercohomology`).

Fully proved the new `AlgebraicGeometry.derivedFreeModule_hom_homology`
(node `lem-pc-derived-free-module-hom-homology`) and its two private helpers.

Added one hole:
`AlgebraicGeometry.derivedStructureSheaf_globalSections_hom`
(node `lem-pc-derived-structure-sheaf-global-sections-hom`). This is only the passage
from sheaf-derived Hom to module-derived Hom; its conclusion does not mention zeroth
homology. The independent free-module calculation and their composition are proved.
Thus this is a decomposition with one original hole closed and one new hole added,
not a claim that the target's entire axiom closure is sorry-free.

## No longer needed

Removed direct proof-only imports:
- `Sheaf.AlgebraicGeometry.GlobalDerivedHom` (`def-pc-global-derived-rhom`): the
  point-space equivalence and general derived internal Hom are unnecessary.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
  (`prop-pur-kinjective-resolutions-exist`): still transitively imported and needed
  for the remaining comparison; no claim that this module can be globally pruned.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`
  (`lem-pc-scheme-modules-grothendieck-abelian`): the ringed-space Grothendieck instance
  already supplies the module-sheaf category used here.

The original direct dependency `lem-weil-pbc-kinjective-hom-derived` remains needed by
the new comparison node. The module-cohomology definitions remain public imports.
None of the unit's realized nodes or steps were bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan was mathematically sound but
omitted the explicit intermediate module-derived Hom comparison. The new nodes expose
that calculation. The generic free-module part admits a direct projectivity/truncation
proof; its former K-projective cycle-quotient plan need not be formalized separately.

## New nodes

`lem-pc-derived-structure-sheaf-global-sections-hom`, in
`Sheaf.AlgebraicGeometry.DerivedStructureSheafGlobalSectionsHom`, isolates the
K-injective and evaluation-at-1 comparison, with its complete proof sketch.

`lem-pc-derived-free-module-hom-homology`, in
`Sheaf.Algebra.Homology.DerivedFreeModuleHomology`, is proved for arbitrary rings and
arbitrary unbounded derived objects. No definition, existing statement, or target
signature changed; no change record or forced adaptation is needed.

## Second reading by H1

1. **Interface unchanged.** Compared the delivered target module byte-for-byte with the repository version: the existing theorem signature and all existing declarations are unchanged. The two additional modules contain only new declarations, and the DAG node statements match their Lean signatures.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`; compilation succeeds. The target theorem and the free-module theorem contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The global-sections comparison is the sole explicitly split theorem and retains its documented `sorry`; its node and report entry agree. The free-module proof uses only the permitted derived-category and projectivity lemmas.

3. **New statements.** Checked both added statements against the Stacks Tag 09M1 argument and small edge cases, including the zero ring and empty scheme. The free-module statement is exactly the rank-one projective calculation and imposes no boundedness or commutativity beyond its stated ring hypothesis. The global-sections statement is precisely the remaining sheaf-to-module comparison and does not restate the target. Searches found no existing declaration with either statement.

4. **Route and pruning.** The target proof follows the unit route by composing the structure-sheaf/global-sections comparison with the free-module/homology equivalence and preserving both naturality equations. The removed direct proof-only imports are no longer used; the remaining derived-direct-image import transitively supplies the K-injective infrastructure needed by the split comparison. No unit realized node or proof dependency was bypassed.

5. **DAG agreement.** Updated node proof steps and dependencies to match the actual composition. The two new nodes have complete source, proof, origin, Lean, chapter, and unit metadata. The unit record remains unchanged because the target node still realizes the same unit route.

I changed only the report by adding this second-reading record; no Lean statement or proof was altered during review.
