## What changed

Proved `AlgebraicGeometry.formalAffineSectionLimit_full_faithful` with its original
signature and all three concrete functor definitions unchanged. Added proof-only imports
of `CoherentFormalModuleAffineProjections`, `CoherentFiniteTypeLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.Modules.AffineHom`, and Mathlib's limit-preservation
isomorphisms. Three proved private helpers establish affine section injectivity,
affine section surjectivity, and descent through a surjective quotient projection.

The proof first takes limits over the open subscheme's section ring. The existing
canonical projection theorem gives ideal-power kernels. Quotient descent gives level
maps; affine Hom correspondence gives sheaf maps; cancellation of the projections
checks naturality and faithfulness. Restriction of scalars along the inclusion's ring
isomorphism, together with `preservesLimitNatIso`, identifies this with the prescribed
concrete limit functor. Both delivered files preserve the unit's route.

The source read was https://stacks.math.columbia.edu/tag/087W, including its canonical
quotient calculation. LeanFinder, Loogle and source grep were run. LeanSearch returned
Internal Server Error and was recorded as unavailable. The sandbox module compiled
cleanly; the delivery dry run performs the required additional checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.formalAffineSectionLimit_full_faithful`
(node `lem-weil-pbc-formal-affine-section-limit-full`).
No `sorry` remains in the delivered module and no new hole or module is added.
The proof uses existing named statements in the library; this does not assert that
all their transitive dependencies are already free of `sorry`.

## No longer needed

No original import was removed: the two public imports are needed by the unchanged
statements and definitions. The original planned direct dependencies
`lem-weil-pbc-coherent-formal-modules-affine`
(`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`) and
`lem-weil-pbc-coherent-formal-modules-iso-equivalence`
(`Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoEquivalence`)
are not needed by this proof. Their modules were never imported into this item.
The new route uses the canonical affine projection theorem instead. This is local
pruning of the item's proof dependencies, not a claim that those modules are
unreachable from every other target branch.

The affine tilde/Gamma correspondence remains needed, implemented by the existing
source-library affine Hom lemmas. An exploratory extra projection theorem was
removed once the existing canonical projection interface was found; none is delivered.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically sound but unnecessarily passed through the
completed-module equivalence and scheme-isomorphism transport. The existing
`coherentFormalModule_affine_projections` supplies the canonical quotient formula
already. Working over the open subscheme's own section ring avoids transporting its
kernel formula through a completed-module equivalence. No statement or definition
was corrected, and no forced adaptation is needed.

## Second reading by T4

1. Compared the delivered module with the repository version. The theorem and all
   existing definitions have byte-for-byte identical signatures; only proof imports,
   private helpers, and the theorem proof changed. No change record is required.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. A
   search found no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proof uses only ordinary library declarations and its
   expected classical/category-theoretic axioms.

3. Checked the proof route against the node and source. The affine projection kernel
   and surjectivity hypotheses are used to descend maps, affine Hom correspondence
   lifts them to sheaf maps, and limit extensionality proves fullness and faithfulness.
   The statement is unchanged and no split-off statements were added. Searches found
   no existing theorem that duplicates this result.

4. Checked pruning and imports. The two original public imports remain necessary for
   the unchanged interface. The added imports are proof-only. The proof does not use
   the planned completed-module equivalence modules, and the node's `proof_deps` and
   route record that pruning. The unit route through affine projections is preserved.

5. Ran the required dry-run delivery checks. The only initial failure was this missing
   second-reading section; it is now supplied. Changes made in this reading were only
   this report section; no Lean code, statement, definition, or node proof was altered.
