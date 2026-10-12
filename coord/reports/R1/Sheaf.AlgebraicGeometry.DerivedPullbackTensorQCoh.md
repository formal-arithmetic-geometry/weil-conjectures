## What changed

The existing theorem's signature is unchanged. Its proof now performs affine localization and gluing in Lean. For pullback, it chooses an affine neighborhood V of each image point and an affine neighborhood U contained in its inverse image, uses the chart computation, proves these neighborhoods cover X, and glues each cohomology sheaf. For tensor, it uses the full affine-open cover and glues degree by degree. Both use Mathlib's `SheafOfModules.IsQuasicoherent.of_coversTop`.

Two new modules contain the remaining affine-local calculations, each with a source and a detailed natural-language proof. The proof uses no global preservation lemma. All three modules compiled together. Searches found the Mathlib locality tools but no derived preservation theorem; LeanSearch returned an internal server error.

## Proved and sorry left

`AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh`: the sole original sorry is replaced by the complete cover/gluing proof.

Remaining named sorries added by this delivery:

- `AlgebraicGeometry.derivedPullback_cohomology_over_affine`, node `lem-pc-derived-pullback-qcoh-component`, in `Sheaf.AlgebraicGeometry.DerivedPullbackPreservesQCoh`.
- `AlgebraicGeometry.derivedTensor_cohomology_over_affine`, node `lem-pc-derived-tensor-qcoh-component`, in `Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh`.

These assert one degree of cohomology on an affine chart; the pullback calculation additionally assumes that the chart maps into an affine chart on Y. The main theorem constructs the relevant charts and cover and performs the global gluing. Empty schemes and empty affine opens cause no issue, and no boundedness, quasi-compactness, or flatness hypothesis is introduced.

## No longer needed

The item no longer directly imports `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` or `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`; the two new affine-local modules import them for their remaining proof plans. Thus neither dependency node is globally pruned, and no underlying modules or nodes are declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The affine formulas and equivalence do not directly supply the needed compatibility of cohomology with restriction, scheme affine chart isomorphisms, and the concrete K-flat tensor representative. Those bridges remain in the new affine-local theorem proof plans. The local source file `literature/stacks-project/perfect.tex` was absent; the source proofs were read at https://stacks.math.columbia.edu/tag/08DW and https://stacks.math.columbia.edu/tag/08DX. The unit's realized arrays are empty; this follows the original two affine-local proof steps and preserves both original dependency modules below the new nodes.

## New nodes

`lem-pc-derived-pullback-qcoh-component`, module `Sheaf.AlgebraicGeometry.DerivedPullbackPreservesQCoh`: the restricted cohomology of the pullback on an affine chart mapping into an affine chart. The proof plan uses open-restriction compatibility and the affine tilde/base-change formula, together with the affine derived equivalence.

`lem-pc-derived-tensor-qcoh-component`, module `Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh`: restricted cohomology of the concrete K-flat tensor representative on an affine chart. The proof plan uses restriction of K-flat models and the affine tensor/tilde formula, together with the affine derived equivalence.


## Second reading by R1

1. **Existing interface unchanged: pass.** Read the complete diff against the repository.
   The only changes in the original module are its two private proof imports and the
   theorem body. The theorem signature, universes, instance hypotheses, local tensor
   instance, public imports and original docstrings are byte for byte unchanged.
   The two other modules and their declarations are new; no definition or statement
   of the library is modified, so no statement-change record is required.

2. **Kernel checking and remaining obligations: pass as a partial delivery.** Compiled
   all three modules in dependency order using lcompile.py. Independently compiled
   scratch copies with `#print axioms` for all three named theorems: each lists only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The main theorem has
   no syntactic sorry; its two affine-local dependencies each have exactly one
   public named theorem whose entire proof is `by sorry`. These are precisely the
   two obligations listed above, each with its node and source/proof docstring.
   No axiom, unsafe, opaque, implemented_by, extern, or hollow definition occurs.
   This is a checked reduction to two open affine calculations, not an axiom-free
   completion of derived preservation.

3. **Affine calculations: pass.** Read Stacks Tags 08DW, 08DX and 06Z0 online and the
   complete imported affine-comparison and affine-equivalence modules. For pullback,
   U and V are affine, hUV gives the restricted morphism, and hE supplies every
   quasi-coherent cohomology sheaf on V. The open-restriction comparison and affine
   base-change formula produce a tilde complex on U, whose cohomology is quasi-coherent.
   For tensor, hP is the K-flat hypothesis needed to compute the derived tensor by
   the particular total complex; hPQ and hNQ are assumptions on cohomology, not on
   individual terms. Restrict, represent both derived objects by module complexes,
   and use the affine tensor comparison. Arbitrary sums in unbounded totalization
   are allowed: tilde is a left adjoint, not merely additive. No quasi-separatedness,
   boundedness, termwise quasi-coherence, or flatness of f is being assumed.
   Tested mathematically the empty scheme/open (zero restricted sheaf), zero input
   complexes, the identity morphism and a nonflat affine ring map. Each local
   assertion remains true; the nonflat case requires derived, not ordinary, tensor.
   These statements leave chart transport, restriction/cohomology compatibility
   and comparison of K-flat representatives to formalize; they are not an immediate
   one-line consequence of the imported Lean declarations. Neither can be closed
   responsibly in a few minutes. They are strictly local calculations, while the
   submitted main proof constructs and glues covers, so this is not a renamed copy
   of either global conjunct.
   Fresh independent LeanFinder query: "restriction of cohomology of derived inverse
   image to an affine open is quasicoherent" returned only underived restriction and
   quasi-coherence tools. Loogle located IsQuasicoherent.of_coversTop. The launcher
   grep query "mapDerivedCategory.*homology|homology.*mapDerivedCategory|tilde.*homology|
   homology.*tilde" found no direct match. Additional rg searches of lean/Sheaf,
   lean/WeilConjectures and the upstream WeilConjectures checkout found no existing
   affine-local derived preservation theorem; Mathlib Tilde.lean supplies the
   underived tilde quasi-coherence and restriction instances only.

4. **Route and pruning: pass.** Checked the pullback cover point by point: choose V
   about f(x), then U about x inside its inverse image. The proof uses the local
   pullback theorem on U and proves the supremum of these opens is top, including
   the empty X case. Tensor uses every affine open and iSup_affineOpens_eq_top.
   Both apply Mathlib IsQuasicoherent.of_coversTop in each degree; the class-valued
   local `have` declarations provide the required instances. No shorter global
   preservation theorem was found. The old proof dependencies
   lem-pc-affine-derived-pullback-tensor-tilde and
   lem-pc-affine-qcoh-derived-equivalence are no longer direct dependencies of the
   main node but remain dependencies/imports of both new affine-local nodes.
   Consequently no node or module is globally pruned. The unit record
   dag/units/sk-thm-picard-f-representable.json has empty realized arrays; no
   realization is bypassed or changed, and the original affine route remains.

5. **DAG consistency: pass after metadata repairs.** Compared the old and new main
   node: only proof, proof_deps and proof_origin change. Its two steps now cite the
   two local calculations and describe the exact covers and gluing in Lean. Both
   new nodes cite the original affine formulas/equivalence and have matching Lean
   statements, source/proof docstrings, status, created, chapter, unit and searches.
   Corrected their blueprint.from.node from the immediate item to
   lem-pc-projection-formula, as `tools/blueprint_refs.py ancestor` requires, and
   replaced the generic decomposition place by the precise preservation use in
   proof step (2). Searched the whole blueprint for "derived pullback" and "tensor";
   no blueprint statement duplicates either affine-local assertion. Added the exact
   Stacks labels to the new source places and removed Lean comment delimiters from
   their natural-language proof fields.

Second-reading changes: removed the unused public KFlat import from the new pullback
module (its statement does not mention K-flatness); corrected the two new nodes'
blueprint provenance and source labels; cleaned their proof text. The checked cover
proof and all theorem statements were kept. No change record is needed for these
repairs to new modules/nodes.
