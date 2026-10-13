## What changed

Proved `DerivedCategory.exists_finite_localization_free_step` with its existing signature and
visibility unchanged. The proof establishes localized cone vanishing by the long exact sequence,
then localized finite top cone homology using `isPseudoCoherent_iff_forall_isMPseudoCoherent`,
`isMPseudoCoherent_cone`, and `finite_homology_of_isMPseudoCoherent`.

Added two fully proved modules:

- `Sheaf.RingTheory.FiniteScalarSurjections`: a finite family of finite scalar extensions of an
  arbitrary module is covered by one finite free source. The proof collects finite tensor factors
  with Mathlib's `TensorProduct.exists_finite_submodule_right_of_setFinite`, takes their finite
  submodule sum, and uses `Module.Finite.exists_fin'`.
- `Sheaf.RingTheory.FiniteConeCycleAttachmentFunctors`: generalizes the actual construction in
  the proved `FiniteConeCycleAttachment` to detection by additive epi-preserving functors. The
  complex and maps are constructed explicitly. The boundary computation is retained; only its
  final cancellation is performed after applying the detecting functors. The original attachment
  theorem cannot be applied here because global cone vanishing and a global generator
  epimorphism are not hypotheses of this item. The original module is unchanged.

Localization is flat, so the homology comparison identifies localized cone cohomology with
scalar extension of global cone cohomology. Apply the first helper to global cone homology and
lift its finite free source map to global cycles by projectivity. Apply the second helper to
extension of scalars. The localized cone exact sequences then give the improved approximation.
All new imports of the item are proof-only imports. Its three original public imports remain.
The second reading removed the unused public `ModuleCat.Free` import from the scalar helper.
In the attachment helper it replaced that broad import by public imports of
`ShortComplex.ModuleCat`, `FreeModule.Basic`, and `Finiteness.Defs`, which supply the
module-category homology instances, freeness, and finiteness appearing in its signature.
`Finiteness.Basic` is imported privately for the proof. The scalar helper publicly imports
`Finiteness.Defs` for its hypothesis.

The source read was Stacks Tag 08EE, `lemma-lift-pseudo-coherent`, the paragraphs beginning with
the induction step and choosing the finite free module, at
https://stacks.math.columbia.edu/tag/08EE. The source's omitted denominator-clearing step is
implemented through finite tensor factors and projectivity. The unit's `realized` arrays are
empty; no unit statement or realized step is bypassed or edited.

## Proved and sorry left

Closed the single original hole:
`DerivedCategory.exists_finite_localization_free_step`
(node `lem-sc-finite-localization-free-step`). No `sorry` remains in the item's module.

The added public declarations are fully proved:
`ModuleCat.exists_finiteFree_scalar_surjections`
(node `lem-sc-finite-scalar-surjections`) and
`DerivedCategory.exists_finiteFree_cone_cycle_attachment_functors`
(node `lem-sc-finite-cone-cycle-attachment-functors`). All private helpers are proved.
There are zero holes added and zero statements split off with `sorry`; this is a proof, not a
hole decomposition. No existing dependency statement or definition changed.

All three modules compiled together through `lcompile.py --all`. Before the final dry run,
the only warning found was a long docstring line, which was shortened. Empty detecting
families, zero scalar extensions, the zero ring, zero obstruction homology, and `n = b+1`
are covered without new hypotheses. The new scalar-surjection theorem is valid for arbitrary
ring maps; the attachment theorem only needs preservation of epis. Flatness is used exclusively
in the item's homology comparison.

## No longer needed

No original import, node, or module is pruned: both original proof imports are used for local
cone finiteness. The planned chain-level denominator-clearing calculation is replaced by the
finite tensor-factor argument and projective lifting; it had no separate DAG node to prune.
The second reading also pruned the new helpers' broad `Mathlib.Algebra.Category.ModuleCat.Free`
imports, replacing the signature dependencies with narrower public imports and the
attachment proof dependency with a plain import. No original dependency module is pruned.
No unused proof imports remain. In particular the original global `FiniteConeCycleAttachment`
module is read as the construction source, but is not added as a direct import of this item or
of its new generalized attachment module.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or tool failure was found. The old plan was valid but required more
chain-level denominator algebra than necessary. Finitely many finite tensor products can be
covered by finite global homology data, and a free source lifts that data to actual cycles.
Updated the item's proof steps and dependencies to reflect this shorter route.

The generalized attachment proof credits the original proved construction (group D3) and its
source. It does not assume a global generating family or global vanishing that the item lacks.
The two new statements introduce no data chosen from an unproved existence theorem.

## New nodes

`lem-sc-finite-scalar-surjections`, module `Sheaf.RingTheory.FiniteScalarSurjections`, records the
fully proved simultaneous scalar-extension surjection lemma. Mathlib searches found the finite
tensor-factor lemma and finite free covers of finite modules, but no exact simultaneous cover
statement. Its hypotheses allow an empty family and do not imply global finiteness.

`lem-sc-finite-cone-cycle-attachment-functors`, module
`Sheaf.RingTheory.FiniteConeCycleAttachmentFunctors`, records the fully proved attachment
construction with the obstruction tested by epi-preserving additive functors. Searches found
mapping-cone constructions but no such detection theorem. It is strictly the attachment part
of the argument: supplied finite free cycles are inputs and no local pseudo-coherence or
choice of generators is asserted. No change record or forced adaptation is needed.


## Second reading by E3

1. **Existing interface unchanged — pass.** Compared the complete delivered item with
   `lean/Sheaf/RingTheory/FiniteLocalizationFreeStep.lean` in the repository using `diff`.
   Also extracted the text from `theorem exists_finite_localization_free_step` to `:= by`
   and checked byte-for-byte equality. The three original public imports, universes,
   declaration name, hypotheses, conclusion, and visibility are unchanged. The added
   declarations in that module are private proved helpers. There is no definition or
   statement change and no forced adaptation. The existing node differs only in `proof`,
   `proof_deps`, and `proof_origin`.

2. **Kernel proof and construction — pass.** Independently compiled all three delivered
   modules through `lcompile.py --all` after the import repairs, with no errors or warnings.
   Read the cone-cycle equations, the construction `G = mappingCone k`, the map `g`, the
   old-term inclusion, and the cone comparison `t`. In degree `n-1`, the explicit boundary
   of minus the new P-term kills the supplied cycles; above that degree the epic homology
   comparison has zero detected source. The finite scalar-cover proof uses finite tensor
   factors, their finite submodule sum, and a finite free cover of that sum. Every choice
   comes from a proved theorem. No data is chosen from an unproved existence theorem.
   Scanned all files: no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
   Compiled scratch copies with `#print axioms` for
   `DerivedCategory.exists_finite_localization_free_step`,
   `ModuleCat.exists_finiteFree_scalar_surjections`, and
   `DerivedCategory.exists_finiteFree_cone_cycle_attachment_functors`: each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`. Removed the scratch copies.

3. **New statements, source, and searches — pass.** There are no split-off open statements.
   Read [Stacks Tag 08EE](https://stacks.math.columbia.edu/tag/08EE),
   `lemma-lift-pseudo-coherent`, its induction step and finite-free cycle choice, and
   [Tag 064U](https://stacks.math.columbia.edu/tag/064U), its descending construction.
   Matched the new scalar theorem to the finite generator choice: arbitrary ring maps
   are sufficient since tensoring preserves surjections; neither flatness nor joint
   faithfulness is needed. Matched the attachment theorem to the supplied-cycle part:
   additivity preserves the zero composite and preservation of epis enables cancellation.
   Exactness is needed only for the original item's localization/homology comparison.
   Checked empty families, zero scalar extensions and rings, P=0, vanishing obstruction,
   and `n=b+1`: the new term is in degree b and the support proof still applies.
   Independently searched with LeanFinder queries about a common finite-rank free cover
   of base-changed modules and killing cone cohomology after epi-preserving functors;
   neither yielded an exact existing result. Loogle's
   `CategoryTheory.ShortComplex.homologyMap, CategoryTheory.Epi` found the existing
   epi-cycles-to-epi-homology lemma already used by the proof. Grep searches of Mathlib,
   `lean/Sheaf`, `lean/WeilConjectures`, and the upstream checkout found no simultaneous
   cover or detected attachment theorem. Read the tensor finite-factor lemma at
   `Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean:141`. The existing global
   `FiniteConeCycleAttachment` requires global vanishing and a global epi, unavailable
   here; its construction is credited, rather than its statement misapplied.

4. **Top-down reduction and pruning — pass after import repair.** The original proof
   first obtains localized cone vanishing, then finite top cone homology from the existing
   pseudo-coherence and finite-homology statements. Flat homology comparison, simultaneous
   finite scalar covers, projective lifting, and the supplied-cycle attachment give the
   improved approximation. The final long exact sequences give the original iso and epi
   assertions at the precise required degrees. No shorter existing theorem found in the
   independent searches applies with these hypotheses. Every original `proof_deps` node
   is still used, so the original-node pruning list is empty. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and sole realized step
   are empty; no realized unit node is bypassed or edited. Narrowed the new helpers'
   public imports as described above; all extra imports of the original item stay private.

5. **DAG agreement — pass.** Opened all three delivered node records and compared each
   statement with its declaration. The item's three steps name exactly the pseudo-coherent
   approximation, cone finiteness, simultaneous scalar cover, and detected attachment
   statements the Lean uses. Its `proof_deps` is their union and its `proof_origin` records
   the tensor-factor/projective-lift route. The two new nodes state strictly separate
   parts of that route, with complete docstring arguments and fully proved declarations;
   neither is an open restatement of the original item. Checked their source, chapter,
   unit, creation records, search records, blueprint origin, and verbatim Lean signatures.

Second-reading changes: import cleanup only, plus this review and the corresponding
report descriptions. No proof body, theorem signature, definition, or node was changed.
Closed one original hole, added zero holes, split off zero open statements. No original
module or original proof-dependency node is pruned.
