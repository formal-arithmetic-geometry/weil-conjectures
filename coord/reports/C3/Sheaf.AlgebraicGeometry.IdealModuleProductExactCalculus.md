## What changed

Proved `AlgebraicGeometry.Scheme.idealModuleProduct_exact_calculus` in
`Sheaf.AlgebraicGeometry.IdealModuleProductExactCalculus`, with its original signature
and visibility. All three clauses are proved: subobjects, quotients, and middle-exact
complexes. The proof works on stalks and uses the already proved product range and
stalk exactness declarations. Eight fully proved private helpers supply zero detection,
scalar annihilation, stalk injectivity/surjectivity, and the affine germ description
that identifies the stalk ideal of J*K with the product of the two stalk ideals.

Added proof-only imports of `Sheaf.Algebra.Homology.ModuleStalkExact`,
`Sheaf.AlgebraicGeometry.IdealModuleMultiplicationStalkRange`,
`Mathlib.Topology.Sheaves.Abelian`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`. All three original public imports
remain necessary for the statement. Updated the existing node's proof, proof_deps,
and proof_origin to describe the actual stalk argument. No definitions, public
interfaces, or other modules were changed.

Source read: Stacks Project Tag 0CYV, `lemma-systems-with-proper-support`, proof of (2),
https://stacks.math.columbia.edu/tag/0CYV. The zero-stalk criterion and ideal operations
were checked directly in the pinned Mathlib sources. Mathlib search found exact-sequence
ring-module lemmas but no matching sheaf annihilator calculus; LeanSearch was unavailable.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.idealModuleProduct_exact_calculus`
(node `lem-weil-pbc-ideal-module-product-exact-calculus`). This proves all three
conjuncts, with no new holes and no holes remaining in the delivery. The eight private
helpers are proved. This is a proof, not a decomposition. Local launcher compilation
passes without warnings; the delivery dry run performs its axiom probe and preflight.

The edge cases are included by the proof: the empty scheme has no stalk obligations;
zero ideals and zero modules satisfy the scalar-annihilation criterion; the exact-complex
argument needs no injectivity or surjectivity on the outer arrows. In particular a
complex with zero outer arrows forces its middle stalk to be zero by exactness.
No arbitrary existence witness is used to define data; stalk identifications and
preimages are used only inside proofs.

## No longer needed

The direct proof dependency `lem-weil-pbc-ringed-space-module-exactness-local-lifting`
and its module `Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` are not
needed by this proof. Stalk exactness replaces the section-cover lifting argument.
No claim is made that this module leaves the entire targets' closure: other importers
may still need it.

`def-pur-sheaf-tensor-product` is no longer a direct proof dependency. Tensor products
remain part of the definition of idealModuleProduct and of the imported stalk-range
results, so `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` is retained
transitively and is not claimed globally pruned.

Removed the two original proof-only imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`. The tensor-product
definitions remain available through the statement dependency
`Sheaf.AlgebraicGeometry.IdealModuleProductStalk`; local lifting is replaced by
`Sheaf.Algebra.Homology.ModuleStalkExact`. A trial explicit import of
`Mathlib.RingTheory.Ideal.Operations` was omitted after checking that the required
operations already arrive through the original public dependencies. The proof needs
neither power nor quotient clauses of ideal_module_product_stalk, though that module
remains needed for its definition, injectivity, and structure-sheaf stalk identification.
The item's node is not a realized unit statement or unit proof step, and no realized
unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned local-cover argument was mathematically sound but unnecessary. Its direct
tensor-product and local-lifting proof dependencies were replaced as above. One interface
detail needs care: ideal_module_product_stalk supplies an identification of the unit
stalk existentially. For products involving both J and K the proof uses a single
identification and invokes ideal_multiplication_stalk_range with it, rather than assuming
that independently supplied identifications are definitionally equal. The new affine
germ helper proves the compatibility of IdealSheafData multiplication with stalks.
There is no statement dispute, interface correction, forced adaptation, or new node.


Historical retry verification (2026-10-13; tooling blocker resolved in the current round): the saved module compiled again through the prescribed
`lcompile.py` entry point, exit code 0, in 11.2 seconds, without warnings. The required
`deliver3.py C3 Sheaf.AlgebraicGeometry.IdealModuleProductExactCalculus --no-push`
dry run still exits with an ImportError in `check_import_sources` (line 65):
`cannot import name 'refuse_missing' from 'import_cycles'`. The repository's
`tools/import_cycles.py` provides neither `refuse_missing` nor `source_roots`, both
requested by that import. This is a tooling blocker, not a proof failure. No tool was
edited or bypassed, and nothing was pushed. The saved independent second reading below
is preserved. A maintainer repair of the launcher/repository tool interface is required
before this delivery can obtain OK.

## Earlier second reading (a previous round; superseded)

1. **Interface: PASS.** Diffed the only delivered Lean module against the repository.
   The signature of `AlgebraicGeometry.Scheme.idealModuleProduct_exact_calculus`
   is byte-for-byte identical. All three original public imports remain; only
   proof-only imports, private proved helpers, the proof and its explanation changed.
   No definitions or statements in other modules were changed; no change record is needed.
2. **Proof and axioms: PASS.** Independently compiled the module with `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms` for the
   main theorem and each of the eight private helpers: all use exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read every proof, including
   affine representatives, common-neighborhood restriction, and middle exactness.
   No `sorry`, axiom, unsafe, opaque, extern, implemented_by, hollow definition, or
   arbitrary-witness data construction is present. Existential stalk identifications
   and preimages are eliminated solely inside proofs.
3. **Split statements and edge cases: PASS.** No statement is split off and no hole
   is added. The private helpers are proved and strictly intermediate. Checked empty
   schemes, zero ideals/modules, identity maps, and exact complexes with zero outer
   maps: the latter force the middle module to vanish on stalks. Neither outer map
   is assumed injective/surjective in clause (3). The same germ-compatible unit-stalk
   identification is used for both ideals, avoiding an unjustified equality of choices.
4. **Route and pruning: PASS after reporting repair.** Checked the source annihilator
   argument in [Stacks Tag 0CYV](https://stacks.math.columbia.edu/tag/0CYV), proof (2).
   Independently searched the IdealSheaf module bridge, upstream Mathlib ideal-sheaf
   operations, the Sheaf ideal-module modules, and Loogle `LinearMap.range, ⊥`.
   The existing range, exactness, ideal-map, and zero-stalk lemmas are used; no matching
   sheaf exact-calculus result was found. The scalar and affine assembly needs no
   further holed lemma. Public imports supply statement types, and each added plain
   import supplies a proof declaration unavailable through public dependencies.
   Both discarded old proof dependencies are reported. Inspected
   `dag/units/sk-thm-p1.json`: the item and discarded nodes are not its realized
   statement or steps, so its prescribed route remains intact.
5. **DAG: PASS.** Compared the node JSON: only `proof`, `proof_deps`, and
   `proof_origin` differ. The seven steps describe the actual Lean helpers and
   assembly, and `proof_deps` is exactly the union of their `uses`. The original
   statement, Lean statement record, source, chapter, unit, and other fields remain
   unchanged. There are no new nodes to audit.

Second-reading repair: corrected `## No longer needed`, which incorrectly said no
original import was removed. It now names the two removed proof-only imports and
explains why tensor-product definitions remain available transitively. The Lean proof
and node were correct and were preserved. One original hole is closed; zero holes
are added. No claim of global module pruning is made.


## Second reading by C3

1. Interface: PASS. Independently diffed the sole delivered module against the
   read-only repository and compared the existing theorem signature byte for byte.
   It is unchanged. All original public imports and visibility remain unchanged;
   the changes are proof-only imports, eight private proved helpers and the proof.
   There are no definition changes, forced adaptations or change records.
2. Proof: PASS. Read each helper and all three clauses. Independently compiled the
   delivered file through lcompile.py (12.2 seconds, no warnings). Verified that
   the scratch axiom probe contains exactly the delivered source before its probes,
   then compiled it (10.4 seconds): the theorem and all eight helpers use only
   propext, Classical.choice and Quot.sound. No sorryAx or forbidden construct is
   present. Existential identifications and preimages are used solely in proofs.
3. Split statements: PASS. None are added; one original hole is closed and zero
   holes added. The intermediate private theorems are fully proved. Checked empty
   schemes, zero ideals and modules, identity morphisms, and exact complexes whose
   outer arrows are zero. The last case forces the middle stalk to be zero. The
   argument uses only middle exactness and a single germ-compatible unit-stalk
   identification for both ideals.
4. Route and pruning: PASS. Read the annihilator argument in
   [Stacks Tag 0CYV](https://stacks.math.columbia.edu/tag/0CYV), proof (2), and the
   imported stalk-range and stalk-exactness declarations and IdealSheaf.Module
   bridge. Searched the library and pinned Mathlib for exactness and annihilators,
   including Mathlib RingTheory/Ideal/Maps.lean. Its injective/surjective annihilator
   lemmas express the same elementary scalar steps but do not replace the sheaf or
   ideal-product argument. Loogle was also queried for Submodule.annihilator.
   No shorter complete sheaf calculus result was found. Proof imports supply stalk
   exactness, multiplication range, zero detection and module exactness; public
   imports supply the statement. Both removed old proof dependencies and imports
   are listed under No longer needed. Inspected sk-thm-p1.json: neither the item
   nor the removed dependencies realize its statement or steps; its route is kept.
5. DAG: PASS. Programmatically checked that only proof, proof_deps and proof_origin
   change and that proof_deps equals the union of the seven steps' uses. Read the
   steps against the Lean argument. Statement, source, Lean record, chapter and
   unit remain unchanged. No new node needs review.

Current second-reading changes: preserved the correct Lean proof and node; marked
an earlier tooling-failure paragraph as historical and added this independent review.
The previous ImportError no longer occurs: the current dry run reached preflight and
requested this review section. No mathematical or interface repair was needed.
