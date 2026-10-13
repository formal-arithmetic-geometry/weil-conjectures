## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.Scheme.picard_fixed_model_residue_derived_comparison` without
changing its signature or public imports. Its proof now applies source residue
minimality, obtains comparisons on each target cycle subspace, and extends those
comparisons to the product of all degree-one terms.

Added `Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality`, with a complete
proof of `AlgebraicGeometry.Scheme.affine_betti_model_residue_minimality` from the
existing `affineFree_residueSections_cohomologyLinearEquiv`. Free sections give
finite residue terms. Injectivity of the cycles inclusion and surjectivity of the
homology projection, together with equal dimensions, force all differentials to
vanish. The scalar-extension adjunction makes every original free coordinate
belong to the evaluation kernel. The residue algebra map annihilates it, proving
vanishing over the affine residue field by tensor induction.

Added `Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison`, whose
statement isolates the geometric comparison on the outgoing kernels. It assumes
the proved source minimality instead of assuming Betti-rank presentations. It
constructs no extension off the kernels and no product map. Its docstring gives
the full geometric proof plan and the relevant existing declarations remain
imported there for the next worker.

The proved `residue_cycle_product_comparison` in the new module
`Sheaf.LinearAlgebra.ResidueCycleProductComparison` chooses complements
by Mathlib's proved `Submodule.exists_isCompl`, projects to the cycle subspaces,
and composes with tensorized coordinate projections. `baseChange_comp` identifies
the chain-map coordinates, and `projectionOnto_apply_of_mem_left` fixes each cycle.
This assembly is valid for arbitrary index types, including the empty family, and
for zero source rank. No data definition was added and no signature was adapted.

Initial author validation: all five initial modules compiled and their axiom probes ran through
`deliver3.py P4 Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison
--no-push`. The final dry run printed OK, passing preflight except for the second
reading, which belongs to the independent reader. Nothing was pushed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.picard_fixed_model_residue_derived_comparison`
(node `lem-sc-picard-fixed-model-residue-derived-comparison`). This is a decomposition,
not a sorry-free proof of all geometric prerequisites.

Proved the new public theorem
`AlgebraicGeometry.Scheme.affine_betti_model_residue_minimality`
(node `lem-sc-affine-betti-model-residue-minimality`), and the new generic module’s
public theorem `AlgebraicGeometry.Scheme.residue_cycle_product_comparison`
(node `lem-sc-residue-cycle-product-comparison`), with no direct holes.

The second reader removed the redundant term-comparison declaration and node,
inlining its proved assembly into the assigned theorem. The combined module
compiles within the single-file limit.

Exactly one new hole remains:
`AlgebraicGeometry.Scheme.picard_fixed_model_residue_cycle_comparison`
(node `lem-sc-picard-fixed-model-residue-cycle-comparison`). It is the entire proof
of a named public theorem in its own module. Source minimality and extension from
cycles are genuinely separate arguments, both proved. The delivery closes one
original hole and adds one geometric hole, so its direct hole balance is zero.

## No longer needed

No original dependency was globally pruned. The geometric dependencies remain
needed by the cycle comparison. Removed the original direct proof imports
`Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial`,
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` from the
assigned module; they remain below the cycle comparison, so none is globally
pruned. All original public imports are retained. The old direct proof DAG is replaced by source minimality,
cycle comparison, and the proved algebraic product extension. No unit step is bypassed.

The old direct proof_deps no longer directly cited by the assigned proof are
`def-sc-derived-fiber-betti`, `def-sc-structure-sheaf-cohomology-pullback`,
`def-weil-residue-field`, `lem-pc-cohomology-sections-affine-base`,
`lem-pc-module-pullback-adjunction`, `lem-pc-rf-perfect-base-change`, and
`lem-sc-field-pullback-rank-one-trivial`. They remain in the statement vocabulary
or below the new comparison/minimality nodes; no original module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated substantial intermediate theory as a reason to abandon.
The existing affine residue cohomology comparison suffices for the source minimality
step; the remaining geometric step can be stated strictly on cycles. The projection
and product construction is independent algebra and is completely proved here.
No mathematical statement error was found. The unit route and the assigned theorem's
hypotheses and conclusion are preserved.

The source lists Tag 08CR, which is a perfect-complex triangle lemma rather than the
specific naturality calculation. The relevant geometric source here is Tag 0BF2's
coefficient pullback argument together with arbitrary base change in Tag 0B91.
LeanSearch was attempted and returned an unavailable-service response; LeanFinder,
Loogle and source grep searches were performed and recorded.

One earlier dry run compiled the delivery but failed the import-source guard
because it could not locate Mathlib sources. The expected package source path
resolved on retry, and the final dry run passed. No tool or shared configuration
was changed by this worker.

## New nodes

`lem-sc-affine-betti-model-residue-minimality`, module
`Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality`: bounded affine free
Betti-rank models have zero section differentials after extension to kappa(p).
This is proved from the existing affine free residue comparison and linear algebra;
it imposes no geometry of a direct image and needs no finiteness hypothesis on E.

`lem-sc-picard-fixed-model-residue-cycle-comparison`, module
`Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison`: the geometric
coefficient-pullback comparison restricted to each target residue cycle subspace.
This is the sole new sorry. Its source, full proof in words, dependencies and
unchanged unit ancestry are recorded. It cannot supply the assigned conclusion by
one application: the assigned proof also proves minimality and the extension to
arbitrary target degree-one vectors by projections and product assembly.

No change records or forced adaptations are needed: all existing signatures,
visibility and public imports stay unchanged.

`lem-sc-residue-cycle-product-comparison` is the fully proved generic algebraic
extension step, in `lean/Sheaf/LinearAlgebra/ResidueCycleProductComparison.lean`.
It chooses complements and uses tensorized coordinate projections, so it works
for arbitrary index types without commuting tensor product with an infinite product.
Its node is `dag/nodes/sec-abelian-varieties/lem-sc-residue-cycle-product-comparison.json`.

The initially added term-comparison module and node were removed by the second
reader: their assembly is now directly in the assigned theorem.

## Second reading by P4

1. Compared the assigned module with the repository using diff, and compared the
   text from its theorem name through the final conclusion before `:= by`:
   byte-identical. Existing public imports and visibility are unchanged. The three
   other delivered modules are new; no definition, target, or other existing module
   is changed. No change record or forced adaptation is needed. Verdict: pass.

2. Compiled all five initial modules locally in import order, then compiled the
   combined assigned theorem after inlining (44.4 seconds). The final delivery has
   four modules and one direct `sorry`, exactly the named public cycle comparison.
   There are no definitions in the delivery and no axiom, unsafe, opaque, extern,
   implemented_by, or hidden proof holes. The delivery dry run performs the axiom
   probes for every declaration; downstream `sorryAx` is expected from the open
   geometric comparison and upstream prerequisites. Classical choices occur inside
   proofs of existence, not data definitions. Verdict: pass. The final dry run printed OK, including compilation, axiom
   probes and preflight.

3. Read the cycle-comparison signature and complete proof docstring against
   [Stacks Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2), specifically the
   coefficient arrows and common source trivialization, and
   [Tag 0B91](https://stacks.math.columbia.edu/tag/0B91), arbitrary base change.
   Flatness of f makes the invertible coefficient relatively flat; properness and
   local finite presentation supply the direct-image comparison. The universal
   structure unit excludes an empty source fibre, so field rank-one triviality
   applies to the descended coefficient. Pulling back that one trivialization,
   rather than using unrelated target trivializations, gives the required
   naturality. Strict perfection makes termwise tensor compute derived tensor.
   The immersion supplies equal residue fields. Zero source differentials identify
   its degree-one term with H-one; the zero target incoming differential identifies
   its H-one with the outgoing kernel. The chain-map equation puts every residue
   image in this kernel. Empty families still assert the source comparison; zero
   source rank forces source H-one zero. No nonempty target is assumed. Verdict:
   true and strictly smaller than the item: source minimality and extension off
   cycles are separate, proved arguments.

   Independently searched with LeanFinder for cohomology functoriality, derived
   pushforward and affine residue perfect models; results were general scheme
   morphism APIs, not this comparison. Loogle found LinearMap.baseChange_comp;
   msearch grep for residue naturality/minimality found no matching result.
   Source rg searches of lean/Sheaf, lean/WeilConjectures and the upstream checkout
   found LocalizedStrictPerfectResidueHomology and ResidueStalkHomologyMapComparison.
   I read these: they concern stalk tensor and degree-zero localized homology,
   not the geometric coefficient arrow and degree-one affine section comparison.
   They cannot close this hole by a short application. The upstream short-complex
   finrank formula could replace the private dimension argument, but the present
   injective/surjective argument is already direct and avoids that import.

4. Checked the proof top down. Minimality uses the existing affine free residue
   cohomology equivalence, term finiteness, cycles inclusion injectivity and homology
   projection surjectivity. Equal dimensions make the cycles inclusion surjective,
   hence the differential zero. The scalar-extension adjunction and kernel of
   evaluation transfer this to kappa(p), without assuming evaluation is surjective.
   The generic assembly uses proved Mathlib complements and projections, and
   baseChange_comp; it works for arbitrary index types without commuting tensor
   with infinite products. Public imports provide signature vocabulary; new proof
   dependencies use plain imports. Read dag/units/sk-prop-av-cube.json: its realized
   statement and sole step are empty in this checkout, and remain unchanged. The
   theorem-of-cube ancestry and coefficient/base-change route are kept. Verdict:
   pass. The unnecessary elaboration helper was removed, not used to evade the
   single-file compile limit.

5. Read all delivered nodes and compared their statements, declarations, proof
   steps, proof_deps and proof_origin with the Lean. Updated the item's proof to
   record the three actual reductions: minimality, cycle comparison, product
   extension. Removed the obsolete assembly node and its cycle- and product-node ancestry
   entries. New nodes have source, docstring proof, search records, creation record,
   unit/chapter ancestry and Lean signatures. Verdict: pass.

Changes by the second reader: inlined the term-comparison proof, removed its module
and node, updated the item DAG and cycle/product-node ancestry, corrected the report’s
attribution of the generic theorem, and completed the dependency accounting below.
No mathematical statement was changed and no additional hole was introduced.

The direct hole accounting is one original hole closed and one new cycle-comparison
hole added: a decomposition with net zero, not a sorry-free geometric proof.

Final second-reader validation: deliver3.py --no-push printed OK at cce95bd730.
The tool classifies this delivery CODEX because it adds three modules/nodes and
one named geometric hole. Compilation and all delivery axiom probes passed.
