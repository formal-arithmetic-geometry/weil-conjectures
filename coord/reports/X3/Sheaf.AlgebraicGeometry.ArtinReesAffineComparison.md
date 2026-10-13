## What changed

Proved `AlgebraicGeometry.Scheme.artin_rees_affine_comparison` in
`Sheaf.AlgebraicGeometry.ArtinReesAffineComparison`, with its signature and existing docstring
unchanged. All changes are in this module and its proof-route node.

The proof computes arbitrary ideal-module multiplication by tensor induction, using the existing
affine tensor and image theorems. Positive power ranges come from
`ideal_times_quasiCoherent_affine_sections`; exponent zero is checked directly. It constructs
intersections as pullbacks, proves quasi-coherence using the kernel of the binary-sum difference
map, and calculates their section ranges by evaluation preserving pullbacks. Mapping the product
range through the intersection inclusion makes `hmodule` exactly the needed affine range equality.

A proved private localization argument extends range inclusions from U to every W contained in U:
the composite with the other inclusion's cokernel vanishes on basic opens, then on W by sheaf
separatedness; the evaluated kernel and mono image factorization give actual section preimages.
No new mathematical assumptions or public declarations were added.

Added proof imports: `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`,
`Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`,
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`, and
`Mathlib.CategoryTheory.Abelian.Basic`. The multiplication helper follows the private range calculation in
`IdealTimesQuasiCoherentAffineSections`. The duplicated `product_qc` helper has been removed:
the two required product quasi-coherence facts now use the public
`quasiCoherent_cokernel_image` theorem's image quasi-coherence clause, transported by
`Abelian.imageIsoImage`. The existing public ideal-product theorem is used for powers.

Compilation is clean with the prescribed `lcompile.py`. A temporary `#print axioms` check
reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the target, with no
`sorryAx`; the check command was removed before the delivery dry run. The empty open, zero modules, zero/unit
ideals, and c=0 or n=0 are included by the unchanged statement and by the separate exponent-zero
calculation; no nonempty or positivity hypothesis enters the comparison.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.artin_rees_affine_comparison`
(node `lem-weil-pbc-artin-rees-affine-comparison`). No sorry remains in this module. No holes were
added, and no intermediate statements were split off. Every private helper is proved.

## No longer needed

Removed the duplicate private `product_qc` declaration; its two uses now apply the existing
public cokernel/image theorem directly. No additional import or node edge is needed.


No pre-existing import was removed: each of the original imports is used by the statement or proof.
The exploratory imports `Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory` and
`Mathlib.CategoryTheory.Limits.Types.Pullbacks` were removed after compilation confirmed that the
remaining imports supply the required interfaces.

The updated node no longer directly uses `def-weil-pbc-coherent-formal-module`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, or
`lem-weil-pbc-module-restriction-open-immersion-colimits`. Their direct proof edges are replaced
by the actual product constructions and the already proved
`lem-weil-pbc-affine-module-basic-open-localization`. This is direct dependency pruning, not a claim
that their modules leave the full target import closure: the localization theorem itself rests on
the affine tilde and restriction results, and the formal-module node remains a statement dependency.
No further module is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing return at head `0bbc092ea`: removed the duplicate private theorem
`AlgebraicGeometry.Scheme.product_qc`. Direct reuse of `Scheme.Modules.product_qc` was
compiled and failed with `Unknown constant AlgebraicGeometry.Scheme.Modules.product_qc`:
that theorem is private in the existing source. Rather than duplicate its statement or alter
another module's visibility, both required facts now directly reuse the public image
quasi-coherence clause of `Scheme.Modules.quasiCoherent_cokernel_image`. The tensor
comparison supplies quasi-coherence of the multiplication source, and the canonical image
isomorphism identifies its image with the defined ideal product. No helper with the duplicate
statement remains. Clean compilation was rerun after this repair.


The first dry run flagged extra global `open` commands as an interface change. They were
removed and all proof names qualified explicitly. The interface comparison now reports no changes;
no change record or forced adaptation is required.

No false statement or unusable definition was found. The original DAG's explicit restriction and
affine equivalence transport is unnecessary for this node: the existing localization theorem,
evaluation preserving kernels, and the mono image factorization give a direct proof. The
intersection is treated as a kernel of a binary-sum difference rather than as a kernel into a
quotient; both are the same sectionwise intersection. The item's node is not in the unit's
`realized` lists, and none of the unit's fixed statement or steps is bypassed.

Read Stacks [01YA](https://stacks.math.columbia.edu/tag/01YA),
[01I8](https://stacks.math.columbia.edu/tag/01I8), and
[01IC](https://stacks.math.columbia.edu/tag/01IC), and the full `sk-thm-p1` unit JSON. The literature
blueprint `_section.md` path recorded in that JSON is absent on this machine; the JSON contains the
unit statement and complete step texts. No changes to the unit were made.


## Earlier second reading (a previous round; superseded)

Independent second reader; I did not write the proof. I read the complete delivered module,
its repository diff, both versions of the node, all seven dependency declarations, the
`sk-thm-p1` realized record, and the relevant localization and product definitions.
I also read Stacks [01YA](https://stacks.math.columbia.edu/tag/01YA),
[01I8](https://stacks.math.columbia.edu/tag/01I8), and
[01IC](https://stacks.math.columbia.edu/tag/01IC).

1. Interface: PASS. The sole existing theorem's signature is byte-for-byte identical,
   including quasi-coherence of F and G, monicity of g, the arbitrary ideal sheaf,
   affine U, unrestricted natural c and n, the precise truncated-subtraction hypothesis,
   and equality on every W contained in U. Its docstring, public imports, namespace,
   universes and global opens are unchanged. The additions are proved private theorems
   and ordinary proof imports. No definitions, target statements or other modules change;
   no change record is needed.

2. Proof: PASS. Prescribed local compilation completed cleanly in 16.3 seconds.
   A scratch copy with `#print axioms AlgebraicGeometry.Scheme.artin_rees_affine_comparison`
   reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no sorry, axiom, unsafe, opaque, implemented_by or extern in the delivery.
   Tensor induction establishes both range inclusions, not merely containment.
   The abelian image is transported to the chosen categorical image with commuting
   inclusions. Evaluation of the pullback supplies actual compatible section preimages.
   The localization argument requires quasi-coherence only of its source; its target
   cokernel is an actual constructed object, not a witness selected from an open theorem.
   Kernel evaluation and the mono image factorization recover actual sections of B.
   The final two range inclusions therefore prove exactly the claimed equality.

3. Split statements: PASS, none. All nine private helpers are proved, and no public
   statement or new node is added. I checked the empty W and empty U cases: the local
   cover can be empty and sheaf separatedness still applies. Power zero is the structure
   module with identity inclusion, whose range is the unit ideal. Zero F or G, zero or
   unit ideals, c=0, n=0 and n<c introduce no excluded case; hmodule remains the exact
   assumption even when truncated subtraction is zero. No finite generation or
   Noetherian premise is silently used.

4. Route and pruning: PASS. Independent LeanFinder search for detecting zero module
   morphisms from affine sections returned only general hom extensionality and
   structure-sheaf vanishing results, not a shorter exact theorem. Loogle and Mathlib
   grep were also run, and repository searches inspected the existing affine-subobject
   cover theorem and product-range helpers. The cover theorem requires an already
   established subobject inequality and a cover of the whole scheme; it does not
   directly replace the comparison below U. Existing arbitrary-product helpers in
   IdealTimesQuasiCoherentAffineSections and ClosedImmersionIdealPowerImage are private.
   The proof already uses the public power and image theorems. The ordinary imports
   supply power ranges, images, kernels, cokernel quasi-coherence, binary sums, tensor
   comparison, and the pullback-to-biproduct kernel isomorphism in Abelian.Basic.
   Statement imports supply ideal products, ideal-sheaf modules and quasi-coherence.
   All three removed old proof edges are listed under No longer needed; no globally
   pruned module is claimed. The item is absent from sk-thm-p1's realized statement and
   steps, and no fixed unit route or unit file changes.

5. Node agreement: PASS. Only proof, proof_deps and proof_origin differ from the
   repository node. Step 1 matches product_qc, multiplication_range, power_qc and
   power_range; step 2 matches pullback_qc and pullback_range; step 3 matches hi, hl
   and he; step 4 matches app_zero_below_affine, range_le_below_affine and heW.
   The seven proof dependencies are the union of the steps' uses and supply the
   definitions and results actually invoked. In particular the product-stalk node
   carries the image-product and power definitions, although its stalk theorem is
   unnecessary here. The affine tensor, image, kernel, binary-sum and localization
   statements have exactly the hypotheses required at their uses. Cokernel
   quasi-coherence is also a clause of the cited cokernel-image node.

Second-reading changes: appended this review and logged independent searches. No repair
of Lean or DAG was needed. One original hole is closed, zero holes are added, and no
intermediate statement is split off. Scratch axiom checks remain outside lean/ and are
not part of the delivery.

## Second reading by X3

1. Interface and statement: PASS. I compared the delivered module with the repository version. The public theorem signature and docstring are byte-for-byte unchanged; only proof imports, private helpers, and the proof body differ. The node statement likewise remains unchanged.

2. Proof and axioms: PASS. `lcompile.py --all` compiles the sandbox cleanly. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; its private helper declarations are all proved. The existing scratch axiom check records only `propext`, `Classical.choice`, and `Quot.sound` for the target.

3. Split statements and edge cases: PASS. No statements were split off and no new holes were added. The zero exponent branches are handled explicitly, and the range and localization arguments apply to empty opens, zero modules, and arbitrary truncated subtraction without extra hypotheses.

4. Route and pruning: PASS. The proof uses the affine tensor, product, image, pullback, kernel, and basic-open localization results required by its actual route. The duplicate private product quasi-coherence helper was removed in favor of the public image clause. The old direct proof edges replaced by the localization route are recorded under `No longer needed`; the unit route and realized records are unchanged.

5. DAG agreement: PASS. The node proof steps, dependencies, and proof origin match the declarations and imports used by the delivered proof. No statement or definition change record is needed.

I changed only this report section after reading: no Lean repair was necessary. The dry run is now ready to repeat.
