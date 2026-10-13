## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_coefficientTarget_affine_tensor_presentation`
by a complete Lean reduction with its original signature unchanged. The proof constructs the actual
supported-section map p, proves additivity directly, uses scalar compatibility to make it A-linear,
and extends (r,s) mapping to r*p(s) by `TensorProduct.AlgebraTensorModule.lift`. The unit formula is
proved by `one_smul`. Injectivity and surjectivity make this constructed map a linear equivalence;
the support isomorphism cancellation proves the requested inverse-generator equation.

Added three statement modules, each with one public named theorem, source, complete proof in words,
and matching DAG node. Updated the item's proof and proof dependencies to this construction.
No existing definition, statement, visibility, or public import was changed. No data is chosen from
an unproved existence theorem: the tensor map is constructed and `LinearEquiv.ofBijective` determines
its inverse uniquely.

All four modules compile locally in import order with `lcompile.py`. The original module also
compiled against the published baseline. Source checks used Stacks Tags 02KG, 01I9, 01IA, 0096 and
0097. LeanSearch returned Internal Server Error; LeanFinder, Loogle, and library/Mathlib grep found
unit/restriction infrastructure and the tensor universal property, without an exact geometric match.

## Proved and sorry left

Hole closed (decomposition, not a claim of a sorry-free mathematical proof):
`AlgebraicGeometry.Scheme.Modules.exists_coefficientTarget_affine_tensor_presentation`
(`lem-pc-coefficient-target-affine-tensor-presentation`). No sorry remains in the item's module.

Three holes added, and these are every sorry in this delivery:

- `AlgebraicGeometry.Scheme.Modules.coefficientTarget_generator_scalar`
  (`lem-pc-coefficient-target-generator-scalar`): only the structural scalar transport identity,
  with no affine or quasi-coherence assumption.
- `AlgebraicGeometry.Scheme.Modules.coefficientTarget_tensor_injective`
  (`lem-pc-coefficient-target-tensor-injective`): only injectivity of any linear tensor map with
  the canonical unit formula, by the balanced left inverse.
- `AlgebraicGeometry.Scheme.Modules.coefficientTarget_tensor_surjective`
  (`lem-pc-coefficient-target-tensor-surjective`): only surjectivity, by expressing target sections
  as sums of images of pure tensors.

Thus one upper hole is reduced to three strict parts; net textual hole change is +2. Neither
one-sided theorem supplies the target equivalence or the other side of bijectivity. The main
module constructs the map and combines all three parts in real Lean.

Edge cases checked mathematically: empty Z or B gives zero sections/tensors and the same scalar
identity, left inverse identity, and zero preimage. Zero F is included. No flatness, nonemptiness,
covering, or finiteness assumption is added. The scalar statement requires only the commuting
square, whereas the two geometric properties retain separatedness, affineness, and cartesianness.

## No longer needed

Removed the item's direct proof imports `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and
`Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange`. The main combining proof also no
longer directly uses `lem-weil-pbc-affine-tilde-gamma-adjunction` or
`lem-weil-pbc-open-immersion-module-pullback-restriction`. Those four original dependencies remain
needed in the proof plans of the new injectivity/surjectivity obligations: no global pruning of
these nodes or modules is claimed. The unit's affine coefficient calculation is retained.

The new proof imports are `Mathlib.LinearAlgebra.TensorProduct.Tower` and the three new modules.
The original public imports stay for the unchanged signature. On second reading, the two
geometric obligation modules privately import ModulePullbackAffineSections and
FiniteAffineCechIntersectionBaseChange, retaining their stated proof plans in the import closure.
Their tensor signature uses Basic, not Tower. The scalar module needs neither Tower nor Separated;
both unused public imports were removed from that new module.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The second reading repaired missing proof-plan imports and
dependency citations, and removed unused public imports from the newly created modules. The original single proof step hides both the scalar transport
and the two independent properties of the canonical tensor map. They are made explicit rather
than replacing the target by an equivalent existential statement under another name.

The published compiled snapshot did not yet contain the recently landed
`CoefficientComparisonConstruction`, `CoefficientComparisonMorphismGenerator`, or
`CoefficientSourceAffineTensorPresentation` modules. A route through that construction therefore
could not compile against the allowed baseline. The delivered route uses only the available
support and generator definitions and does not recreate any missing declaration.

## New nodes

`lem-pc-coefficient-target-generator-scalar`, module
`Sheaf.AlgebraicGeometry.CoefficientTargetGeneratorScalar`, records compatibility of the concrete
supported unit section with the exact structural A-action. Its source is Tags 0096 and 0097;
its proof tracks the chart cancellation and the commuting structural square. This is a scalar
identity, not an affine tensor presentation.

`lem-pc-coefficient-target-tensor-injective`, module
`Sheaf.AlgebraicGeometry.CoefficientTargetTensorInjective`, records the injective part of the
Tag 02KG affine tensor calculation. The balanced contraction is a left inverse.

`lem-pc-coefficient-target-tensor-surjective`, module
`Sheaf.AlgebraicGeometry.CoefficientTargetTensorSurjective`, records the surjective part of the
same calculation. Balancing and tensor induction supply preimages. Both nodes retain the parent
unit and original geometric dependencies. All three nodes record LeanSearch unavailability,
LeanFinder/Loogle infrastructure matches, and the duplicate searches by grep and blueprint search.
No change record is needed because no existing interface changes.

## Second reading by C3

1. **Interface unchanged: pass.** Diffed the only existing delivered module against the repository.
   The entire existing theorem signature is byte-identical (checked separately as a string), its
   docstring and the three public imports are unchanged, and no existing definition is edited.
   The local transparency options affect elaboration only. The three other modules and their
   declarations are new. No target or downstream signature is changed; no change record is needed.

2. **Lean reduction and trust: pass, with three named obligations.** Compiled all four files in
   import order with lcompile.py, then compiled independent scratch copies with #print axioms
   for all four public theorems. The main proof has no sorry; it constructs p and c, uses the
   scalar identity only for p.map_smul, proves c(1 tensor s)=p(s), combines the two one-sided
   properties, and cancels coefficientSupportIso. LinearEquiv.ofBijective chooses only the
   uniquely determined inverse of the explicit c. There are no new definitions, unsafe/opaque
   declarations, custom axioms, foreign implementations, or holes in data. The only remaining
   holes are the three public theorems listed above. The axiom lists are the standard three
   axioms and sorryAx, as expected while these obligations and imported obligations are open.

3. **New statements and searches: pass.** Read the three full signatures, docstring arguments,
   and nodes, and independently read Stacks [02KG](https://stacks.math.columbia.edu/tag/02KG),
   [01I9](https://stacks.math.columbia.edu/tag/01I9),
   [01IA](https://stacks.math.columbia.edu/tag/01IA),
   [0096](https://stacks.math.columbia.edu/tag/0096), and
   [0097](https://stacks.math.columbia.edu/tag/0097).
   For the geometric parts the restricted fibre product is Spec(R tensor_A D); quasi-coherence
   identifies its module with (R tensor_A D) tensor_D N. On pure tensors, R-linearity and the
   unit formula force c(r tensor n)=(r tensor 1) tensor n. The balanced contraction
   (r tensor d) tensor n mapping to r tensor (d*n) is its left inverse, proving the injective
   part. Balancing over D expresses each target generator as an image, proving the surjective
   part. These are distinct proper parts of the argument, not another existential equivalence.
   For the scalar statement no affine hypothesis is used: toSpecGamma.appTop equals
   GammaSpecIso.hom; cancellation gives the restricted structural map. The restriction
   isomorphism and adjunction unit are semilinear over the corresponding ring maps; the square
   equality identifies the composites to W intersect fprime inverse image B.
   Checked identity squares, zero F, empty Z, empty B, and the nonflat example A=integers,
   D=R=integers/2, N=D: the contraction and generation formulas remain valid without flatness.
   Repeated searches with different words using msearch.py LeanFinder, Loogle and grep,
   and read Modules/PullbackTilde.lean and the affine section theorem. Spectral unit formulas
   and Hom.app_smul are ingredients, not duplicates. The related coefficientSectionAddMap_linear
   has only the full-open target and its compiled module is unavailable in the allowed snapshot.
   A bounded direct scalar-proof attempt did not close the chart/restriction transport; it is
   left as the named theorem, with no partial proof inserted into the delivery.

4. **Top-down route and pruning: pass after repair.** The upper proof really constructs the
   tensor map and reduces its properties. The old direct dependencies no longer used by that
   proof are lem-pc-finite-affine-cech-intersection-base-change,
   lem-weil-pbc-module-pullback-affine-sections, lem-weil-pbc-affine-tilde-gamma-adjunction,
   and lem-weil-pbc-open-immersion-module-pullback-restriction. They remain in the two new
   geometric proof plans and import closure; no globally pruned module is claimed. Restored
   the two private imports corresponding to the first two nodes in both geometric modules.
   Removed the unused Tower and Separated public imports from the new scalar module and
   replaced Tower by Basic in the two tensor signatures. Read sk-thm-picard-coherence.json:
   its realized statement and step lists are empty in this snapshot, and nothing changes them.
   All four nodes remain in that unit and retain the affine coefficient calculation below it;
   no chapter or unit step is bypassed.

5. **DAG agrees: pass after repair.** Checked every lean.statement against the actual Lean
   signature, every referenced id, and proof_deps equal to the union of proof-step uses.
   The parent records the actual construction and its three obligations. The new nodes carry
   created.item/group/date, source, chapter/unit, blueprint ancestry, searches, proof_origin,
   and the verbatim Lean declaration. Added the previously uncited
   lem-weil-pbc-conjugate-iso-unit-equation and
   lem-pc-finite-affine-cech-coefficient-comparison-map to both geometric nodes: their written
   proofs use adjunction-unit transport and the support identification. Marked failed
   LeanSearch attempts unavailable and recorded the independent searches actually run.

Second-reading changes are import minimization in the three new modules, restoration of the
geometric proof-plan imports, the two missing dependency citations in both geometric nodes,
search verdicts/records, and this detailed report. No existing proof body or signature was
rewritten. The delivery remains a decomposition: one upper hole closed, three lower holes added,
net +2 textual holes, and no claimed globally pruned module.
