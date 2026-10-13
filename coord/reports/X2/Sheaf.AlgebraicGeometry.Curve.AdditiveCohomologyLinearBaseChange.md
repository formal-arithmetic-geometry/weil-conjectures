## What changed

The statement and public imports of `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyLinearBaseChange` are unchanged. Its proof now constructs the canonical tensor-linear map and its normalized inverse, rather than leaving the whole assertion unproved.

The private helper `additive_cohomology_pullback_smul` is proved directly. It chooses the scalar sheaf maps from the supplied hypotheses, compares their composites with q through the upper-star/lower-star adjunction, proves equality on sections using multiplication preservation and the displayed pullback square, and applies cohomology naturality. This proves the actual pullback is compatible with the given scalar actions; it does not assume a base-change equivalence.

The target then restricts scalars on the target cohomology group, constructs the k-linear pullback, and uses `TensorProduct.AlgebraTensorModule.lift` on the bilinear map `(b,x) ↦ b • pullback(x)`. Its pure-tensor formula is definitional. Two new proof-only imports supply triviality of its kernel and surjectivity. Injectivity follows by applying the kernel theorem to `z-w`. `LinearEquiv.ofBijective` constructs its equivalence; cancellation and the formula at `b=1` establish the requested normalization of the inverse.

All three modules compile together without warnings through lcompile.py. No definition or existing signature was changed, and no other module was adapted. The two new modules each contain one named public theorem with its entire proof postponed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.IsCurve.exists_additive_cohomology_linear_base_change`, node `lem-pbc-additive-cohomology-linear-base-change`. Its new private scalar-compatibility helper is fully proved, as are the tensor extension construction, injectivity from kernel triviality, and the inverse normalization.

Two holes were added:

- `AlgebraicGeometry.IsCurve.additive_cohomology_tensor_kernel`, node `lem-pbc-additive-cohomology-tensor-kernel`: the explicit normalized tensor map has zero kernel.
- `AlgebraicGeometry.IsCurve.additive_cohomology_tensor_surjective`, node `lem-pbc-additive-cohomology-tensor-surjective`: the explicit normalized tensor map is surjective.

This is a decomposition: one original hole closed and two strictly partial geometric obligations added (net -1), not a sorry-free proof of geometric base change. Neither new theorem supplies an equivalence or the other's conclusion. The original module contains no sorry; the new obligations are the entire remaining holes of this delivery.

Both statements were checked against the separated finite affine-cover proofs of Stacks [02KH](https://stacks.math.columbia.edu/tag/02KH) and [03P2](https://stacks.math.columbia.edu/tag/03P2). Tensor exactness separately proves kernel triviality and the existence of preimages. Empty schemes, affine curves, and zero-dimensional curves have zero first cohomology, so both obligations reduce to true assertions on zero groups. The arguments do not introduce properness, finite-dimensionality, smoothness, algebraic closure, or connectedness. The identity field extension reduces to the coefficient-sheaf isomorphism determined by the section formulas.

## No longer needed

No existing library import was removed, and no global module pruning is claimed. The target's direct proof dependencies are now just the two new nodes. The old direct dependencies `lem-sc-etale-tensor-unit-sections-natural` / `Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural` and `lem-sc-etale-qcoherent-source-comparison-natural` / `Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural` remain in the new obligations' plans, rather than being used directly by the target's algebraic reduction.

The old direct dependencies `lem-pc-cech-computes` / `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray` and `lem-sc-flat-base-change-coherent` / `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` are replaced at this level by the normalized affine Cech inverse-image and tensor cohomology comparison nodes. Those existing modules can still be reached by the library's public imports or other arguments. The old direct dependency `lem-weil-pbc-sheafH-ext-derived-comparison` / `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` is unnecessary for this argument, which stays in the specified `Sheaf.H` Ext model throughout.

The new dependencies `lem-pc-flat-cech-base-change`, `lem-pc-affine-cech-inverse-image`, and `lem-pc-flat-cech-cohomology-square` are existing tools within the retained finite affine-cover route. No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The recorded coherent flat-base-change theorem provides a nonempty linear equivalence without a pullback normalization in its signature. Likewise the source-comparison theorem supplies naturality for coefficient endomorphisms on a fixed scheme, not a cross-scheme base-change square for the two arbitrary section-presented sheaves. These cannot simply be composed to obtain the original normalized assertion. The remaining named kernel and surjectivity obligations expose that geometric comparison rather than treating the missing normalization as automatic.

The node's old separate Ext/derived comparison is unnecessary: the input and conclusion already use the same Ext-based `Sheaf.H`, and the direct scalar-compatibility proof uses its actual naturality lemmas. No mathematical counterexample to the original statement was found. Mathlib searches found generic tensor and group-cohomology tools, but no exact geometric base-change statement; LeanSearch returned an internal server error, recorded as unavailable.

## New nodes

`lem-pbc-additive-cohomology-tensor-kernel` is recorded in `dag/nodes/sec-proper-base-change/lem-pbc-additive-cohomology-tensor-kernel.json`, with module `lean/Sheaf/AlgebraicGeometry/Curve/AdditiveCohomologyTensorKernel.lean`. It states only kernel triviality of a supplied tensor-linear map with the canonical pure-tensor formula.

`lem-pbc-additive-cohomology-tensor-surjective` is recorded in `dag/nodes/sec-proper-base-change/lem-pbc-additive-cohomology-tensor-surjective.json`, with module `lean/Sheaf/AlgebraicGeometry/Curve/AdditiveCohomologyTensorSurjective.lean`. It states only existence of preimages under that map. Both nodes retain the original hypotheses, have complete source-based proof sketches and three recorded search kinds, and inherit the item's chapter and unit. No change record is required because existing interfaces are unchanged.

## Second reading by X2

1. **Interfaces unchanged — pass.** Compared all three delivered source files with
   the repository. The two tensor-obligation modules are new. The existing target's
   complete signature is now byte-for-byte identical, including whitespace; its
   docstring and two public imports are unchanged. No definition, target statement,
   downstream file, or declaration visibility changes. No change record is needed.

2. **Proof and axioms — pass as a decomposition.** Independently compiled all three
   modules in import order through lcompile.py, without errors or warnings. Scratch
   copies with #print axioms show only propext, Classical.choice and Quot.sound for
   the private scalar-compatibility theorem. The target and each tensor obligation
   additionally use sorryAx, exactly as expected from the two reported open theorems.
   The only literal sorries are the complete proofs of those named public obligations.
   No axiom, unsafe, opaque, implemented_by, extern, hollow definition, or arbitrary
   data witness from an unproved existence theorem occurs. Scalar maps are obtained
   from hypotheses inside a proof; the inverse is uniquely determined by the explicit
   tensor map and its bijectivity. This closes one original hole and adds two holes;
   it does not prove the original declaration without sorryAx.

3. **Split statements — pass.** Read both complete statements and their proof
   docstrings. Kernel triviality and surjectivity are separate, strictly partial
   obligations; neither restates or assumes the normalized equivalence. The section
   coordinates and naturality identify the actual additive structure sheaves, and
   hscalar/hscalar' fix the cohomology actions rather than assuming arbitrary ones.
   Checked the finite affine-cover and exact-tensor argument against Stacks
   [02KH](https://stacks.math.columbia.edu/tag/02KH) and the affine-acyclicity and
   Cech comparison of [03P2](https://stacks.math.columbia.edu/tag/03P2). Empty and
   affine curves reduce to zero H1; identity field extension reduces to the section
   coordinate isomorphism; disconnected covers, nonproper curves and arbitrary
   field extensions require no extra assumption. IsCurve supplies separatedness
   and quasi-compactness. Repeated leanfinder, loogle and grep searches with different
   terminology, and searched lean/ for canonical base-change and comparison results.
   No duplicate exact statement was found. The normalized comparison between the
   actual etale pullback and coherent cohomology remains geometric work in both
   obligations; fixed-scheme endomorphism naturality alone does not close it. Neither
   hole can be closed by the existing coherent equivalence in a few minutes.

4. **Route and pruning — pass.** Read the scalar-compatibility proof top downward:
   adjunction reduces the sheaf square to sections, the pullback square gives the
   scalar equation, and cohomology naturality gives linearity. The tensor lift and
   inverse normalization use existing Mathlib constructions directly. Both public
   imports supply types in signatures; both new ordinary imports are used only by
   the proof. No unused import is present and no module pruning is claimed. The
   No longer needed section now explicitly accounts for all five old direct
   proof dependencies. Read dag/units/sk-thm-p1.json, including realized: this item
   is below its realized curve-calculation steps, and the characteristic-p additive
   structure-sheaf route is retained. No unit statement or realized step is removed.

5. **DAG and Lean agree — pass.** The target's proof steps and proof_deps name
   exactly the two obligations used by the Lean reduction. Both new nodes have
   sources, three search kinds, full statements, union-of-uses proof_deps, origins,
   blueprint ancestry, chapter/unit, creation data and Lean records. Their pending
   proof plans match their docstrings. Corrected the new lean.statement records
   from flattened text to the verbatim multiline signatures, and recorded the
   second reader's searches in each new node. Existing node fields outside the
   permitted stage-3 proof fields are unchanged.

Second reading changed: restored one space in the existing signature, removed
extra blank lines, made both new node signatures verbatim, recorded independent
searches, and made the pruning report account explicitly for the two retained
lower-plan dependencies. The mathematical proof and split statements were retained.
