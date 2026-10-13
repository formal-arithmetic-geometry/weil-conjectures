## What changed

The original signature and docstring are unchanged. The proof chooses local isomorphisms,
aligns them by source automorphisms, and evaluates the inverse-hom identity to produce
preimages on every smaller open. Two new modules isolate existence and alignment. The local-isomorphism theorem is
proved from the existing self-Ext pullback frame, affine conormal frame, conormal
basis, and exterior local-free comparison; only alignment remains unproved.

## Proved and sorry left

Closed `AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_comparison`
(1 of 1 original holes), with one new hole split off:

- `AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_alignment`
  (`new-w4-koszul-self-ext-local-alignment`).

Also proved the new intermediate declaration
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_iso`
(`new-w4-koszul-self-ext-local-iso`) from existing chart frame theorems. Its module
contains no sorry. The private frame restriction helper is an explicit composite
of existing isomorphisms and contains no sorry. Section surjectivity in the parent
is proved by evaluating the inverse-hom identity. This is a decomposition with no
net change in holes; the remaining hole is only overlap alignment, not affine
existence or section surjectivity. No other sorry is added.

## No longer needed

Removed direct proof imports from the parent:

- `Sheaf.RingTheory.KoszulProjectiveResolution`.
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`.
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`.
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`.
- `Sheaf.AlgebraicGeometry.AffineConormalFrame`.
- `Sheaf.RingTheory.KoszulConormalBasis`.
- `Sheaf.RingTheory.KoszulGeneratorChainMap`.

These dependencies remain in the intermediate modules' plans; none is pruned from
the transitive closure. The parent uses only its two new proof imports.

The old parent proof dependencies replaced by the two new dependencies are
`new-j3-koszul-projective-resolution`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-derived-hom-finite-free-model`, `lem-sc-affine-conormal-frame`,
`lem-sc-koszul-conormal-basis`, and `new-q2-koszul-generator-chain-map`.
They remain transitively imported by the alignment module; no module is pruned.

## Where the brief, the DAG or earlier work was wrong

No existing statement is changed or disputed. The all-degree generator comparison
and homotopy independence remain in the alignment problem: the existing generator
chain-map declaration specifies only its top-degree component. Local isomorphisms
alone do not give compatibility. Arbitrary compatible morphisms need not be surjective
(zero maps are a counterexample); this delivery aligns genuine isomorphisms instead.
The normalized Koszul comparisons supply the alignment, via the stated generator
and localization argument. Empty V, degree zero, and degrees above chart length are
covered. The unit route is unchanged.

## New nodes

`new-w4-koszul-self-ext-local-iso`: pointwise local isomorphism existence only,
without compatibility, proved from existing frames in
`Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore`.

`new-w4-koszul-self-ext-local-alignment`: compatibility adjustment for already supplied
isomorphisms, with no cover or local-map existence, in
`Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalAlignment`.
Both retain the original source and unit. No interface change or change record.

Validation: local compilation of the frame construction and combining proof passed.


## Second reading by W4

1. Compared the parent file with the repository by diff. Only private proof imports
   and the theorem proof change; the existing signature, public imports, and
   docstring are byte-for-byte unchanged. There are no interface changes or forced
   adaptations. The two new theorem signatures agree with their node lean records.
2. Compiled all three modules locally and checked the three public declarations with
   `#print axioms` in a scratch module. Only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` occur. The parent and core contain no sorry; alignment
   contains exactly its reported named theorem hole. There are no forbidden
   declarations or hollow definitions. `restrictLocalFrame` explicitly composes
   restriction isomorphisms. Existential choices of frames and isomorphisms occur
   inside theorem proofs only, not as definitions of unspecified data.
3. Read the local-frame, affine-conormal-frame, conormal-basis, and exterior-frame
   interfaces. The core composes frames with exactly the same subset index and
   restricts them along V. The alignment hypothesis supplies the isomorphisms and
   cover: its remaining obligation is compatibility, not their existence or section
   surjectivity. Read Stacks Tags 0BQY (zero-differential Hom calculation) and 062I
   (conormal basis); checked empty V, m=0, n=0, n>m, and empty overlaps. Alignment
   needs the normalized comparison, not arbitrary local isomorphisms alone. Its
   source automorphism is c_z followed by e_z.inv. Repeated LeanFinder, Loogle,
   and grep searches with descent/change-of-sequence terminology; no usable exact
   match was found. Project exterior/dual-exterior/global-surjection statements
   depend on this parent and would be circular. The generator chain map's public
   statement controls only the top-degree component, so it cannot close the
   all-degree overlap calculation in a few lines.
4. The parent genuinely uses local existence proved from existing frames, then
   alignment, then inverse evaluation for section surjectivity. No shorter
   independent library route was found. All proof-dependency imports remain
   necessary for the outstanding alignment plan. Listed all seven replaced parent
   node dependencies explicitly; they remain in the transitive closure. The unit
   `sk-thm-picard-duality` has empty realized statement/step lists, unchanged;
   this below-unit decomposition bypasses no realized unit node. One original hole
   closed and one new hole added is a decomposition with net zero holes, not a
   fully proved result.
5. Compared node changes: the existing node changes only `proof`, `proof_deps`,
   and `proof_origin`; its two uses match the Lean combining proof. The core node
   cites exactly the four frame/basis dependencies used. The alignment node carries
   the remaining source argument and its dependency imports. Both new nodes have
   source, docstring proof, creation metadata, unit/chapter, searches, and verbatim
   Lean signatures. Verdict: delivery is a valid decomposition.

Second-reading changes: clarified the new alignment docstring and node proof with
local equal-rank refinement and the explicit automorphism formula, and completed
reporting of the replaced parent DAG dependencies. Existing Lean proofs were kept.
