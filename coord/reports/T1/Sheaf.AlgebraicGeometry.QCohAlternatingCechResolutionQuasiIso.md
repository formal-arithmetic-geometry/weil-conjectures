## What changed

Closed `AlgebraicGeometry.qcoh_alternatingCech_resolution_quasiIso` with an explicit
proof of the finite product and finite column argument. Its signature is unchanged.
Added proof-only imports of the upstream finite-column comparison, ModuleCat products
and the new affine-open section theorem.

The private proved helpers construct projection chain maps from each actual nonnegative
column to its section complexes, prove their product is an isomorphism, transport the
finite product quasi-isomorphism along these maps, and prove both column bounds.
The finite-column theorem then proves the actual total map is a quasi-isomorphism.

Added `Sheaf.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso`, containing a proved
additivity instance for the existing presheaf functor and one open affine-section theorem.
No object is chosen from an unproved existence statement and no definition contains a hole.

Read Stacks Cohomology 08C2 in full from the official stacks-project TeX, saved in the
sandbox scratchpad. Its unbounded proof uses all three acyclicity conditions and a
compatible truncation-resolution tower, with eventual constancy and Mittag-Leffler.
The new theorem records this argument. Tested the empty open, zero coefficient complex,
empty cover, singleton cover, and unbounded coefficient degrees mathematically; the
column-bound proof handles r=0 directly with the integer bound r-1=-1.

Both modules compile locally with lcompile.py; the delivery dry run is the final check.

## Proved and sorry left

Closed: `AlgebraicGeometry.qcoh_alternatingCech_resolution_quasiIso`
(node `lem-sc-qcoh-alternating-cech-resolution-quasi-iso`).

Added and still sorry: `AlgebraicGeometry.affineOpenSections_resolution_quasiIso`
(node `lem-sc-affine-open-sections-resolution-quasi-iso`). This is the single-open
component of the argument, without a covering or totalization. The parent proof performs
all finite products, projection compatibility, support bounds, and total comparison.
This delivery is a decomposition: one upper hole closed, one lower hole added; net zero.
The item itself has no remaining sorry, and all private helpers and the new additivity
instance are proved.

## No longer needed

No original imports removed: both existing public imports are needed by the signature.
Removed the tentative proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`: its declarations and instances
are already available through the required imports. The ModuleCat Products import is
necessary for the explicit degreewise `piIsoPi` isomorphism.

The parent's proof no longer needs `lem-pc-affine-qcoh-derived-equivalence`
(`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`) or
`lem-sc-qcoh-acyclic-derived-sections-comparison`
(`Sheaf.Paper.QCohAcyclicDerivedSectionsComparison`); neither is imported.
The affine-open comparison instead follows the singleton-affine case of 08C2 directly.
These modules may have other users; no claim is made that they leave the whole target closure.

The parent's direct dependencies on `lem-sc-derived-k-injective-restrict-open` and
`def-pc-ringed-spaces-derived-direct-image` move into the new affine-section node; they
are still needed there, so this is not pruning them from the full argument.
`lem-sc-integer-finite-column-total-comparison` remains used explicitly.
No realized statement or step of unit `sk-thm-picard-duality` is bypassed; its realized
statement and step lists are empty in the supplied unit record.

## Where the brief, the DAG or earlier work was wrong

The planned derived equivalence and cohomology comparison statements do not directly
supply invertibility of the actual ordinary section chain map. The new component theorem
records this missing interface, including canonical-map compatibility and all unbounded
acyclicity hypotheses. No existing statement or definition is changed.

`PrincipalOpenSectionsResolutionQuasiIso` looks reusable, but its proof reaches the parent
`QCohComplexAlternatingCechDerivedSections`, which reaches this item. The import-direction
tool confirmed that importing it would close a cycle; it was not used.

LeanSearch returned an internal server error, recorded as unavailable. Lean Finder,
Loogle and Mathlib source grep ran; none supplied the affine section comparison.

The kernel and cokernel-image nodes used by the new affine component are generic tools
filed in the proper-base-change unit; they establish the quasi-coherence hypotheses of
08C2 and do not change the Picard unit route.

## New nodes

`lem-sc-affine-open-sections-resolution-quasi-iso`, in
`dag/nodes/sec-picard-framework/`, states the actual section quasi-isomorphism on one
affine open, with the global-ring scalar action and arbitrary unbounded coefficients.
Its source is Cohomology 08C2, with restriction 08BS and affine vanishing 01XB.
Its Lean statement is in `Sheaf.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso`.
The docstring and node explain restriction, all three affine acyclicity conditions,
unbounded truncation comparison, compatibility with the given resolution, and scalar
restriction. No change record or forced adaptation is required.

## Second reading by T1

1. PASS: Compared the delivered parent module with the repository using diff.
   The existing theorem signature is byte for byte unchanged; only its proof,
   explanatory docstring, authors and three plain proof imports change. Neither
   existing public import nor any existing definition changes. The existing node
   changes only in proof, proof_deps and proof_origin. No change record is needed.
2. PASS: Independently compiled both modules with lcompile.py --all (4.4 and
   15.2 seconds, no errors or warnings). A scratch copy with #print axioms checked
   every private helper, both public theorems and the additivity instance. Only
   propext, Classical.choice and Quot.sound occur, with sorryAx additionally in
   the affine theorem, column quasi-isomorphism and parent. The one literal sorry
   is exactly the reported named affine theorem. No forbidden declaration or
   hollow definition occurs; the projection data is constructed explicitly.
   The scratch probe was removed before delivery.
3. PASS: Read the complete statement and proof of 08C2 in scratchpad/cohomology.tex
   (lemma-alternating-cech-complex-complex-ss). The affine basis verifies term,
   differential-cokernel and cohomology acyclicity; its singleton cover computes
   ordinary sections. Comparing resolutions by homotopy equivalence justifies
   arbitrary K-injective J. Scalar restriction preserves the underlying homology.
   Empty V gives zero complexes; a degree-zero F gives ordinary affine vanishing;
   unbounded F is covered by the truncation tower argument, not a bounded-below
   assertion. The new node matches the Lean statement and supplies its source
   and natural-language proof. This is strictly the single-open component: the
   parent additionally proves finite-product naturality and total comparison.
   Independent msearch queries used Lean Finder (taking sections over an affine
   open of a K-injective resolution), Loogle (CochainComplex and QuasiIso) and
   grep (IsQuasicoherent/IsAffineOpen with QuasiIso); no exact reusable theorem
   was found. Also searched lean/Sheaf and lean/WeilConjectures by sections,
   quasi-isomorphisms and affine opens. PrincipalOpenSectionsResolutionQuasiIso
   imports QCohComplexAlternatingCechDerivedSections, which uses this item, so
   its otherwise related theorem cannot shorten this proof without a cycle.
4. PASS: Read the projection maps, their degreewise product isomorphism, the
   homology product comparison, the naturality square and both support bounds.
   The parent uses the existing finite-column theorem directly. For r=0 its
   interval is empty (0 through -1); for r=1 only column zero remains. No bound
   on coefficient degrees is introduced. Imports have the required visibility
   and each added import supplies a declaration used in the proof. The report
   names all four removed old proof dependencies (including the two moved to
   the new node). The unit sk-thm-picard-duality has realized.statement = []
   and realized.steps = [[]]; no realized step or unit route is bypassed.
5. PASS: Compared both nodes against the Lean. Parent proof_deps is exactly the
   affine component and existing integer finite-column comparison; its proof
   describes the implemented reduction. New-node metadata, signature, source,
   searches, provenance, chapter and unit are present, and its proof_deps agree
   with its documented remaining argument. The original node's statement and
   statement dependencies are unchanged.

Second-reader changes: appended this independent review and its verification
results. No Lean or DAG repair was necessary. One upper hole is closed and one
strictly smaller lower hole is added: decomposition, net zero holes closed.
