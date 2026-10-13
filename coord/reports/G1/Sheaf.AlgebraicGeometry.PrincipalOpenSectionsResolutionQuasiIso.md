## What changed

Closed the proof of `AlgebraicGeometry.principalOpenSections_resolution_quasiIso`
without changing its signature, docstring, or public imports. Completed the earlier
sandbox argument using the existing `qcoh_complex_alternating_cech_derived_sections`
canonical comparison equation. Restrict the given resolution, transport quasi-coherence
and K-injectivity to the open scheme, use its singleton affine cover, and cancel the
augmentation in the derived category to obtain the section quasi-isomorphism.

Added two modules, each with a new node:
`Sheaf.AlgebraicGeometry.SingletonCechAugmentationIso` is fully proved;
`Sheaf.AlgebraicGeometry.PrincipalOpenSectionsRestrictionComparison` states the remaining
scalar/restriction identification as a single named public theorem. The latter has no
quasi-coherence, K-injectivity, or resolution hypothesis, and compares the two explicitly
specified functors for any morphism of complexes. It is strictly the final identification
step, not a renamed copy of the resolution theorem.

The singleton proof constructs the inverse to evaluation at the unique degree-zero
tuple, proves every other column zero by cardinality or extension by zero, and constructs
a degreewise inverse to its total inclusion by `totalDesc`. The already-defined
augmentation is a cochain map, so componentwise isomorphisms suffice. No new construction
chooses data from an unproved existence theorem. The comparison witness beta is used only
inside a proposition proof.

Updated the parent's proof, proof_deps and proof_origin to follow the Lean argument.
No existing statement, definition, or module interface changed. No forced adaptations.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.principalOpenSections_resolution_quasiIso`
(node `lem-sc-principal-open-sections-resolution-quasi-iso`).

Added and fully proved:
`AlgebraicGeometry.singletonCechAugmentation_isIso`
(node `lem-sc-singleton-cech-augmentation-iso`).

One new hole remains, as the entire proof of a public theorem in its own module:
`AlgebraicGeometry.principalOpenSections_restriction_quasiIso_iff`
(node `lem-sc-principal-open-sections-restriction-comparison`).
There are no sorries in the item or the singleton module. This is a decomposition with
one existing hole closed and one new hole added, not an unconditional proof of the target
closure. The imported derived-section theorem and other existing dependencies retain
their own proof status.

The item and singleton module compiled without errors or warnings. The scalar comparison
statement also compiles. The final dry run compiles the whole delivery and runs the axiom
probe; its result is the handoff gate. Empty schemes/opens and zero complexes require no
special nonemptiness assumptions. Positive Cech columns vanish by injectivity cardinality;
negative columns vanish by extension by zero. No boundedness of F or J and no injective-term
hypothesis on J is introduced. The scalar comparison applies to arbitrary i, including
identity and zero maps, and the zero ring/empty basic open cases.

## No longer needed

No original public import was removed: `PrincipalOpenCechTotal` supplies the unchanged
statement's `affineOpenSections` definition. Removed the earlier sandbox's unused proof
import `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and unused
local composite R. Compilation passed without that import. The proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` is necessary:
removing it causes failure to synthesize K-injectivity after the module equivalence.

The following old direct proof dependencies are no longer used directly by this item:
`lem-weil-pbc-quasi-coherent-module-kernel`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, `lem-pc-affine-vanishing`,
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-hom-derived`,
`def-pc-ringed-spaces-derived-direct-image`.
Their modules are respectively `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`, Mathlib derived-category K-injective
modules, and `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`.
The imported derived-section theorem still encapsulates the relevant affine acyclicity and
resolution theory. This does not claim that those modules leave the entire target closure.
No library module is asserted globally pruned, and no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox held a compiling reduction but no nodes or report for its two new
statements. Its singleton hole has now been proved. The final identification remains a
separate statement, with a complete proof in words and node.

No false statement was found. The old plan explicitly repeated the affine acyclicity and
resolution-independence work already packaged in the existing Cech comparison theorem.
Its defining equation quantifies over every K-injective resolution, so it can be applied
to the given J without imposing quasi-coherence or injectivity of its terms. Naturality of
the explicit augmentation and isomorphism cancellation give the remaining glue in Lean.
The item is not a realized statement or step of `sk-thm-picard-duality`; this change stays
below that unit, retaining the Cech-derived-section route.

Read Stacks Tags 08C2, 08BS and 08D2 online, the entire item and its dependency signatures,
and the singleton total definitions. Repeated msearch LeanFinder, Loogle and grep searches:
only generic alternating-face-map/resolution results and scalar-restriction tools were
found. LeanSearch was unavailable (Internal Server Error), recorded without an absence
verdict. Local rg and blueprint searches found no existing statement of either new lemma.

## New nodes

`lem-sc-singleton-cech-augmentation-iso` in
`dag/nodes/sec-picard-framework/lem-sc-singleton-cech-augmentation-iso.json`
records the proved unconditional isomorphism of the actual singleton augmentation,
realized by `Sheaf.AlgebraicGeometry.SingletonCechAugmentationIso`.

`lem-sc-principal-open-sections-restriction-comparison` in
`dag/nodes/sec-picard-framework/lem-sc-principal-open-sections-restriction-comparison.json`
records the remaining arbitrary-complex section comparison, realized by
`Sheaf.AlgebraicGeometry.PrincipalOpenSectionsRestrictionComparison`. Its source is the
A-linear section interpretation of 08D2 and open restriction of 08BS; its proof expands
the natural identification and exact, conservative restriction of scalars. Each node has
three search kinds, complete proof steps, the inherited chapter/unit, and a blueprint path
through the parent. No change record is needed for these new modules or proof-only imports.

## Second reading by G1

1. I compared the delivered parent module with the repository version. The theorem
signature and docstring are byte-for-byte unchanged; the added imports are proof-only
and are all plain imports. The new modules publicly import only signature dependencies. The two new declarations have distinct
signatures and their nodes match the Lean declarations.

2. I compiled all three sandbox modules with `lcompile.py --all`. They compile without
errors or warnings. The parent target has no `sorry`; the only remaining `sorry` is the
named restriction-comparison theorem, whose node and docstring are present. No forbidden
`axiom`, `unsafe`, `opaque`, `extern`, or hollow definition was found.
The scratch-copy `#print axioms` probe showed only `propext`, `Classical.choice`, and
`Quot.sound` for the singleton theorem; the parent and restriction comparison additionally
use `sorryAx`, as expected from the explicitly reported open dependency.

3. The singleton augmentation theorem is a genuine componentwise isomorphism proof for
the singleton cover, including empty schemes and unbounded complexes. The restriction
comparison theorem is exactly the remaining scalar/restriction identification and is
strictly weaker than the parent target; it does not restate the resolution theorem.
Local searches found no duplicate declaration.
I independently searched scalar restriction with Loogle (`ModuleCat.restrictScalars`)
and singleton/section quasi-isomorphisms with `rg` in both library roots. Loogle confirms
the exactness adjunctions and reflection of isomorphisms, but supplies no identification
of the two scheme section functors. The local singleton tensor results concern a different
Čech construction and do not replace this explicit alternating augmentation.

4. The proof uses the existing canonical derived-section comparison and the explicit
singleton augmentation, avoiding the former direct acyclicity and resolution modules.
The report's removed proof dependencies are therefore complete, and the unit's Cech
derived-section route is retained.

5. The parent node's proof, proof dependencies, and proof origin agree with the proof;
the two new nodes contain their source, proof steps, searches, Lean records, and unit.
No target statement or definition changed.

I changed only this report section after the first reading: no Lean proof, statement,
node, or import required repair.
