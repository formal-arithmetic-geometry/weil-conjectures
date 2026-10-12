## What changed

Replaced the direct sorry in `AlgebraicGeometry.Etale.etale_affine_qcoherent_succ`
with a compiling proof combining the existing lifted-coefficient affine vanishing theorem,
the existing Ext/right-derived terminal-evaluation comparison, and a new resolution-lift
lemma. The arbitrary-positive-degree wrapper `etale_affine_qcoherent` is unchanged.
The existing public imports, definitions, theorem signatures, universes and docstrings
are unchanged. A local transparency option permits the standard short-complex homology
comparison to elaborate.

The proof chooses the identity étale object T and an injective resolution R of the original
sheaf. It obtains a resolution S of the lifted sheaf, converts lifted vanishing to zero
homology of evaluated S, and transports this through the evaluation-complex isomorphism and
`ShortComplex.mapHomologyIso` for ULift. Injectivity of ULift.up reflects subsingletonness.
The comparison for R then gives the original Ext-defined Sheaf.H group. Thus the assembly
is real Lean, rather than a renamed copy of the original vanishing assertion.

Added `Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution`, with one public theorem and
one named whole-proof sorry. This statement concerns arbitrary abelian étale sheaves and
arbitrary injective resolutions on any scheme. It assumes neither affineness nor
quasi-coherence and asserts a resolution with compatible evaluation complexes, without
asserting any cohomology vanishing. Its proof is documented from Stacks 01DO, using the
small affine étale model and shrinking subsheaves of free representables before applying
the injectivity test. Kernels and local surjectivity give exactness of lift.

The existing unit `sk-prop-h2` has no realized node requiring a particular subroute here.
The affine basis, disjoint-union comparison, and faithfully flat Amitsur route are retained
through the existing lifted-coefficient affine theorem.

Validation: both sandbox modules compile together in import order with lcompile.py,
without warnings. No lake invocation or repository edit was made by hand. The new lemma's
edge cases were checked mathematically: arbitrary X, empty X, zero sheaf, and a trivial
resolution are included; there is no section-vanishing hypothesis to conceal the conclusion.

## Proved and sorry left

`AlgebraicGeometry.Etale.etale_affine_qcoherent_succ`
(node `lem-sc-etale-affine-qcoherent-succ`): removed its one direct sorry, conditional on the
existing named lifted-coefficient vanishing theorem and the new resolution-lift theorem.
`AlgebraicGeometry.Etale.etale_affine_qcoherent` remains the already-proved degree wrapper.
The item's module has no direct sorry.

This delivery is a decomposition: one direct hole closed and one new lower hole added,
for net zero holes from these edits. Neither theorem is asserted to be axiom-free.

One new sorry remains:
`AlgebraicGeometry.Scheme.exists_etale_ulift_injectiveResolution`
(node `lem-sc-etale-ulift-injective-resolution`, module
`Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution`). Its entire proof is `by sorry`.
The existing unresolved Čech/Amitsur statement
`AlgebraicGeometry.Scheme.isZero_etaleTensorSectionsSheaf_ulift_cech`
(node `new-etale-affine-tensor-cech-vanishing`) remains a transitive dependency of the
lifted-coefficient theorem; it was not changed or restated in this delivery.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion`
- `Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.EtaleStandardCoverCech`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.RingTheory.FaithfullyFlat.Amitsur`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

The first two and the affine-sections, tensor-pullback, standard-cover, tilde and Amitsur
modules remain needed transitively through the lifted-coefficient theorem or the unchanged
public tensor-section-sheaf import. Their mathematical nodes are not claimed to be globally
pruned. The item now uses only three direct proof imports: the lifted affine theorem,
the new resolution-lift theorem, and the Ext/terminal-evaluation comparison.

The old node's separate route through `prop-weil-pbc-kinjective-resolutions-exist`,
`def-weil-pbc-etale-cohomology`, and `def-weil-pbc-global-sections-functor` is unnecessary
for this proof. Ordinary injective resolutions, right-derived evaluation, and the proved
Ext comparison suffice; no K-injective comparison with unbounded derived global sections
is used. The other former proof dependencies are retained underneath the lifted affine
node, rather than being separately reapplied here.

Every old direct `proof_deps` edge removed from the successor node is listed here
(the retained lifted theorem supplies the Čech/Amitsur route transitively; removal
of a direct edge is not a claim of global pruning):

- `lem-weil-pbc-cech-vanishing-criterion`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-etale-covering-affine-refinement`
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-sc-etale-qcoherent-descent`
- `def-weil-pbc-etale-site`
- `lem-sc-etale-standard-cover-cech`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-pc-module-pullback-identity-composition`
- `def-sc-etale-qcoherent-module`
- `lem-pc-cech-exact`
- `def-weil-pbc-global-sections-functor`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `def-weil-pbc-etale-cohomology`

## Where the brief, the DAG or earlier work was wrong

The old node plan did not supply the bridge between the small coefficients of this theorem
and the larger coefficients of `isZero_rightDerived_etale_of_cech_vanishing`. The existing
lifted-affine theorem already supplies the Čech argument in the correct larger universe.
The new lemma isolates the missing resolution bridge without changing the original
statement or duplicating the quasi-coherent vanishing assertion.

The existing `Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift` theorem is not usable:
its DAG proof depends on the present small-coefficient affine theorem, and import_direction.py
confirms that importing it here creates a cycle. That theorem also assumes quasi-compactness,
separatedness and quasi-coherence, whereas the new resolution lemma has none of these
hypotheses. No existing declaration or definition was corrected.

Searches: Lean Finder returned cohomology definitions and the sheaf condition for lifted
presheaves, not an injective-resolution transport theorem. Loogle's query
`"Injective", "sheafCompose"` returned no matches. Mathlib grep found only injective
functions involving ULift, not preservation of injective sheaf objects. LeanSearch was
attempted and returned an Internal Server Error; this is recorded as unavailable, without
a mathematical verdict. The blueprint search `injective universe` returned no matches.

## New nodes

`lem-sc-etale-ulift-injective-resolution`:
`dag/nodes/sec-curve-estimates/lem-sc-etale-ulift-injective-resolution.json`, realized by
`Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution`. It is the coefficient-universe
resolution part of Step 3, with the complete injectivity, exactness, and evaluation argument
in its docstring and node. Source: Stacks Project, Injectives, Lemma 19.7.3 (Tag 01DO),
https://stacks.math.columbia.edu/tag/01DO, plus Mathlib's small affine-site equivalence and
ULift preservation of limits and colimits. The item's node proof and direct proof_deps
now follow the Lean assembly. No change record is needed: existing interfaces are unchanged.

## Second reading by H1

1. PASS. Compared the complete item module with the repository version using diff.
   Both existing theorem signatures, universes, docstrings, and public imports are
   byte-for-byte unchanged; the positive-degree wrapper is unchanged. No definition
   was changed, and no change record is required. The new module has no prior interface.
2. PASS. Compiled both modules in import order with lcompile.py without warnings or
   errors. The item has no direct sorry; the new module has exactly its one named
   whole-proof sorry. Scanned for axiom, unsafe, opaque, implemented_by, extern and
   hollow definitions. Printed axioms of both item declarations and the new theorem:
   only propext, Classical.choice, Quot.sound and the expected sorryAx occur.
3. PASS as a decomposition. Read Stacks 01DO and checked the extension criterion.
   The affine étale site is essentially u-small, so use its u-small skeleton before
   the small free-representable argument. Subobjects of those generators shrink,
   their maps descend by full faithfulness, and injectivity in the small category
   supplies the extensions. Lift is exact by the local surjectivity criterion.
   Empty X, zero F, injective F with a degree-zero resolution, and arbitrary
   non-affine X cause no extra hypotheses or false vanishing assertion. This is
   the resolution-transport part of the proof, not a restatement of affine
   acyclicity. Additional Loogle and Lean Finder searches and rg in Mathlib,
   upstream and Sheaf found only module-object lift preservation, generic
   adjunction results, and Grothendieck-category facts, not this sheaf theorem.
   The existing quasi-coherent lift theorem depends on this item and cannot be
   imported here. No short proof of the sheaf injectivity bridge was found.
4. PASS. Read the lifted affine theorem and the proved terminal-evaluation
   comparison, then checked the displayed homology isomorphisms and their
   orientations. Every new import supplies a type or a proof ingredient. The
   new module's public imports are required for its public statement and its
   instances. The removed direct DAG edges are now exhaustively listed above;
   none is claimed globally pruned without a closure calculation. The unit
   sk-prop-h2 has empty realized entries, and the affine basis/Amitsur route is
   retained transitively through the lifted affine theorem.
5. PASS. Checked both JSON nodes, the exact new Lean signature, source, searches,
   creation/blueprint fields, and union of proof-step uses against proof_deps.
   The successor node names the actual three assembly ingredients; the new node
   documents the resolution lift and its source.

Changed only the new lemma's natural-language proof and node to explicitly pass
from the essentially small affine site to its small skeleton; recorded the
independent searches; made the zero-net decomposition accounting explicit; and
completed the removed direct DAG-dependency list. No Lean proof or signature
needed repair.
