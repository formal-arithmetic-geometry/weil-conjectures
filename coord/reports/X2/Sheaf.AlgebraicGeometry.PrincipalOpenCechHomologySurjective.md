## What changed

Completed the proof body of `AlgebraicGeometry.principalOpenCech_homology_surjective`
in `Sheaf.AlgebraicGeometry.PrincipalOpenCechHomologySurjective`, without changing
its signature, universes, visibility, or public imports. The proof restricts the
coefficient complex to the open union, proves that the induced principal opens cover
it, applies the existing K-injective alternating augmentation theorem, and transports
its quasi-isomorphism through an arrow isomorphism after forgetting scalar actions.
Exact forgetful functors reflect the result back to A-modules, where its homology
maps are isomorphisms and therefore epimorphisms.

Added the proof imports `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetComparison`,
`Sheaf.AlgebraicGeometry.KInjectiveAlternatingCechAugmentationQuasiIso`,
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
The last import supplies preservation of K-injectivity through the module equivalence.
Updated the parent node's proof, proof dependencies, and proof origin to this route.

Added a module containing one structural comparison theorem. It has no K-injectivity
hypothesis and asserts a chain-level arrow isomorphism, not a homology property.
The restricted complex, open family, and both forgetful functors are explicitly
specified. No arbitrary witness is used to define data. The comparison requires
reindexing the finite tuple total by subset cardinality, transporting section modules
along intersection equalities, and verifying differentials and augmentation.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.principalOpenCech_homology_surjective`
(node `lem-sc-principal-open-cech-homology-surjective`). Its full proof compiles.
The item's module now contains no direct sorry.

Added one hole:
`AlgebraicGeometry.principalOpenCech_subset_comparison`
(node `lem-sc-principal-open-cech-subset-comparison`, module
`Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetComparison`). Its entire proof is
`:= by sorry`; its docstring and node give the complete coordinate argument.
This is a decomposition: one upper hole closed and one structural hole added,
with zero net direct holes removed. The comparison is strictly separate from the
cohomological argument: it applies even to non-K-injective complexes and makes
no assertion of surjectivity or quasi-isomorphism.

Validation: both delivered modules compile through `lcompile.py --all`.
The empty cover, a singleton cover, repeated principal opens, empty intersections,
and arbitrary unbounded coefficients were checked against the comparison argument.
For the empty cover both products are empty, the tuple total is zero, and sections
on the empty union are zero. A singleton is exactly restriction to that principal
open. Indexing retains repeated indices, so repetition does not alter the bijection.

## No longer needed

No existing imports were removed from the item's module, and no module is claimed
pruned from the targets' import closure.

The parent's direct proof edges to `prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-sc-alternating-cech-total-homotopy`,
`lem-weil-pbc-module-injective-open-cover-cech-acyclic`, and
`lem-pc-alternating-cech-computes` are replaced by the existing tuple augmentation
and open restriction results plus the structural comparison. The existing tuple
augmentation supplies the resolution, exact-row and staircase argument; its
transitive dependencies remain needed where that proof uses them. No duplicate
subset-coordinate resolution or staircase theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

The planned argument is mathematically sound. The reusable tuple-model K-injective
augmentation theorem already proves its cohomological steps. It requires a cover
of the entire scheme; the principal family in this item covers only its union.
The proof therefore applies it on the open subscheme of that union, rather than
adding the false hypothesis that the principal opens cover Spec A.
The remaining gap is the explicit subset-to-tuple chain comparison on that scheme.
The unit's realized statement and steps are untouched.

The local clone does not contain `literature/stacks-project/cohomology.tex`.
The relevant source was read at https://stacks.math.columbia.edu/tag/08C1;
the coordinate verification of the omitted compatibilities is marked as agent-written.
LeanSearch returned an unavailable-service error, recorded without a mathematical
verdict. LeanFinder and source grep found no existing comparison theorem.

## New nodes

`lem-sc-principal-open-cech-subset-comparison` records
`AlgebraicGeometry.principalOpenCech_subset_comparison` in
`lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechSubsetComparison.lean`.
It identifies the given section-to-subset-total arrow with the actual increasing-tuple
augmentation on the open union after forgetting scalar actions. Its statement has
no K-injectivity assumption; its proof follows section restriction, finite coordinate
regrouping, matching deletion signs and augmentation components. It inherits the
parent's chapter, unit, and blueprint ancestry. Three kinds of Mathlib search are
recorded from `msearch.py`, including the unavailable LeanSearch result.
No existing statement or definition was changed, so no change record or forced
adaptation is needed.

## Second reading by X2

1. **Interfaces: pass.** Compared the entire delivered parent module with the
   repository by `diff -u` and by `stage3_delivery.diff_module`: no existing
   statement changed, no declaration was added to the parent, and its public
   imports are identical. The changes are the proof, its explanatory docstring,
   and four plain proof imports. The comparison module is new. There are no
   changes to existing definitions, target signatures, or other modules, and no
   change record is required.

2. **Proof and axioms: pass as a decomposition.** Independently compiled both
   modules with `lcompile.py --all` (14.0 and 55.7 seconds, exit 0). Scratch copies
   with `#print axioms` for both declarations compiled and printed precisely
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only direct hole
   is the named comparison theorem, exactly `:= by sorry`. There are no axioms,
   unsafe/opaque declarations, implementation overrides, or holed definitions.
   Read the open-restriction theorem, the equivalence-preservation instance in
   `RightDerivedFunctor.Comp`, and the finite-cover augmentation theorem: each
   is applied with its required hypotheses. In particular `hU` proves a cover
   of V.toScheme, without imposing a cover of Spec A. The local quasi-isomorphism
   hypotheses feed the forgetful-functor preservation and reflection instances;
   arrow transport then proves that the actual displayed alpha is a quasi-isomorphism.

3. **Split comparison: pass.** Read the tuple differential, extension to integer
   degrees, flipped double complex, totalization, and augmentation definitions
   in `AlternatingCechTotalComplex`. Range and increasing enumeration identify
   tuples of length p+1 with subsets of cardinality p+1. For each S the coefficient
   degree is q=n+1-card S, and deleting its k-th element has exponent k, exactly
   card {i in S | i<j}. Both scalar signs become integer multiplication after
   forgetting, so changing global scalar rings introduces no discrepancy.
   Restriction to V identifies the underlying section groups and their maps;
   the finite nonzero columns make the diagonal coproduct a finite product.
   The assumed sigma, tau, and augmentation equations therefore give the two
   chain isomorphisms and their commuting square. Off-successor differentials
   vanish by the cochain shape. Checked r=0, r=1, two indices (the horizontal
   term is restriction from index 1 minus restriction from index 0), repeated
   opens, zero principal opens, the zero ring, and arbitrary unbounded J.
   The comparison is true without K-injectivity and contains no cohomology
   assertion: it is a strictly structural part of the original argument, not
   its conclusion under another name. Its docstring supplies both directions
   and differential/augmentation compatibility. Repeated searches used Loogle
   `Finset.orderIsoOfFin` (the increasing enumeration primitive), LeanFinder
   "Reindexing a finite Cech complex by nonempty subsets instead of strictly
   increasing tuples preserves its differential and augmentation" (no matching
   comparison), and source `rg` with subset/Cech and overEquiv terms across
   lean/, upstream, and Mathlib. Existing PrincipalCechTotalRegrouping and
   PrincipalCechRegroupDifferential regroup the subset model, not this tuple
   model on V; they do not close the remaining comparison. Its proof is not a
   few-minute closure. Read Stacks 08C1, 01FM, and 08BS online; the new coordinate
   argument is correctly marked agent-written, not claimed to be their verbatim
   statement.

4. **Route and pruning: pass.** The parent's three proof edges are exactly open
   restriction, finite-cover tuple augmentation, and the subset comparison.
   All five replaced direct edges from the old proof_deps appear under
   "No longer needed"; their use inside the existing augmentation remains
   transitive. The unit sk-thm-picard-duality and its realized fields are untouched;
   no unit statement or step is bypassed. The added parent imports are plain
   because they serve only this proof. Removed the redundant direct public
   import of DerivedHomMayerVietoris from the new comparison module: it is
   already public through AlternatingCechTotalComplex's RingedSpaceDerivedDirectImage.
   The remaining new-module imports serve its signature. No existing module is
   pruned from the target closure by this removal.

5. **DAG: pass after correction.** The parent node changes only proof,
   proof_deps, and proof_origin; its statement and Lean record agree with the
   unchanged theorem. The new node has source, ancestry, chapter/unit, matching
   verbatim Lean statement, creation record, searches, and the full coordinate
   argument. Corrected its three `elementary` flags to false: the restriction
   section comparison, finite regrouping, and differential/augmentation
   verification are the substantive remaining proof, rather than already
   established elementary steps. Their dependency remains the explicit tuple
   construction, whose definitions are what the argument expands.

Second reading changed only the redundant import in the new module, the new
node's elementary flags, and this report. One original hole is closed by a real
reduction, one structural hole is added, and the net direct-hole improvement is
zero. This remains a decomposition; no fully sorry-free target is claimed.
