## What changed

Proved `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_derived_hom_descent`
in `Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent`, with its signature,
universes and visibility unchanged. Added a proved private helper
`perfect_stalk_isKProjective`, following the already checked argument in
`PerfectStalkQuasiIsoDetection`: stalks take each finite-free retraction to a
retraction of a projective module, and preserve the upper support bound.

The proved upstream `CochainComplex.IsKProjective.exists_Q_map_eq` gives a
chain representative of the input derived arrow. The existing
`exists_affine_perfect_open_stalk_chainMap_lift` supplies its affine neighborhood
and a natural chain comparison. Applying Q to that comparison and using the
naturality of the exact derived functor factorization proves the requested equation.
The original declaration docstring is retained; the node's proof records the actual,
shorter argument.

Added proof-only imports `Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift`,
`Sheaf.AlgebraicGeometry.OpenModuleStalkFreeProjective`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective`.
Public imports are unchanged.
The theorem's local heartbeat allowance is increased for comparison of nested
localized stalk and derived functors; the file still compiles in under 60 seconds.

The source argument was checked at https://stacks.math.columbia.edu/tag/09RE
(affine case (1), bounded-projective chain representatives) and
https://stacks.math.columbia.edu/tag/0BC7 (2). No unit statement or realized step
is bypassed: this node is below the theorem-of-cube unit, and that unit's realized
arrays are empty. `lem-sc-open-module-stalk-free-projective` is used as a tool from
the Picard-duality unit because it supplies exactly projectivity of the finite-free
open stalks; `lem-sc-bounded-above-projective-kprojective` is a Mathlib leaf.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_derived_hom_descent`
(node `lem-sc-perfect-open-stalk-derived-hom-descent`).
Added zero holes. No sorry remains in the delivered module. The private
`perfect_stalk_isKProjective` helper is proved, not split off.
This proves the item from existing library declarations; it does not assert that
all dependencies of those declarations are free of sorry.

## No longer needed

Removed all four old proof-only imports and their direct proof-dependency nodes:

- `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`:
  `lem-pc-affine-perfect-hom-colimit`.
- `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`:
  `lem-weil-pbc-localization-colimit-principal-localizations`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `lem-pc-affine-qcoh-derived-equivalence`.
- `Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso`:
  `lem-pc-open-restriction-stalk-extension-iso`.

The proof requires neither Hom injectivity, an arbitrary derived Hom diagram,
nor transport through an affine quasi-coherent derived equivalence. Neighborhood
comparison is supplied as part of the chain-map lifting theorem. This list records
pruning from this item's proof route, not a claim that these modules disappear
from every target's transitive import closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The original DAG route was
unnecessarily long for this strictly perfect setting: the existing chain-map
lifting theorem and K-projectivity suffice. Search used leanfinder for derived
stalk descent, loogle for IsKProjective, the supplied grep service for derived
stalk comparisons, and local rg over both library roots. The local searches found
the existing chain-map lift and the projectivity argument, avoiding new nodes.


## Second reading by J2

1. Interface: PASS. Compared the sole delivered module with the repository using
   diff and checked the existing theorem signature byte for byte. Universes,
   binders, conclusion and public visibility are unchanged; no definition or
   target statement changes, no forced adaptation and no change record.
2. Proof: PASS. The original delivery compiled cleanly in 17.3 seconds. A scratch
   copy with `#print axioms` showed only `propext`, `Classical.choice`, `Quot.sound`
   for the private helper, and these plus `sorryAx` for the main theorem through
   existing dependencies. No local sorry or forbidden trust escape occurs, and
   no data definition chooses an arbitrary witness from an unproved existence
   theorem. The main existential proof uses existing theorem witnesses locally.
3. Split statements: PASS; none added. The helper is a proved private theorem.
   Checked zero-rank retracts, zero complexes, arbitrary integer support bounds,
   and the vacuous empty-open case (excluded by x in U). Projectivity follows by
   functorial retraction; the upper support bound suffices for K-projectivity.
   Independent leanfinder, loogle and grep-service queries plus local rg found
   the proved upstream chain-representative lemma; no new geometric lemma is
   needed. Loogle returned a query parse error; the successful leanfinder search
   and local source inspection supplied the relevant results.
4. Route and pruning: PASS after repair. All four old proof dependencies absent
   from the new proof are listed under No longer needed. Each retained or added
   import supplies the signature or an actually used declaration. Read
   `dag/units/sk-prop-av-cube.json`: its statement realization and sole step
   realization are empty; this subordinate node changes no unit-level route.
   The chain-map lifting theorem has the exact comparison equation needed,
   and derived-factorization naturality gives the final equation in the correct
   diagrammatic order. No shorter geometric route was found.
5. DAG: PASS after repair. Only proof, proof_deps and proof_origin differ from
   the repository node; statement and lean record stay unchanged. Proof-step
   dependencies have union exactly proof_deps and existing matching declarations
   or a Mathlib match. No new node is required.

Changed: replaced the duplicated localization/quotient chain-representative
argument with one application of the proved upstream
`CochainComplex.IsKProjective.exists_Q_map_eq`, replaced its proof-only Mathlib
import with the upstream module import, and updated DAG step 2 and this report.
The original theorem docstring is retained as an alternative source argument;
the DAG and What changed describe the implemented route. One hole closed, zero
holes added; no split statements. Final compile, axiom and delivery checks are
recorded below.

Final local scratch compile: clean, 15.6 seconds; the main theorem and private
helper axiom lists are unchanged after the shortcut. Final signature, DAG
field/dependency-union, dependency-declaration and line-width checks pass.
