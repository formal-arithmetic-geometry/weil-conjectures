## What changed

Returned-delivery repair: removed all nine duplicate helper implementations from
`ContinuousAffineEtaleLattice` and the seven duplicates from
`ContinuousLatticeFiniteCoproduct`. The four raw free-module facts are reused by
`import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`.
The five remaining transport facts and the exact `LocallyFree` abbreviation move
from the unclaimed `ContinuousLisseStratifiedLattices` module into the new proved
`ContinuousLocallyFreePullback` API. All three consumers import that API; its
lower imports avoid the cycle that importing the stratification theorem would
create. The old implementations are removed, so every helper has one owner.
The stratification theorem and its existing public imports remain unchanged.
A scan using the landing checker's declaration and statement parser across
14,118 modules found one further duplicate, `openUnitIsIso`; the coproduct
module now imports that existing private proof from
`Sheaf.Paper.CondensedOpenClosedRecollement` and removes its copy.

Change record: `coord/changes/B2-continuous-local-freeness-helper-sharing.md`.
It records the original and new helper declarations and all eight downstream
consumers. The independent reading retained from the returned delivery was
removed from this report because this repair requires a fresh second reading.

The statement of `AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_etale_lattice`
is unchanged. Its proof now chooses affine etale lattice neighborhoods, takes a finite
subcover using compactness of the noetherian base, and applies a proved finite-coproduct
assembly theorem. Etaleness, surjectivity, compactness and quasi-separatedness of the
resulting cover are proved in Lean, including the empty base.

Added five modules:

- `ContinuousCoefficientModuleEncoding`: actual coefficient and module equivalences;
  the identity-on-sections reconstructed ring comparison; equality of the given and
  spectral metrics and integral subrings; regular- and finite-free-module comparisons;
  the scalar-map square through the spectral identifications,
  and natural restriction-of-scalars comparisons for the reconstructed and the full
  continuous encodings. Every definition has a real body.
- `ContinuousModuleEncodingLattices`: the one remaining compatibility obligation for
  those specified encodings. It asserts local-freeness transport and transport of any
  already supplied lattice, with no assertion of lattice or neighborhood existence.
- `ContinuousAffineEtaleLattice`: a complete proof from the compatibility interface
  and the existing `exists_lisse_lattice_etale_local`. It extracts a covering member
  above a given point, applies the inverse integral encoding, and pulls back to an
  affine open. This neighborhood theorem works for any scheme; noetherianity is
  used only for the finite-subcover step in the item theorem. Local-freeness under
  pullback is proved using the actual raw `mapMod`
  predicate and a pulled-back scheme cover.
- `ContinuousLatticeFiniteCoproduct`: a complete assembly proof. Its integral module is
  the finite biproduct of the component extensions by zero. Empty intersections give
  zero off-diagonal restrictions; full faithfulness gives the diagonal restriction.
  The component free covers bind to a pro-etale free cover. Scalar extension commutes
  with the biproduct and open extension, and the counit to the rational target is an
  isomorphism by restriction conservativity. No compatibility between local lattices
  is assumed.

- `ContinuousLocallyFreePullback`: the five proved local-freeness transport
  lemmas and their identical scheme-cover predicate, moved from the stratification
  module and shared by all three consumers. It has no holes.

All seven modules compile individually in the prescribed 60-second limit and together
through `lcompile.py --all`. No public target or lattice statement changes.
The return repair moves
proved private helpers out of the unclaimed stratified-lattice module. It has
a change record and updates that module and its node in the same delivery.
No module held by another group is adapted.

Validation of the repair: `lcompile.py --all` compiled all seven modules without
errors or warnings, each within 60 seconds. The final delivery dry run repeats
the compilation and axiom checks after the import cleanup.
All seven node records have their verbatim Lean signatures and dependency unions
checked against the delivered sources. The unchanged source statement of
[Stacks Tag 03DO](https://stacks.math.columbia.edu/tag/03DO), including its proof
by pulling back a trivializing cover, was read for the moved API.

## Proved and sorry left

The return repair adds no holes and closes no additional holes. The shared
local-freeness API and the adapted stratification module have zero holes.
The existing compatibility split is retained unchanged; no new split is made.

Original holes: 1. Closed in the item module: 1, in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_etale_lattice`.
New holes: 1. Net hole reduction: 0. This is a decomposition, not a completed proof
free of new unproved inputs.

The only `sorry` in the seven delivered modules is
`AlgebraicGeometry.ProEtale.CondensedRing.continuousModuleEncoding_lattice_compatibility`,
node `lem-weil-pbc-continuous-module-encoding-lattices`.
It still needs the comparison on covering slices, conversion between sectionwise
finite local generators and the exact raw pro-etale free-cover predicate; the
extension-of-scalars comparison via its Hom adjunction; and the etale inverse-image
comparison. These are specified in its docstring and node with the relevant Stacks
sources. It assumes the sectionwise lattice is already supplied, so it does not
restate the original lattice-existence theorem. No geometric finite-cover or assembly
argument is left in this hole.

Proved new declarations include `continuousLisse_affine_etale_lattice` and
`continuousLattice_finite_coproduct`. The encoding module contains no holes, including
`reconstructedRingIso`, `sectionModuleComapIso`, `sectionModuleRegularIso`,
`continuousIntegers_eq`, `lisseFieldSheaf_eq`, `lisseIntegerSheaf_eq`,
`continuousRingRegularIso`, `continuousRingFreeIso`, `continuousFieldFreeIso` and
`continuousIntegerFreeIso`, `continuousRing_free_isFiniteLocallyFree` and
`continuousInteger_inverse_free`, and the canonical weakly-etale coefficient
comparison `AlgebraicGeometry.ProEtale.continuousChart_pullback`, and
`continuousRing_comap_compatibility` for the full continuous encodings, and
`lisseScalar_square` for the integral-to-field scalar map. The encoding data is
constructed by specified functors
and ring isomorphisms; it never chooses arbitrary data from an unproved existence
statement. The main proof still depends on the library's existing unproved inputs
through its imports; these are not counted as holes closed by this delivery.

## No longer needed

Pruned duplicate implementations: `free_comap`, `free_of_iso`,
`free_of_comap`, and `free_pullback_comp_iff` from both new lattice modules;
`locallyFree_of_iso` and `locallyFree_comap` from both; and `free_map`,
`locallyFree_map`, and `locallyFree_upperStar` from the affine module.
The five local-freeness transport implementations now occur only in the shared API, having been
removed from `ContinuousLisseStratifiedLattices` as well. All three duplicate
local `LocallyFree` abbreviations are replaced by that shared abbreviation.
The stratification module no longer imports all of the local-triviality module
directly; the shared API owns that proof dependency. Its public imports stay.
Its node likewise removes the direct proof dependencies
`def-weil-pbc-condensed-e-module-category` and
`lem-weil-pbc-condensed-lfp-local-triviality`; their free-module arguments are
now reached through `lem-weil-pbc-continuous-locally-free-pullback`.
Removed the affine module's direct `ProfinitePointPullback` import; its
pullback and scalar-change APIs are already in the public coefficient imports.
The shared API also omits that unused direct import. The coproduct module keeps
its direct import because it uses `profinitePointModuleForgetPullbackIso`.
The coproduct module's copied `openUnitIsIso` implementation is also removed;
its existing owner is reused through a proof-only `import all`.
These are duplicate-code removals; no entire module is globally pruned.

Removed these direct proof imports from the item module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.ContinuousCoefficientRealizations`

The last four interfaces remain used through the explicit encoding or affine
neighborhood proof, and some of these modules remain transitive imports. This is
not a claim that all six modules disappear from the target import closure.

The Mathlib leaf nodes `lem-weil-pbc-etale-morphism-open-map` and
`lem-weil-pbc-affine-morphism-permanence` remain used: their matched Mathlib
results prove openness and affineness of the finite coproduct. They are retained
in the main node's proof dependencies. The generic coefficient-realization and
module-equivalence dependencies are reused in lower nodes. No existing module
or mathematical proof branch is claimed globally pruned; the cleanup concerns
unnecessary direct imports and the location of the dependencies.

The original main node's following eight direct proof dependencies are no longer
used directly by the main proof (they are retained through statement dependencies
or the lower encoding/affine proof where needed):

- `def-pur-sheaf-tensor-product`
- `def-weil-pbc-condensed-e-module-category`
- `def-weil-pbc-continuous-integral-coefficients`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-l-adic-extension-absolute-value`
- `lem-weil-pbc-continuous-coefficient-realizations`
- `lem-weil-pbc-lisse-lattice-etale-local`

Removed redundant imports from the new modules after successful compilation:
`Mathlib.AlgebraicGeometry.Morphisms.Etale` from the coproduct module;
`Mathlib.AlgebraicGeometry.Limits` and the direct generic module-equivalence import
from the affine module; and `ProfinitePointPullback` and
`Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` from the encoding module.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied already-proved private helpers. Those copies were
mathematically correct but violated the single-owner rule. The repair imports
the existing lower helpers and moves the higher ones to an acyclic shared API,
adapting their original unclaimed consumer in the same delivery.

The generic internal-module/sectionwise-module equivalence and the sectionwise
etale-local lattice theorem are already proved and can be reused. Their
coefficient identifications, compatibility with the exact raw local-freeness
predicate, and pullback/scalar-extension comparisons are additional obligations;
merely invoking the generic equivalence does not discharge these. The existing
`continuousChart_scheme_naturality` was found in the shared library
and reused to prove the weakly-etale pullback coefficient comparison. The existing
`finiteLocallyFree_restrict` already handles coefficient-ring isomorphisms and is
identified in the remaining proof plan for reuse.

An initially explored stronger claim, that a lattice exists on an arbitrarily
specified affine etale cover, was discarded before delivery. The correct argument
chooses some etale lattice neighborhood at each point, then refines and selects a
finite subcover. No false or disputed statement from that exploration remains.

The blueprint-ancestor script could not follow the historical `created.item`
module names on this chain. The new node metadata follows the explicit existing
`blueprint.from` chain to `thm-weil-pbc-finite-extension`, recording its intermediate
nodes. The unit route itself is unchanged.

## New nodes

`def-weil-pbc-continuous-coefficient-module-encoding`: the specified actual
continuous coefficient module equivalences and their proved elementary comparisons;
module `Sheaf.Paper.ContinuousCoefficientModuleEncoding`, no holes.

`lem-weil-pbc-continuous-module-encoding-lattices`: local-freeness and supplied-lattice
compatibility of those encodings; module `Sheaf.Paper.ContinuousModuleEncodingLattices`,
one remaining hole, with the outstanding work described above.

`lem-weil-pbc-continuous-affine-etale-lattice`: affine lattice neighborhoods extracted
from the existing sectionwise lattice theorem through the encoding compatibility;
module `Sheaf.Paper.ContinuousAffineEtaleLattice`, no holes.

`lem-weil-pbc-continuous-lattice-finite-coproduct`: explicit finite-biproduct assembly
by open extensions by zero; module `Sheaf.Paper.ContinuousLatticeFiniteCoproduct`,
no holes. It permits arbitrary component maps and an empty family.

`lem-weil-pbc-continuous-locally-free-pullback`: the existing local-freeness
transport proofs relocated to `Sheaf.Paper.ContinuousLocallyFreePullback`;
zero holes. Change record: `coord/changes/B2-continuous-local-freeness-helper-sharing.md`.

## Second reading by B2

1. **Interfaces: pass.** Compared both existing modules against the shared repository.
   The complete signature of `continuousLisse_etale_lattice` is byte-for-byte
   unchanged. In `ContinuousLisseStratifiedLattices`, everything starting at
   `locallyFree_lfp`, including the public theorem and its proof, is byte-for-byte
   unchanged. The only other changes there are the replacement proof import and
   deletion of the private predicate and five helpers, relocated with identical
   types and bodies to `ContinuousLocallyFreePullback`. The change record declares
   their new public visibility and lists downstream users. No target definition
   changes. The five other modules are new.

2. **Proofs and axioms: pass with the declared hole.** Read all seven files and
   compiled them together through `lcompile.py --all`: no errors or warnings,
   each file under 60 seconds. Searched for forbidden declarations and every
   `sorry`: the sole hole is the named compatibility theorem listed above.
   A scratch module printed axioms for all 34 public declarations. The encoding
   constructions, coproduct assembly and shared transport API use only
   `propext`, `Classical.choice`, `Quot.sound`. The compatibility theorem, affine
   neighborhood theorem, main theorem and stratification theorem additionally
   use `sorryAx`, as reported. Definitions construct specified equivalences,
   inverse images and biproducts; none chooses arbitrary data from an unproved
   existence statement. Choosing an inverse of a proved isomorphism is legitimate.

3. **Remaining split: pass.** Read the entire signature, docstring and node of
   `continuousModuleEncoding_lattice_compatibility`. It transports a supplied
   lattice through the specified encodings; it never asserts lattice existence,
   a neighborhood or finite-cover assembly. It is strictly the encoding part of
   the argument, not a renamed item. The first clause supplies exactly the input
   to `exists_lisse_lattice_etale_local`; the second is applied to the lattice
   returned by that existing theorem. Read Bhatt--Scholze Definition 6.8.3,
   Proposition 6.8.4(6) and the first paragraph of Lemma 6.8.13 in `source.txt`;
   also read Stacks [03DM](https://stacks.math.columbia.edu/tag/03DM),
   [03DO](https://stacks.math.columbia.edu/tag/03DO),
   [03D7](https://stacks.math.columbia.edu/tag/03D7),
   [03EK](https://stacks.math.columbia.edu/tag/03EK) and
   [03EL](https://stacks.math.columbia.edu/tag/03EL).
   The free-module comparisons and identity-on-sections coefficient comparisons
   justify the stated transport proof; the remaining slice and adjunction
   arguments are substantial and cannot be closed by a short existing lemma.
   Independent semantic search returned `SheafOfModules.mapFree` and generator
   APIs, already used in the encoding, not the full comparison. Loogle rejected
   the project-only identifier; a separate grep search and searches across both
   library roots found no existing compatibility theorem. The existing
   `finiteLocallyFree_restrict` is already identified for the remaining work.
   Checked rank zero, variable finite ranks, empty schemes, and the identity
   etale arrow: the claim imposes no spurious positivity, constant-rank or
   nonemptiness condition.

4. **Route and pruning: pass.** The main proof starts with actual affine lattice
   neighborhoods, obtains a finite subcover using compactness, and constructs
   their disjoint union. In the assembly proof the integral object is explicitly
   the finite biproduct of open extensions by zero. Off-diagonal restrictions
   vanish on empty intersections; diagonal restrictions use the imported
   `openUnitIsIso`. Restriction conservativity verifies the rational counit,
   including the empty family. No descent datum is assumed. Read Stacks
   [04TR](https://stacks.math.columbia.edu/tag/04TR) for the gluing source.
   Existing free-module helpers are reused through proof-only `import all`;
   the five relocated transport lemmas now have one implementation. Reviewed
   imports: public imports supply types or definitions in public signatures;
   added proof imports are ordinary imports. Checked every removed direct
   `proof_deps` edge against the pruning section, and completed its two missing
   explicit names for the adapted stratification node. Read
   `dag/units/sk-thm-properbasechange.json`, including `realized`: its statement
   and three steps are unaffected; this reduction stays below the unit level.

5. **Nodes: pass.** Checked all seven node signatures against their actual Lean
   declarations and checked that each `proof_deps` is the union of its proof
   steps' `uses`. For the two existing nodes, only `proof`, `proof_deps` and
   `proof_origin` differ from the shared versions. New nodes have their source,
   proof, searches, creation record, blueprint ancestry, chapter, unit and Lean
   records. The compatibility hole has its matching node and complete proof in
   words. The proved encoding and coproduct modules provide actual reductions;
   no holed helper restates the main theorem.

Second-reader changes: completed the explicit pruning inventory in this report
and added this independent reading. No Lean proof or statement repair was needed;
no hole was added or closed by the second reading. The delivered result remains
one original hole closed and one strictly lower hole added, hence a decomposition
with net hole reduction zero.
