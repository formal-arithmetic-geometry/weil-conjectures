## What changed

Proved the complete formal evaluation/biduality argument in Sheaf.Paper.DualityPairing:
parametrized tensor-Hom adjunction, normalized inverse-braiding evaluation, its transpose
as the unit of a contravariant self-adjunction, both naturality clauses, all integral shift
identities, and all three squares of each distinguished triangle. Both ambient site clauses
use this same argument. Private NormalizedDualityPairing only factors the proof goal;
every existing public definition, statement, universe and public import stays unchanged.
The earlier standalone etaleKoszulSymmetry proof is retained verbatim.

Also filled the existing etaleTensorRaw hole in Sheaf.Paper.DualityPairingHelpers by proving
the identity abstractly before specializing. Added one strictly separate source lemma,
NativeInternalHomExact, for coherent contravariant exactness of derived Hom. Unlike the
item, it constructs no evaluation, bidual map, triangle morphism or geometric object.

The concrete proof passes the localization's recorded instances to the abstract theorem.
This prevents the kernel from unfolding the large concrete derived closed structure.
The two-site pairing module compiled in 44.3 seconds with the original public definitions
and the completely proved transport from native Hom to a parametrized right adjoint.
The new exactness statement and raw-tensor helper also compile separately. A complete
sandbox compile passes. An axiom probe confirms etaleTensorRaw uses only propext,
Classical.choice and Quot.sound; ambient_duality_pairing still depends on sorryAx through
the new exactness theorem, as recorded below.

## Proved and sorry left

- Closed AlgebraicGeometry.Etale.etaleTensorRaw with a complete proof, adding no hole.
- Replaced the item's sole baseline hole,
  AlgebraicGeometry.Etale.ambient_duality_pairing, by a complete proof from the exactness
  lemma below. This is a decomposition, not an independent proof of derived Hom exactness.
- Added one hole: DerivedCategory.nativeInternalHom_contravariant_exact, node
  lem-weil-native-internal-hom-contravariant-exact. It is the entire proof of its named
  public theorem, with source and proof in words in its docstring and node.
- No sorry remains in DualityPairing or DualityPairingHelpers. No definition has a hole.
  Net packet holes: two existing closed, one added; one genuine net closure, plus pruning.
  The baseline standalone symmetry was already proved by F4 before this packet was copied;
  it is not counted as an S1 closure.

## No longer needed

The proof reuses the existing native closed tensor structure rather than reconstructing
its adjunction through a different ringed-module encoding. Removed these private imports:

- import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
- import WeilConjectures.Algebra.Homology.RhomGlobalSections
- import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
- import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- import WeilConjectures.Algebra.Homology.HomComplex
- import Mathlib.Algebra.Homology.BifunctorShift
- import Mathlib.Algebra.Homology.DerivedCategory.Basic
- import Sheaf.Algebra.Homology.KInjectiveHomComplex
- import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
- import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
- import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
- import Mathlib.Algebra.Category.ModuleCat.AB
- import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
- import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
- import WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy
- import WeilConjectures.Algebra.Homology.HomTensorTotal
- import Sheaf.Algebra.Homology.SignedDoubleHomCone
- import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- import WeilConjectures.AlgebraicGeometry.DerivedCategories
- import WeilConjectures.Compactification.Defs
- import WeilConjectures.Compactification.Noetherian
- import Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses

The following entries are removed from the main node's direct proof dependencies.
This does not assert that they vanish from its statement or transitive dependencies:
def-weil-abstract-derived-category is still a dependency of the new exactness node,
and def-pur-derived-internal-hom remains a statement dependency.

- lem-pc-kflat-resolution
- prop-pur-kinjective-resolutions-exist
- def-pur-derived-internal-hom
- lem-pur-hom-kflat-into-kinjective
- lem-weil-pbc-site-derived-tensor-descent
- lem-weil-pbc-kinjective-hom-derived
- lem-sc-derived-hom-tensor-total
- def-pur-hom-complex
- lem-pur-hom-complex-global-homotopy
- def-pc-tensor-complex-sheaves
- lem-pur-rhom-well-defined
- lem-sf-double-hom-cone-comparison
- def-weil-abstract-derived-category
- lem-weil-pbc-commshift-nattrans-triangle-morphism
- sk-thm-nagata-sketch-noetherian
- def-nagata-compactification
- lem-weil-pbc-finite-type-over-noetherian
- def-weil-size-convention

The geometric input is already used in specifying the dualizing object in the statement;
no compactification or Noetherian reconstruction is required inside this proof. The formal
triangle morphism is constructed directly, so no separate triangle-morphism theorem is
imported. The signed double-Hom cone result for SheafOfModules is not needed here: the
remaining exactness input is the single contravariant native-Hom source result, and the
unit of the self-adjunction supplies bidual shift compatibility. All original statement
dependencies remain, and the unit route is unchanged (its realized statement/step lists
contain no alternate route to bypass).

Removed the obsolete approved tool_uses entries:

- lem-weil-pbc-ringed-internal-hom-exact-restriction
- lem-pur-rhom-global-sections
- lem-weil-pbc-site-derived-tensor-descent
- prop-pur-kinjective-resolutions-exist
- lem-pur-rhom-well-defined
- lem-pc-kflat-resolution
- lem-weil-pbc-commshift-nattrans-triangle-morphism
- lem-pur-hom-kflat-into-kinjective
- lem-weil-pbc-kinjective-hom-derived
- lem-pur-hom-complex-global-homotopy
- lem-sc-derived-hom-tensor-total
- sk-thm-nagata-sketch-noetherian
- lem-weil-pbc-finite-type-over-noetherian

These are local proof prunings, not withdrawals of library modules. No adopted source-tree
declaration or proof is deleted or replaced by sorry. No global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-site Hom/cone declarations use SheafOfModules and its recorded derived
Hom, whereas this item's public statements use native ModuleCat-valued sheaves and the
source-library closed structure. They are not interchangeable by definitional equality.
The additive site-module equivalence does not by itself supply a normalized derived
monoidal/Hom comparison. Reconstructing that bridge is longer than the native argument.

ClosedTriangulated.exists_distinguished_ihom_pre supplies an unspecified third arrow.
It does not prove coherent exactness with a connecting map compatible with shifts; the
new lemma isolates precisely that source result instead of treating the weaker assertion
as enough. Further work after the first delivery gate proved the parametrized-adjoint
transport and narrowed the remaining hole to canonical native Hom. The private, completely proved cochainSourceShift in
NativeInternalHomExact gives
cochain source-shift existence by adjunction transport from tensor shifts. It records
a proved part of the remaining model calculation for its next worker. The private
sourceShiftSign_add also proves q(m+n)=q(m)+q(n)+m*n for arbitrary integers, using
the divisibility of consecutive products by two, including negative integers. The complete
remaining model calculation is now explicit in the node/docstring: q(m)=m(m-1)/2
cancels the reindexing discrepancy, and the reversed split boundary has factor
(-1)^(p+1). Mathlib triangleOpEquivalence itself introduces no additional sign.
The formal unit argument proves the required biduality shift/triangle squares
once that exactness structure is supplied. A braiding suffices: use its inverse to normalize
evaluation, then its reverse to construct the self-adjunction. No derived symmetric-class
instance is assumed.

Specializing native constructions by direct exact/rfl repeatedly hit the kernel's limit,
even though elaboration took less than a second. Abstracting only the coefficient category
was insufficient for the whole pairing proof. Passing the target's actual localization
instances explicitly solved this without changing public definitions or limits.

## New nodes

lem-weil-native-internal-hom-contravariant-exact records Tag 08JC for the native monoidal
Grothendieck derived category, including the opposite shift convention. The node and docstring give the
K-injective model and signed source-shift/cone route. The transport to a general
parametrized right adjoint is proved privately in the item: right-adjoint uniqueness
gives the components, the parametrized counit identity proves source naturality, and
CommShift.ofIso plus isTriangulated_of_iso transport the exact structure. It is strictly one part of the
argument, and applies independently of any double-dual pairing or geometry. Existing
ringedInternalHom_exact has a different category and Hom encoding; it is not an exact
match and no unproved comparison between the encodings is assumed.

Change record: coord/changes/duality-pairing-raw-tensor-proof.md.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
