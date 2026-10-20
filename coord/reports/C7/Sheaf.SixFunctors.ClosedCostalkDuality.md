## What changed

Replaced both `sorry` bodies in `Sheaf.SixFunctors.ClosedCostalkDuality` by complete
Lean proofs from the closed projection formula and the existing normalized
ringed-site tensor-Hom model. The private categorical argument composes five Hom
bijections, proves naturality in the test object and internal-Hom source, and
uses `Yoneda.ext` and `NatIso.ofComponents`. In particular the K-naturality is
proved; the result is an isomorphism of functors, rather than unrelated object
isomorphisms.

Added `Sheaf.SixFunctors.ClosedProjectionEtale` and
`Sheaf.SixFunctors.ClosedProjectionProEtale`, one projection statement each. They
isolate steps 1--3 of the original plan and the middle projection identity of the
current blueprint proof. Neither has an exceptional adjoint, dualizing object,
or internal-Hom comparison as its conclusion. Their inputs retain arbitrary
commutative ring sheaves, the actual inverse-image coefficients and operations,
ordinary unbounded derived categories, and independent site universes. The etale
version accepts exactly the original adjoint and Q-factorization data. The
pro-etale version retains `QuasiCompact j` and is fully proved in this packet. Its
private helpers construct the projection map, prove bivariate naturality, descend
closed full faithfulness, compute open vanishing on cohomology, and detect
isomorphisms by the distinguished cone. Each theorem quantifies over normalized
tensor models, so no arbitrary tensor structure is substituted. The etale module
also proves `closedEtaleModulePushExact` privately: finite direct-image exactness
for abelian sheaves transfers to the actual module pushforward by reflection of
finite colimits through the target forgetful functor, for arbitrary coefficient
maps.

Existing public imports, definitions, instances and theorem signatures in the
item are unchanged. New imports in that module are private proof imports. The
pre-existing unused `let ΛU` binders are retained verbatim, with the unused-variable
linter scoped off only around those two declarations. No adopted source-library
file or consumer interface was changed. Two unclaimed Sheaf dependency modules
also have five existing bookkeeping holes filled, with unchanged signatures,
attributes and public imports: `Sheaf.Paper.ProEtaleCanonicalTensorPullback` and
`Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses`. The proof-only
change is recorded in `coord/changes/C7-closed-costalk-tensor-bookkeeping.md`.

## Proved and sorry left

Holes closed (2 of 2 in the item):

- `AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality_etale`.
- `AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality`.

Additional existing holes closed in the two unclaimed tensor dependencies (5):

- `AlgebraicGeometry.Scheme.proEtaleTensorPreadditive`.
- `AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback_naturality`.
- `AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal_isIso`.
- `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive`.
- `SheafOfModules.CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison.total_isIso`.

Holes added (1):

- `AlgebraicGeometry.Scheme.closedImmersionEtaleProjection`, node
  `lem-sf-etale-closed-projection-unbounded`.

The following existing dependency holes are retained unchanged; all four carry
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and sourced proof docstrings:

- `AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback_existsUnique`.
- `AlgebraicGeometry.Scheme.proEtaleCanonicalTensorPullback`.
- `SheafOfModules.CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_existsUnique`.
- `SheafOfModules.CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_unit`.

These four and the new etale projection hole are every `sorry` in the delivered
Lean files. The packet closes seven existing holes, including both original item
holes, and adds one strictly smaller etale projection hole: six fewer holes in
the edited packet. The project ledger determines the net count in the targets'
import closure against its pinned baselines. The pro-etale projection theorem is
proved in full from
existing library declarations. The etale branch is a decomposition, not a claim
that its geometric projection formula is fully proved. The new statements are
genuine separate results:
they provide the source's middle tensor identity, reusable independently of any
exceptional adjunction or Verdier dual. The real combining proof is in the item;
neither new theorem restates either duality theorem.

`costalkHomEquiv`, `costalkTranspose_left`, `costalkTranspose_source`,
`costalkHomEquiv_left`, `costalkHomEquiv_source` and
`costalkDualityOfProjection` are private and fully proved. Diagnostic `#print axioms`
checks showed only `propext`, `Classical.choice`, and `Quot.sound` for the Hom
bijection, its two naturalities, and the final generic duality proof. The formal
projection helper and all seven geometric/cohomological helpers in the
pro-etale module also have only these permitted axioms; the public pro-etale
projection proof additionally uses existing canonical tensor/model declarations.
The public duality theorems still depend on existing library holes, including
`CategoryTheory.ringedSiteDualityMaps_exists`; the etale theorem also depends on
the one new projection hole. They are not claimed to be
axiom-closed.

The two preadditivity proofs and the general total-isomorphism proof were checked
with `#print axioms`: only the three permitted axioms occur. The selected pro-etale
ordinary naturality and total-isomorphism proofs additionally depend on the retained
`proEtaleOrdinaryTensorPullback_existsUnique` theorem, exactly as intended.

Compilation: all five modules compile cleanly through `lcompile.py --all`; all Lean lines
are at most 100 characters. The projection docstrings and nodes supply complete
proofs in words. Edge cases checked mathematically: empty closed subscheme,
empty complement, zero complexes and zero coefficient ring; none requires an
extra hypothesis. The projection direction is deliberately inverted before
precomposition in the Hom chain.

## No longer needed

Removed the following direct private imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `Sheaf.Paper.PbcCompletedPullbackActual`.
- `Sheaf.Paper.PbcActualScalarPullback`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`.
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

The closed-support, exact inverse-image, tensor-pullback, cohomology-detection and
cone arguments remain needed in the two projection nodes, with their dependencies
retained there. They have moved to the correct part of the proof and are not
claimed as globally pruned. In particular no upstream declaration was removed,
weakened or replaced by `sorry`.

The item's direct proof no longer needs nodes
`lem-weil-pbc-ringed-internal-hom-exact-restriction` and
`lem-pur-rhom-global-sections` to manufacture its Hom equivalence; it uses the
existing closed tensor-Hom adjunction directly. The exact restriction and
unbounded support facts from original steps 1--3 are still needed in the projection
nodes. No Lean module is withdrawn. The old direct `lem-kun-04ca` tool approval is
removed from the parent; its etale projection use is explicitly declared for
review in the new node's split report.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-route error was found. The original DAG's middle projection
identity had no standalone Lean declaration at the required arbitrary-coefficient,
unbounded scope. The finite constant-coefficient projection theorems found in the
adopted source do not supply this identity. The two new statements isolate this
actual gap without imposing perfectness, finite coefficients or a Tor bound.
The pro-etale gap is closed here. On the etale side, the declared closed-support
and essential-image facts are formulated for abelian sheaves. The exactness
coefficient-action bridge is now proved directly from the existing finite
direct-image instance, rather than rebuilding the geometric-stalk proof. Closed
full faithfulness and open detection with coefficient actions, tensor pullback,
and transport through the supplied termwise comparisons remain the one separately
stated projection lemma. The constant-coefficient source theorems and
`etaleInverseImageModuleAdjunction` were checked; the latter chooses a ring
inverse image up to adjoint comparison and does not directly provide this
normalized unbounded projection statement.

The old currying interface `ringedInternalHom_tensor_adjunction` is stated on a
site with equal object and morphism universes. The actual sites here have object
universe u+1 and morphism universe u. The already recorded independent-universe
`RingedSiteDualityModel` and `ringedSiteDualityMaps_exists` provide the needed
closed tensor-Hom interface without shrinking the sites or changing a category.
Its use is a request for a generic tool use of `lem-sfb-ringed-site-duality-maps`:
only the ambient tensor-Hom model is taken, not biduality or any unit's geometric
route. No maintainer approval was added to the parent node.

## New nodes

`lem-sf-etale-closed-projection-unbounded`, in
`dag/nodes/sec-six-functors/`, records the middle projection identity on the
small etale site. Its declaration is in `Sheaf.SixFunctors.ClosedProjectionEtale`.
Its three proof steps are finite direct-image exactness with the proved
coefficient-action bridge and the original etale closed-support facts, exact
termwise descent and tensor comparison, and cone detection of the projection
map's invertibility. The finite direct-image use is declared for independent
review as a generic exactness tool, not a curve-unit result. LeanSearch, LeanFinder, Loogle and Mathlib grep were run;
the complete imported blueprint was searched for closed projection and projection
identity. No matching statement at this scope was found.

`lem-sf-proetale-closed-projection-unbounded`, in the same chapter directory,
records that identity on the actual small pro-etale site, with quasi-compact
complement. Its declaration is in `Sheaf.SixFunctors.ClosedProjectionProEtale`.
Its Lean proof uses the existing ringed open-closed sequence, actual-coefficient
essential-image and detection lemmas, and generic derived full faithfulness,
rather than geometric-stalk conservativity on that site. The corresponding
off-unit uses are declared for review in its split report. This is the original
closed-support route, not an invocation of biduality or a closed-unit result. The same four searches and blueprint searches apply.
Both nodes have their own strictly smaller tensor conclusion and the exact source
location in the current blueprint proof. The proof-only dependency adaptations are
recorded in `coord/changes/C7-closed-costalk-tensor-bookkeeping.md`; neither changes
a statement or definition.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
