## What changed

Proved `AlgebraicGeometry.etale_discreteNoetherian_constructible_serre` in
`Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`, with its signature unchanged.
The proof converts the affine-local finite constant-model predicate to finite local
constancy, intersects the two finite stratifications, and applies exact inverse image
and local closure on each common stratum. The existing constant-scalar equivalence then
transports this to intrinsic module sheaves.

The extension argument was written in private helpers in the item module. Unlike the
existing finite-ring extension theorem, it uses a finite generating set of the relation
module of a finite free presentation, available over every Noetherian ring. It applies
the existing lifted-presentation/pushout lemma, composes the covering refinements, and
uses stalk exactness for finite generation. No finite-ring assumption was introduced.

Added proof imports of `WeilConjectures.ConstructibleSheaf.KernelCokernel` and
`WeilConjectures.ConstructibleSheaf.OpenClosed`, retaining the existing refinement import.
The DAG records the actual étale route and explicitly retains the original open
pro-étale plan. No definition, public theorem signature, or target statement changed.
The public-import removals are recorded in
`coord/changes/A5-discrete-noetherian-serre-imports.md`, including all 230 source-graph
consumers and their holders. Six direct consumers are checked in a separate scratch
mirror, against the delivered module; no consumer edits are proposed. All six compiled
successfully against the delivered module: AdicStratifiedPerfect (5.3s), DetThmSfCtfStabilityInternalHom (4.2s),
FiniteFieldInternalHomFiniteness (3.2s), FiniteTorInternalHomAnyField (3.1s),
PrimeFieldTensorDevissage (3.2s), and AdicClosedConstructible (5.0s), all under
`Sheaf.Paper`. The item compiled again in that check (10.4s), with the diagnostic
`#print` removed. These checks used a scratch mirror outside the delivered source tree.

Validation: the retained item was recompiled successfully on 2026-10-19 (12.5 seconds).
The complete item compiles without warnings. `#print axioms` for the étale
closure theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The only remaining `sorry` is the original pro-étale theorem. Empty cover members are
removed only when choosing a geometric point; their removal preserves the cover.
The trivial-stratum zero argument handles the empty scheme and zero coefficient ring.

## Proved and sorry left

Closed 1 of the original 2 holes:
`AlgebraicGeometry.etale_discreteNoetherian_constructible_serre`.

Left unchanged:
`AlgebraicGeometry.proEtale_discreteNoetherian_constructible_serre`
(blueprint `lem-sfb-discrete-noetherian-constructible-serre`).

Added 0 holes and split off 0 theorems. Every delivered private helper is proved.
This is a proof of the étale theorem, not a decomposition.

For the remaining theorem, the generic local Serre declaration uses a small site with
object and arrow universe equal, whereas the original pro-étale site has objects in
u+1 and arrows in u. Its constant modules are global constants restricted to slices;
the item predicate instead uses sheafification directly on each slice, after forgetting
commutativity of the coefficient ring. Applying the existing theorem requires transport
through AsSmall, the coefficient-ring comparison, and the normalized constant-module
localization comparison. Common strata also require transporting the canonical module
pullback composition isomorphism and its local constant models. The existing finite-ring
pullback/local-constancy declarations cannot be used for arbitrary Noetherian R.
I did not add replacement holes for these interfaces. A zero-sheaf proof was explored
but no unused pro-étale helpers are included in this delivery.

## No longer needed

Removed these original imports from the item module:

- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` (public): its finite-ring
  realization interface is unused by either public signature or the completed proof.
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf` (public): the signatures
  use the existing affine-local predicates; the étale proof uses the module-valued API.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`.
- `Sheaf.Paper.LocalizeRingedSiteMorphism`.
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`.
- `Mathlib.Algebra.Module.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`.

The last eight imports are unnecessary for the completed étale proof: concrete
upperStar composition, restriction, constants, stalks and exactness are already proved
in the source library. The generic local Serre theorem is replaced here by existing
Noetherian kernel/cokernel closure and the proved finite-presentation extension argument.

For the étale part the planned proof nodes
`lem-weil-pbc-left-exact-site-inverse-image-tensor`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-site-morphism-composition`,
`lem-weil-pbc-localize-ringed-site-morphism`, and
`lem-weil-pbc-locally-constant-derived-serre` need no new proof. They remain in the
item node's proof dependency union because the still-open pro-étale plan cites them;
this delivery does not claim that they can be pruned from the whole target closure.
`lem-weil-pbc-constructible-stratification-intersection` remains used directly.
There are no withdrawn modules or new-node subtrees.

Exploratory imports of `WeilConjectures.ConstructibleSheaf.FiniteConstantModel`,
`WeilConjectures.ConstructibleSheaf.EtaleDescent`, and
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` were also removed before delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned generic route needs actual comparison maps
between its small-site constant-ring module presentation and the pro-étale predicate;
these interfaces are not definitionally identical. This is glue still needed for the
open theorem, not a mathematical objection to the dependency statements.

The source library's extension theorem assumes a finite coefficient ring. Its proof
can be generalized as above: trivialize the finitely many generators of the relation
module rather than every relation. The existing kernel and cokernel statements already
have the needed Noetherian/general coefficient hypotheses. Thus the étale theorem can
be completed entirely from proved declarations, without the generic still-open inputs.

Resume infrastructure notes (2026-10-19): the first required dry run terminated with
exit 137. The second dry run waited for worktree capacity, then raised
`subprocess.TimeoutExpired` while checking out its temporary worktree after 600 seconds.
A further retry is running. These are delivery-tool failures before preflight;
the item and its six direct consumers compiled successfully through lcompile.py.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
