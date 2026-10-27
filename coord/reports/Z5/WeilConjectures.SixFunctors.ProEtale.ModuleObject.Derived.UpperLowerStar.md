## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`
using the internal/section tensor equivalence, the existing concrete pro-étale algebraic
inverse-image presentation with coefficient comparison the identity, and enough topos points.
All original public imports, signatures and non-theorem bodies are retained. Private proved
instances cache colimits, graded tensor hypotheses, exact sequential colimits and flat
resolutions. Local irreducibility settings prevent large tensor/derived constructions from
being unfolded during comparison; no compile or heartbeat limit is raised. Proof imports
are private. The unit's derived-factorization route is retained.

Added `Sheaf.AlgebraicGeometry.ProEtaleInternalPullbackKFlat`, proving the generic
arbitrary-ring coefficient result, and `Sheaf.Algebra.Homology.AlgebraicInverseImageKFlat`,
proving the reusable pointwise preservation step. It constructs the composite ringed point explicitly: its ring is the
target stalk ring, and its module functor is the composite of algebraic inverse image and
the target stalk. All seven ring/module operation graph fields are proved by successive
application of the two presentations. Equal-universe ULifts are removed by the canonical
natural isomorphism, without changing the module functor. The two clauses of the existing
stalk criterion then prove K-flat preservation. The proof does not require flat terms.

Searches: LeanFinder for inverse image preserving K-flat complexes returned ordinary module
flatness and inverse-image finite-limit declarations; Loogle for mapHomologicalComplex
returned the generic mapping/comparison API; msearch grep for composite ringed points and
pointwise preservation returned no matches. Local searches of both library roots found the
existing section-module algebraic presentation and the stalk criterion. The other general
ringed-topos K-flat pullback statements require flat terms and do not apply to this instance.
Read Stacks `sites-cohomology.tex`, `lemma-check-K-flat-stalks` and
`lemma-pullback-K-flat-points` (Tags 0DEN and 0DEP). The latter explicitly tests arbitrary
target complexes through their stalks. Edge cases checked: identity inverse image, zero
ring, empty conservative family, and unbounded complexes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`
(node `lem-sfb-module-mapmod-pullback-kflat`).

Added no holes. The generic coefficient theorem
`AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_proEtale`
(node `lem-sfb-proetale-internal-pullback-kflat`) is proved, as is
`SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points`
(node `lem-sfb-algebraic-inverse-image-kflat`). No `sorry` remains in the item
or either new module. This is a proof, not a decomposition into new admitted statements.

## No longer needed

No existing public import was removed. The proof uses
`lem-c2-proetale-section-module-algebraic-inverse-image` directly at `rho = id`, so it does
not need `lem-sfb-internal-module-inverse-image-comparison` or import its module
`Sheaf.CategoryTheory.InternalModuleInverseImageComparison`. The concrete scheme-specific
presentation already proves the actual ring, module action and differential comparison
needed here. The general normalization theorem remains in the library for its other users.
The existing tensor/transport tool-use approvals are retained.
No module is withdrawn. The generic module omits unrelated derived adjunction,
right-derived functor and injective-resolution imports from the original source context.
The assigned source module retains every original public import.

## Where the brief, the DAG or earlier work was wrong

The concrete condensed-ring substitution makes inferred graded-tensor and derived-functor
comparisons expensive. The source file therefore uses proved private Prop-instance caches
and local irreducibility settings; the original declaration bodies remain unchanged except
for the assigned proof. The generic theorem and concrete instance also compiled separately.


The existing pointwise plan is correct. Its generic normalization comparison is stronger
than this item needs: the already proved scheme-specific algebraic presentation gives the
needed comparison without rebuilding a normalized abelian lift. The latest blueprint's
short flat-resolution explanation cannot be applied as a direct exact-monoidal argument:
the target acyclic test complex need not be a pullback. The proof uses the published 0DEN/
0DEP stalk argument to handle that quantifier. No statement or definition was weakened.

## New nodes

`lem-sfb-algebraic-inverse-image-kflat`, in the item's chapter and unit, records the proved
generic composition-of-ringed-points argument. Its statement takes an explicit conservative
family and its stalk presentations, permits empty families, and has no flat-term assumption.
It is strictly the stalk-preservation part of the assigned instance; the second new module
supplies the actual pullback presentation, internal/section K-flat comparison and
conservative family. The assigned instance specializes that generic result.

`lem-sfb-proetale-internal-pullback-kflat` records the fully proved arbitrary-coefficient
argument. Its separate module keeps private tensor-comparison imports out of the source
module’s elaboration environment. It has no admitted fields or statements. No change record
is needed: no existing signature, public import or definition was changed. Ringed-site stalk witnesses are selected from the fully proved
`RingedSitePoint.nonempty`; its underlying-set isomorphisms and operation graphs determine
the ring and module structures up to the isomorphisms used in the stalk argument.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
