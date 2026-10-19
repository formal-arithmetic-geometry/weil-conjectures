## What changed

Replaced the proof of `AlgebraicGeometry.Etale.finiteRing_compactGenerators` with a
compiling proof from the declared stratum-compactness and thick-generation results.
The finite-type assumptions supply Noetherianity. Compact objects form a thick
subcategory, and flat geometric fibres of each stratum sheaf let the existing
stratum compactness theorem apply. The fibre comparison explicitly lifts the
point universe and transports along `uliftSheafFiberIso`.

The generator family is constructed directly: index by `T.AffineEtale`, take the
free Yoneda sheaf with coefficient module `C`, and put it in degree zero. Existing
source results prove constructibility and flatness. The proof compares the two
constructibility conventions and supplies a single bounded flat complex to prove
Tor amplitude `[0,0]`. No data are chosen from an unproved existence theorem.

Isomorphism detection is also proved, in `AffineEtaleFreeDetection`. The ordinary
free sheaves separate morphisms by free Yoneda and affine cover density. For any
separating family, vanishing of all shifted derived Hom tests forces a K-injective
representative to be exact: the Hom-complex single-object formula supplies lifts
of generator maps to cycles, and separation proves the differential onto cycles
epi. The distinguished cone exact sequence then turns the postcomposition
bijections into a zero cone and hence an isomorphism. The proof explicitly handles
the signs in shifted triangles and shift-addition naturality.

The parent signature and all existing public imports are unchanged. Both delivery
modules compile through `lcompile.py --all` with no errors or warnings.
The current resumed session revalidated both modules on 2026-10-19 with
`lcompile.py --all`: exit code 0, detection module 0.1 seconds and parent
1.8 seconds, without errors or warnings. It checked the unchanged parent signature,
the stratum and thick-generation interfaces, and the direct free-sheaf construction.
The existing node differs only in its allowed proof, proof-dependency, proof-origin
and obsolete-tool-use fields.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.finiteRing_compactGenerators` (one of one original holes).
Also proved the new auxiliary theorem
`AlgebraicGeometry.Etale.isIso_of_affineEtaleFreeComplex`
(node `lem-pur-affine-etale-free-detection`). All four private helpers in its
module are proved. Both delivered modules contain zero `sorry`; no holes added,
no unfinished split-offs. Net one original hole removed. The parent still uses
existing declared compactness and thick-generation dependencies whose own proofs
are separate project items; no claim is made that the full target closure is
axiom-free yet.

The explicit affine free-sheaf definition constructs its data directly. No data
are chosen from an unproved existence theorem. Detection covers arbitrary
unbounded targets, empty schemes, zero rings, and non-separated schemes.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`,
  `WeilConjectures.CategoryTheory.Sites.Point.Flat`, and
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic`: the needed declarations
  are publicly re-exported by imports already required for the proof.

- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`: Mathlib's affine
  etale site already provides the required ModuleCat-valued Grothendieck instance.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the canonical
  source Grothendieck-derived instances supply the needed resolutions; no separate
  ringed-site resolution theorem is used.
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`: only existence of
  coproducts is needed, supplied by `GrothendieckDerivedCoproducts`.
- `Mathlib.Algebra.Homology.HomologicalComplexLimits` and
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`: no direct proof use.
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement` and
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: the stratum objects in
  `etaleThickGeneration` already use the ordinary closed pushforward, exactly as
  in stratum compactness; no extra derived/ordinary comparison is needed here.
- `Sheaf.CategoryTheory.CompactCone`: the proved `CompactObjectsThick` theorem
  supplies all thick closure properties together.
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible`: use the proved
  source affine Noetherian specialization `isConstructibleSheaf_freeYoneda`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`: use the proved
  source `flat_freeYoneda`, a specialization of free-sheaf flatness.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: the existing flat-model
  characterization proves the degree-zero Tor assertion directly.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` and
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: already available via imports
  actually needed for the statement and proof.

These are removals of direct imports. In particular,
`GrothendieckDerivedCoproductsColimit` remains imported by the stratum-compactness
module. No claim is made that any of these modules is globally unreachable from
the targets.

Updated the node's direct proof dependencies. The parent no longer directly needs
`lem-weil-pbc-locally-noetherian-quasi-separated`, `def-weil-size-convention`,
`prop-pur-kinjective-resolutions-exist`, `lem-kun-grothendieck-derived-coproducts`,
`lem-cbc-open-closed-recollement`, `lem-weil-pbc-exact-functor-derived-functor`,
`lem-sc-compact-cone`, `def-pc-compact-object`,
`lem-pc-sites-modules-j-shriek-flat`, or `def-kun-derived-tensor` as proof tools.
Their needed conclusions come from the explicit instances, general coproduct
existence, thick closure, direct free-sheaf flatness and flat-model criterion.
The free-Yoneda and K-injective detection dependencies of old steps 5 and 6
move to the proved detection node. Its cone argument avoids a separate
section-cohomology comparison and local cocycle/boundary sheaf argument. These
are changes of direct dependencies, not claims of global pruning.
Removed the corresponding obsolete direct `tool_uses` approvals from the parent
node, preserving the order of the approvals still used by its proof.
The removed approvals are `lem-weil-pbc-locally-noetherian-quasi-separated`,
`prop-pur-kinjective-resolutions-exist`, `lem-kun-grothendieck-derived-coproducts`,
`lem-cbc-open-closed-recollement`, `lem-weil-pbc-exact-functor-derived-functor`,
`lem-sc-compact-cone`, `lem-pc-sites-modules-j-shriek-flat`,
`lem-weil-pbc-free-yoneda-presheaf-module`, and `lem-weil-pbc-kinjective-hom-derived`.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route defect found. The original proof plan asks for
more direct imports than the actual argument needs: termwise coproduct comparison,
a separate closed derived/direct-image identification, and ringed extension-by-zero
flatness can be replaced by the already declared APIs above. The source's affine
free-sheaf constructibility theorem is already proved and avoids reproving the
more general etale extension statement. The two source constructibility predicates
must be explicitly compared; they are not definitionally identical.

## New nodes

`lem-pur-affine-etale-free-detection`, attached to the proved
`AlgebraicGeometry.Etale.isIso_of_affineEtaleFreeComplex` and its explicit
`affineEtaleFreeComplex` construction. This packages the completed generator
detection part of the argument, with no remaining holes. The earlier attempt's
three Mathlib searches and DAG/blueprint duplicate searches are retained. The
proof uses existing source and Mathlib APIs rather than the originally planned
section-cohomology computation. No change record is needed: no existing statement
or definition changes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
