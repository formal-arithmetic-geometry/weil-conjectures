## What changed

Replaced `AlgebraicGeometry.Etale.ordinary_supported_kummer`'s single `sorry` by a complete
assembly from the unique normalized boundary, normalized finite-twist transport, the Chern
realization, and the two separate compatibility results below. Both existing public signatures,
visibility, and public imports are unchanged. The existing unique-boundary projection continues
to use `supported_cartier_boundary_existsUnique` directly.

The closed exchange is invertible by finite sheaf base change and the constant-sheaf comparison;
this part is proved here rather than left inside the pullback result. The chosen derived arrow
is precisely `supportedExactDerivedMap`, and the chosen first-Chern representative is the inverse
of `Ext.homEquiv` applied to the derived unit composed with that arrow.

Added `SupportedDerivedUnitForget`, proving the exact derived-unit comparison on single objects
and the coefficient square on constant sections, and `SupportedKummerChernRealization`, proving
the Chern equality from the relative-boundary witnesses. For the latter, the equivariant map
identifies the frame torsor with the extension's lifting torsor, the torsor boundary is its
extension class evaluated at the integral unit, and Yoneda associativity gives the Kummer class.
The two remaining compatibility results are isolated in one new module each. They retain the
original declared dependencies and the source's separate pullback and scalar arguments.

`DerivedSingleUnitExact` computes the unit of the existing full left-derived/right-derived
adjunction on single objects. To avoid repeatedly specializing its large structural instance
application, `supportedDerivedUnit` in `OrdinarySupportedKummerSystem` now calls the explicit generic
`Adjunction.derivedSingleUnit`. Its body names exactly the old full derived-unit/single-comparison
composite; unfolding the names recovers the original construction definitionally. Its existing
signature and attributes stay verbatim, and every other explicit definition body is unchanged.
One new public import is required by this cache. The definition module is unclaimed; the
A7 direct consumer is checked against the repair. No adaptation to a held module is delivered.
See `coord/changes/supported-derived-unit-comparison-cache.md`; normal definition review applies.

The concrete derived comparison and the boundary/scalar interfaces locally select the
sheafification and Grothendieck instance proofs already captured by `DerivedCategoryModule`.
The two interface definitions retain their written signatures and bodies; their stored implicit
instance expressions now match the derived interfaces. Original target clause probes isolated
the cost: the boundary predicate took about ten seconds, uniqueness eight seconds, and the
scalar clause exceeded twelve thousand kernel heartbeats. The original full target statement
alone took twenty-six seconds, and a complete proof subsequently exceeded sixty seconds.
The two additional definition records are
`coord/changes/supported-kummer-boundary-instances.md` and
`coord/changes/supported-kummer-scalar-instances.md`. Both modules are unclaimed.
The main declaration uses these same instances; its helpers and unique-boundary projection
retain their default instances. The selections are local and export no instances. The existing
auxiliary proof names lack a stable source API; source refactors may require updating them.
The auxLemma linter is disabled only on these intentional attribute commands.
After normalizing the interfaces, all ten modules compile cleanly; the main theorem takes
34.0 seconds, the unit definition module 41.8 seconds, the boundary interface 29.2 seconds,
and the scalar interface 26.4 seconds. No timeout limit is raised and no file is split to
meet the limit. No source-library file, target, or written existing theorem signature changes.
No data is chosen from mere existence in a definition.

## Proved and sorry left

Original holes closed: `AlgebraicGeometry.Etale.ordinary_supported_kummer` (one body).
The item module now contains zero `sorry`. All three repaired definition modules contain zero holes.

New proved declarations:

- `CategoryTheory.Adjunction.derivedSingleUnit_comp_comparison`
  (`lem-asd-derived-single-unit-exact`), using the explicit cache
  `CategoryTheory.Adjunction.derivedSingleUnit` (`def-asd-derived-single-unit`).
- `AlgebraicGeometry.Etale.supported_derived_unit_forget`
  (`lem-asd-supported-derived-unit-forget`).
- `AlgebraicGeometry.Etale.supported_kummer_chern_realization`
  (`lem-asd-supported-kummer-chern-realization`).
- Private exact-single adjunction, integral-generator, exchange-isomorphism,
  and transport assembly helpers in their respective modules.

New holes left:

- `AlgebraicGeometry.Etale.supported_kummer_boundary_pullback`
  (`lem-asd-supported-kummer-boundary-pullback`), the Ext equation only, for arbitrary
  Cartier-preserving pullback and roots-normalized transport.
- `AlgebraicGeometry.Etale.supported_kummer_boundary_scalar`
  (`lem-asd-supported-kummer-boundary-scalar`), scalar compatibility for two given normalized
  boundary representatives, including the specified unbounded derived scalar units.

This is a decomposition: one original hole is closed and two strictly separate compatibility
holes are added. It is not an axiom-free proof or a positive net hole reduction. Existing imported
holes are retained as the stage-3 contract requires; they are not new holes in this packet.

Validation: the ten delivered Lean modules are checked together by `lcompile.py --all`.
Original direct consumers of all three repaired definitions are checked as separate probes.
The N1 consumer limitation is reported below; no failed adaptation is included.
Six unchanged external consumers compile: CartierKummerMap (43.7 s),
FiniteP1ArbitraryBaseIntegrals (42.5 s), GeoCartierCycleClass (48.4 s),
ProjectiveLineDiagonalIntegrals (33.1 s), SupportedCartierBoundaryExistence (43.8 s),
and FiniteReductionAffineOrientation (41.6 s). The two pre-existing verification limits
are documented below. Server delivery preflight supplies the final compile, signature,
and axiom audit.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`
- `Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback`
- `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource`
- `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`

These are direct-import removals, not a claim that the modules are globally unnecessary.
Several are now used in the Chern or compatibility modules, while the others remain reachable
through retained dependencies. No module is withdrawn and no upstream declaration is removed.
The Chern calculation itself does not require relative-cone or module-cohomology comparison
machinery: it uses the actual torsor extension supplied by the boundary specification.

Removed obsolete top-level direct `tool_uses` entries from the item's node (their use, where
still needed, is below the new compatibility nodes):

- `def-pc-divisor-line-bundle`
- `def-weil-sheaf-of-modules-category`
- `lem-kun-inverse-image-monoidal`
- `lem-kun-pullback-constant`
- `lem-kun-stalk-as-pullback`
- `lem-pur-derived-change-of-rings`
- `lem-sc-line-bundle-torsor`
- `lem-weil-pbc-etale-module-cohomology-forget`
- `lem-weil-pbc-etale-module-pullback-forget-naturality`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-weil-pbc-module-abelian-derived-direct-image-comparison`
- `lem-weil-pbc-open-closed-short-exact`
- `lemma-weil-pbc-finite-direct-image-exact`
- `lemma-weil-pbc-finite-stalk-formula`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-geometric-stalks-exact`
- `prop-weil-pbc-inverse-image-modules-exact`

The retained item approval is `lem-asd-etale-finite-twist-pullback`. Node proof dependencies now
follow the actual assembly, and all dependencies of the unproved compatibility arguments remain
recorded below those arguments. No whole module is claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The original proof plan conflated construction,
normalization, and two functoriality checks in one large existential theorem. Boundary existence
and uniqueness are already supplied by `supported_cartier_boundary_existsUnique`; reconstructing
them here would duplicate existing work. The Chern equation follows directly from its torsor
extension witnesses, together with exact derived-unit normalization. Finite sheaf base change
already proves the exchange-isomorphism clause without a fresh stalk argument.

The remaining pullback and scalar equations are genuine additional arguments, not consequences
of existence and uniqueness without checking how the relative normalization transports. Their
new statements assume the existing normalized representatives, so they neither reconstruct
those representatives nor repeat the entire existential theorem. Edge cases checked in the
statements and prose proofs include empty support and schemes, N = 1, nonflat coefficient maps,
and nonflat base maps whose pullback remains Cartier. No unit-level route is bypassed.

The original `CartierReductionSiteComparison`, held by N1, exceeds sixty seconds both
against this packet and against the unchanged shared library. The control compile used
`scratchpad/N1OriginalBaseline.lean`, outside `lean/`, so it saw only the original shared
artifacts. Whole-module and single-declaration local instance selections did not make the
file compile within the limit. Those attempted adaptations are excluded: this is a pre-existing
consumer verification limitation, not a tool failure, and the holder retains all its work.
The maintainer/N1 should resolve that file's existing performance problem. No signature or
proof in the held module is changed in this delivery.

The original `ProEtaleProjectiveLineTrace` cannot currently be checked: the shared build lacks
`Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem.olean`. That dependency's source is
present and no rework withdrawal is recorded. This packet neither imports that consumer nor
adds this dependency; both existing modules and their DAG attachments are preserved. This is
another pre-existing consumer verification limitation for the maintainer's global build.

## New nodes

`lem-asd-derived-single-unit-exact`, in
`dag/nodes/sec-smooth-purity/lem-asd-derived-single-unit-exact.json`, records the proved
comparison of the full derived adjunction unit on a single object with its ordinary
adjunction unit. Its public theorem is `derivedSingleUnit_comp_comparison` in
`DerivedSingleUnitExact.lean`. It has no holes.

`lem-asd-supported-derived-unit-forget`, in
`dag/nodes/sec-smooth-purity/lem-asd-supported-derived-unit-forget.json`, records the proved
generic exact-unit and integral-evaluation identity. It requires neither Cartier geometry nor
finite coefficients. Its public theorem is in `SupportedDerivedUnitForget.lean`.

`lem-asd-supported-kummer-chern-realization`, in the same node directory, records the proved
Chern clause from a normalized boundary, using the frame/lifting-torsor classification.
The main assembly composes it with the preceding generic identity. Its public theorem is in `SupportedKummerChernRealization.lean`.

`lem-asd-supported-kummer-boundary-pullback` records the source's penultimate pullback argument:
Cartier line and section comparison, natural relative torsor and Kummer boundaries, the natural
support-Hom comparison, and the normalized root-tensor transport. It retains all the applicable
original declared proof dependencies. Its remaining hole is in `SupportedKummerBoundaryPullback.lean`.

`lem-asd-supported-kummer-boundary-scalar` records the source's final coefficient-extension
argument, including the normalized source and line scalar units and the boundary square. It
retains scalar-source, the finite twist line, derived change of rings, and the relative torsor
and Kummer declarations. Its remaining hole is in `SupportedKummerBoundaryScalar.lean`.

Each node has its source, numbered proof, declaration attachment, three kinds of Mathlib search,
and the original blueprint ancestor and unit. Blueprint search found no existing statement of
these precise compatibility interfaces. The generic comparison node additionally records the full derived-adjunction hypotheses
and the exact single-object computation. Its theorem is in `DerivedSingleUnitExact.lean`, has
no holes, and uses the existing full derived adjunction and its published unit factorization.

`def-asd-derived-single-unit` records the explicit generic cache of the original full derived
unit followed by its left-single comparison and the image of c. It has the full ambient
monoidal/flat-resolution hypotheses required by the existing left-derived adjunction, no holes,
and no new choice. The existing definition node records this implementation dependency; its
mathematical statement is unchanged. The change record lists every direct consumer.

The two existing boundary/scalar definition nodes record only the implementation repair notes;
their mathematical statements and dependency lists are preserved. Their change records list
all direct declaration users and current holders. No node is withdrawn.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
