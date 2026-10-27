## Worker report

The module `Sheaf.TraceFormula.GeonormalGeoconnectedFiniteTypeIntegral` states
`AlgebraicGeometry.geometricallyIntegral_of_geometricallyConnected_of_geometricallyNormal`.
Its only proof is `sorry`. The existing node is changed only in `lean`; no definition,
new node, dependency repair, or statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The scheme X over k is `{X : Scheme.{u}} [X.Over (Spec (.of k))]`; its structure
  map is `X ↘ Spec (.of k)`.
- Nonemptiness is `[Nonempty X]`, retained explicitly as in the node.
- Finite type is the recorded conjunction, supplied as the two instance binders
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`.
- An arbitrary field extension is `(K : Type u) [Field K] [Algebra k K]`.
  These test fields use the same universe as k and X, exactly as the recorded
  Mathlib geometric predicates; there is no smaller independent test universe.
  No finiteness, separability, algebraicity, or characteristic restriction is imposed.
- The base change X_K is `Limits.pullback (X ↘ Spec (.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. This is the scheme fibre product
  specified by the base-change dependency, not a product of underlying sets.
- Geometric connectedness is `[GeometricallyConnected (X ↘ Spec (.of k))]`.
  Its field-base-change meaning follows from its defining `geometrically` field
  and `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`.
  The property used is `ConnectedSpace`, which includes nonemptiness.
- Geometric normality is `hnormal`: for every such extension and every point x of
  that precise pullback scheme, `IsDomain` and `IsIntegrallyClosed` of its
  `presheaf.stalk x`. The first conjunct supplies the domain requirement; the second
  means integrally closed in `FractionRing` of that same ring. This uses the
  normal-domain conjunction recorded by def-weil-pbc-normal-ring without a new predicate.
- The conclusion is `GeometricallyIntegral (X ↘ Spec (.of k))`. Its defining
  `geometrically IsIntegral` field and the same Mathlib equivalence say that X_K
  is integral for every field extension, including nonemptiness and reducedness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its QuasiCompact import:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`
  (def-weil-finite-type-morphism).
- `Mathlib.Algebra.Algebra.Defs` through the geometric imports: `Algebra`, `algebraMap`
  (def-pc-field-extension).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documented scheme
  base-change interface is `CategoryTheory.Limits.pullback`, rather than the
  record's principal declaration `Scheme.Modules.moduleBaseChange` (which is only
  module base change). The module is imported publicly (def-pc-base-change).
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.GeometricallyConnected`; its imported Basic module defines
  `geometrically` and the field-extension equivalences. `ConnectedSpace` is from
  `Mathlib.Topology.Connected.Basic` (def-weil-connected-scheme).
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`, with the imported irreducible and reduced
  classes (def-pc-geometrically-irreducible). `AlgebraicGeometry.IsIntegral` is in
  `Mathlib.AlgebraicGeometry.Properties` (def-pc-integral-scheme).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` (def-weil-pbc-normal-ring).
- Proof-only `Mathlib.AlgebraicGeometry.Noetherian` supplies `IsLocallyNoetherian`
  and `LocallyOfFiniteType.isLocallyNoetherian` (pqf-def-locnoeth,
  pqf-lem-locnoeth-lft). The finite-type import supplies the two base-change instances
  of lem-sfb-finite-type-composition-base-change.
- Proof-only `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`:
  `AlgebraicGeometry.regular_normal_and_normal_decomposition`, clause (2)
  (rem-pc-regular-normal). The declaration and complete docstring were read.

Source and edge-case reading:

Read Stacks `properties.tex`, lemma-normal-Noetherian (033M), and the final connected
normal component argument of `more-morphisms.tex`, lemma-local-local-structure-finite-type
(057K). The three-step proof in the theorem docstring records the node's finite-type
Noetherian reduction, clopen normal decomposition and connectedness argument, and arbitrary
extension conclusion, with the dependency node names.

The empty scheme is excluded by the stated nonemptiness hypothesis, and also cannot
satisfy geometric connectedness. `Spec k` is the basic zero-dimensional example. A finite
disjoint union of two rational points has normal base changes but fails geometric
connectedness. Two affine lines meeting at a point may be connected but the intersection
stalk is not a domain; nilpotent thickenings likewise fail the domain condition. K = k,
inseparable extensions, transcendental extensions and every characteristic are included.
The geometric predicates and the explicit normality test use one common arbitrary
universe u, following the recorded dependency's convention.

Searches actually run (via `/home/ubuntu/weil-launcher-all/batch2/msearch.py`):

- LeanFinder: `A finite type geometrically connected scheme with normal local domains
  after every field extension is geometrically integral` returned eight hits: integrality
  definitions, affine criteria, the reduced-plus-irreducible criterion and normalization
  instances. None states this implication.
- Loogle: `"GeometricallyConnected", "GeometricallyIntegral"` returned zero hits.
- Mathlib grep: `normal.*connected|connected.*normal|GeometricallyNormal` in
  `AlgebraicGeometry` returned zero hits.
- LeanSearch: `A finite type geometrically connected geometrically normal scheme over
  a field is geometrically integral` returned eight hits, again integrality definitions
  and reduced-plus-irreducible/affine criteria; no exact statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for geometric integral, geometric
  connected, geometric normal, normal/connected combinations and stalk normality found
  related smooth-family/curve results and the normal decomposition, but no exact match.
  The smooth-component theorem has the additional smoothness and point hypotheses;
  it cannot replace this general geometric-normality implication.
- The item id has no occurrence in `lean/WeilConjectures`. The proposed declaration
  name has no occurrence in Mathlib, WeilConjectures, Sheaf or `dag/lean_names_upstream.json`.

No statement dispute or node fault found. No repair note is present for the item.

Validation: `scompile.py Q45 lem-trf-geonormal-geoconnected-finite-type-integral <file>`
compiled both the sandbox and final module name cleanly (2.5 s and 3.6 s).
The first attempt exposed a scheme-to-type coercion ambiguity at the point binder;
writing `x : ↥(Limits.pullback ...)` fixes it without changing the mathematical statement.
All universe and term variables are explicit; `autoImplicit` is disabled. All lines
are at most 100 characters.

## Second reading by Q45

The dispatcher explicitly prohibits starting other agents; this is a second in-thread
reading, with independent maintainer review still to follow. I reread the complete node
statement against the final signature. Field, scheme over that field, nonemptiness,
locally finite type and quasi-compactness, geometric connectedness, both stalk normal-domain
conjuncts after every extension, and geometric integrality are all present on the same
scheme and structure map. The point binder explicitly coerces the scheme pullback to its
carrier, so it is not accidentally a pullback in Type. Both normality conjuncts refer to
the identical stalk at that point. No regularity, smoothness, separatedness, perfectness,
Noetherian hypothesis or extension restriction has been added. The Noetherian condition
is used only in the source proof, where finite type over a field establishes it.
No mismatch remains and no mathematical statement was changed.
