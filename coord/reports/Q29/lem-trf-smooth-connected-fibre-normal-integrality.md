## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothConnectedFibreNormalIntegrality` states
`AlgebraicGeometry.smooth_connected_fibre_normal_integrality`, with its sole proof `sorry`.
It states precisely the assigned node; no definitions, helper nodes, dependency repairs,
or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes and morphism `v : V → B`: `{V B : Scheme.{u}} (v : V ⟶ B)`.
- Smoothness: `[Smooth v]`, the dependency's Mathlib notion.
- Every residue fibre geometrically connected: `hconn : ∀ t : B,
  GeometricallyConnected (v.fiberToSpecResidueField t)`. Mathlib's `v.fiber t` is
  definitionally `pullback v (B.fromSpecResidueField t)`, and
  `v.fiberToSpecResidueField t` is its second projection. Thus this is exactly the
  hypothesis about `V_t → Spec κ(t)`, rather than about the total space.
- Connected includes nonempty: Mathlib `GeometricallyConnected` uses `ConnectedSpace`,
  whose `toNonempty` field explicitly requires nonemptiness. In particular the identity
  field extension rules out an empty residue fibre.
- Every point and every field extension: `(t : B) (K : Type u) [Field K]
  [Algebra (B.residueField t) K]`. The algebra map is the specified field embedding.
  All scheme and field universes are bound explicitly, in the standard common-universe
  convention of the recorded geometric-connectedness and base-change interfaces.
- The actual scheme `C = V_t ×_{Spec κ(t)} Spec K`: every occurrence is
  `pullback (C := Scheme.{u}) (v.fiberToSpecResidueField t)
  (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField t) K)))`.
  The explicit category argument ensures the point binder is a point of the scheme
  pullback, not a pullback in `Type`.
- Integral scheme: the first conjunct `IsIntegral` of exactly this pullback.
- Every local ring is a domain: `∀ x` of the same pullback, `IsDomain (...presheaf.stalk x)`.
- Integrally closed in its fraction field: the second stalk conjunct
  `IsIntegrallyClosed (...presheaf.stalk x)`, Mathlib's integral closedness in `FractionRing`.
- No quasi-compactness, separatedness, Noetherianity or normality of `B` or `V` is
  assumed: there are no corresponding binders or bundled hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.snd` (def-pc-fibre-product).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField` (def-weil-residue-field).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`, the chosen fibre and projection used by the
  recorded `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` module
  (def-pc-base-change). That recorded module is publicly imported, with no new base change.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: the recorded module for
  def-pc-geometrically-irreducible is publicly imported. Its connectedness clause is
  the existing `AlgebraicGeometry.GeometricallyConnected` in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`, also publicly imported as the
  dependency's note requests. Its definition and
  `GeometricallyConnected.iff_geometricallyConnected_fiber` were read.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` including `toNonempty`
  (def-weil-connected-scheme, a Mathlib leaf).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap` (def-pc-field-extension).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (def-pc-integral-scheme).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `Mathlib.Algebra.Ring.Defs`: `IsDomain` (normal-domain clause of
  def-weil-pbc-normal-ring, using the recorded inline conjunction).

Proof-only imports preserve the DAG route:
`Mathlib.AlgebraicGeometry.Morphisms.Proper` for
`IsProper.isStableUnderBaseChange` (lem-pc-proper-base-change; its smooth clause is
`smooth_isStableUnderBaseChange` in the already public Smooth module), and
`WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore` for
`AlgebraicGeometry.Scheme.smooth_connected_generic_geometry_core`.
The latter declaration, its full signature and docstring were read. The theorem
applies over the normal integral one-point scheme `Spec K` after two smooth base changes,
field-extension pullback pasting, and nonemptiness from connectedness. Its total-space
conclusions give integral closedness and integrality; domain stalks follow from integrality.
This three-step argument is retained in the theorem's docstring.

Sources read locally: `literature/stacks-project/more-morphisms.tex`,
`lemma-normal-morphism-irreducible` (Tag 057J), including its final geometric-fibre
argument; `varieties.tex`, `lemma-smooth-geometrically-normal` (056T);
`properties.tex`, `lemma-normal-Noetherian` (033M) and the adjacent locally Noetherian
version. Smoothness over the field gives local Noetherianity without a finiteness
assumption on the whole fibre. No global Noetherianity is introduced.

Edge cases checked before writing: an empty base admits no `t`, so the assertion is
vacuous; an empty total space over a nonempty base violates `hconn` through the
nonempty-connectedness convention. The extension `K = κ(t)` with its identity algebra
is allowed. No finite, algebraic, separable or perfect-field restriction is present;
positive characteristic and transcendental extensions are covered. Nonquasicompact and
nonseparated smooth schemes are covered; the normal-integral geometry core used here
explicitly requires neither condition.

Searches actually run (via the prescribed `batch2/msearch.py Q29 <item>`):

- `leanfinder`, query `A smooth morphism with geometrically connected fibres has integral
  fibres with integrally closed local rings after every residue field extension`:
  eight hits, including `AlgebraicGeometry.IsIntegral` and integral-morphism/normalization
  declarations; none states the assigned theorem.
- `loogle`, query `"Smooth", "IsIntegrallyClosed"`: zero hits.
- `grep`, query `smooth.*normal|normal.*smooth|of_smooth_of_geometricallyConnected`,
  subdirectory `AlgebraicGeometry`: four hits, all in `Normalization.lean`, about
  normalization commuting with smooth base change, not this statement.
- `leansearch`, query `Every field extension of a geometrically connected fibre of a
  smooth scheme morphism is integral and has integrally closed local rings`: eight
  hits; integral closures, integral ring extensions, germ injectivity and
  `Field.instIsIntegrallyClosed`, not the assigned statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `of_smooth_of_geometricallyConnected|smooth.*[Ii]ntegral|smooth.*[Nn]ormal|geometricallyConnected.*[Ii]ntegral`:
  found the general smooth-connected-generic geometry core and smooth-geometrically-normal
  results. The former has an integral normal base, a nonempty total space and an explicit
  generic fibre; the latter gives normal stalks and reducedness without integrality.
  Neither is the assigned all-residue-fibres theorem. Reused their existing notions
  and imported the core as the prescribed proof dependency.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no hits.
- `rg` for `smooth_connected_fibre_normal_integrality` in Mathlib, WeilConjectures and
  Sheaf: no hits, so the declaration name is new.

No mathematical node fault or disputed statement was found. The original node is
preserved outside `lean`. The local CompactObject example is withdrawn; its recorded
upstream replacement was read for the module conventions.

## Second reading by Q29

A separate rereading pass by this worker checked the node and final Lean signature;
no second agent was started, as instructed by the dispatcher. The maintainer's
independent reading remains the delivery review.

The schemes, morphism and smoothness appear as the first binders; `hconn` explicitly
quantifies over every residue fibre, and the two next binders quantify over every
point and field extension. The pullback uses the residue-fibre projection, giving
exactly the two-stage object in the node. The first conclusion is `IsIntegral C`;
the second is `∀ x : C, IsDomain (O_C,x) ∧ IsIntegrallyClosed (O_C,x)`. Both occurrences
of the stalk use the same `x` in the same chosen scheme. Connectedness uses nonempty
`ConnectedSpace`, and identity extensions and the empty-base case remain included.
No hidden section variables, local notation, additional scheme properties or helper
constructions occur. The first compiler pass found only category inference in the
point binder; adding explicit `(C := Scheme.{u})` repaired it without changing meaning.

Validation: the final file compiled cleanly through `scompile.py`, both as the
sandbox probe and under its actual library module name, with no warnings or errors.
Every line is at most 97 characters; the node differs from the read-only source only
in `lean`, whose signature is copied verbatim from the final theorem.
