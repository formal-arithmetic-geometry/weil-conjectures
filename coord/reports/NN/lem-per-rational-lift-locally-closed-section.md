## Worker report

The module `Sheaf.AlgebraicGeometry.RationalLiftLocallyClosedSection` states
`AlgebraicGeometry.rationalLift_iff_locallyClosed_section`, with its sole proof `sorry`.
The item's statement and all dependency lists are unchanged; only `lean` is set.
The former module named by `lean_removed` is absent from the current sources, and the
searches below found no surviving equivalent statement. No new notion is introduced.

Source read: ILO, Travaux de Gabber, Exposé II, Proposition 2.2.3, printed p. 27
(PDF page 33). It assumes a locally finite type morphism and a Noetherian base, and
identifies membership in cd(f) with a section over a subscheme containing x. Its proof
extends the generic section over an open of the reduced closure of x. The node's full
five-step affine proof is reproduced in the theorem docstring, including the finite
generator denominator construction and the reverse field-retraction argument.

Clause-by-clause correspondence:

- Schemes X and Y and their morphism: `{X Y : Scheme.{u}}` and `(f : Y ⟶ X)`.
  The universe `u` is explicit and arbitrary; every variable is explicitly bound,
  and `set_option autoImplicit false` enforces this.
- X has a finite affine cover by spectra of Noetherian rings: `[IsNoetherian X]`.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` in
  `Mathlib.AlgebraicGeometry.Noetherian` identifies this class with precisely this
  affine-cover formulation. Its Noetherian ring condition is `IsNoetherianRing`,
  all ideals finitely generated, as recorded by the dependency.
- f is locally of finite type: `[LocallyOfFiniteType f]`, not a finite type or
  quasi-compact hypothesis.
- The arbitrary point x: `(x : X)`.
- Clause (i), a point over x: `∃ y : Y, f y = x ∧ ...`.
- Clause (i), the induced residue map is an isomorphism:
  `IsIso (f.residueFieldMap y)`. This is the actual canonical map
  `X.residueField (f y) ⟶ Y.residueField y`; the preceding equality identifies
  its source point with x. No unrelated isomorphism or arbitrary field map is used.
- The equivalence of (i) and (ii): `↔`.
- Clause (ii), a locally closed subscheme: `∃ (Z : Scheme.{u}) (j : Z ⟶ X),
  IsImmersion j ∧ ...`. Mathlib's `IsImmersion.isImmersion_iff_exists` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion` is exactly factorization as a
  closed immersion followed by an open immersion, the definition in the node.
- Clause (ii), containing x: `x ∈ Set.range j`.
- Clause (ii), a section over that subscheme: `∃ s : Z ⟶ Y, s ≫ f = j`.
  This is f composed with s equals j, in Mathlib's diagrammatic composition order.
- No quasi-compactness or separation assumptions are imposed on Y or f. There are
  no such typeclass assumptions or premises in the signature.

Recorded statement-dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (structure signatures and docstrings read).
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; used through the standard scheme Noetherian
  class and its finite affine cover characterization, whose signatures were read.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its all-affine-pairs signature
  and docstring were read.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`; both complete definitions and docstrings read.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; the dependency's
  `mathlib_match` explicitly also supplies `AlgebraicGeometry.IsImmersion` and
  `IsImmersion.isImmersion_iff_exists` in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
  All these complete signatures and docstrings were read. No dependency repair is needed.

Public imports expose these statement notions. The stated proof dependencies are
available through the Mathlib imports and the private imports of
`Mathlib.RingTheory.Localization.Away.Basic`,
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, and
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`; the latter's recorded
`Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion` was read in full.

Edge cases checked before writing: an empty X has no point x to instantiate, so
nothing is excluded; when Y is empty both conditions fail for a point x; an empty Z
cannot satisfy range membership. The identity f has both conditions for every x.
Closed x and non-locally-closed generic points are allowed: Z is not required to be
{x}, open in X, reduced, affine, or a neighborhood of x in X. Nonreduced X and
nonseparated or non-quasi-compact Y are admitted. No characteristic restrictions or
nonemptiness assumptions occur. The proof uses d = 1 when B has no generators.

Searches actually run (2026-10-24):

- `msearch.py ... leansearch "rational lift locally closed subscheme section locally
  finite type morphism"`: 8 hits on locally finite type definitions and related
  instances, no equivalence.
- `msearch.py ... leanfinder "A rational lift for a locally finite type morphism over
  a Noetherian scheme exists if and only if a section exists on a locally closed
  subscheme through the point"`: 8 hits, notably
  `AlgebraicGeometry.spread_out_of_isGermInjective'` and rational/partial map
  constructions. Its complete signature and docstring were read: it extends a
  morphism from a stalk under a germ-injectivity hypothesis; it does not state this
  residue-field/loci equivalence.
- `msearch.py ... loogle "AlgebraicGeometry.IsImmersion,
  AlgebraicGeometry.Scheme.Hom.residueFieldMap"`: 0 hits.
- `msearch.py ... grep
  "rationalLift|locallyClosed.*section|section.*locallyClosed|spread_out_of_isGermInjective"
  AlgebraicGeometry`: 9 hits, all spreading-out and its rational-map uses, no match.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `rationalLift_iff_locallyClosed_section|rational.*[Ll]ift|locallyClosed.*section|locally.closed.*section`:
  only unrelated rational lifts and locally closed stratifications; no duplicate.
- `rg -n "lem-per-rational-lift-locally-closed-section" lean/WeilConjectures`:
  no hits.

Validation: prescribed `scompile.py NN lem-per-rational-lift-locally-closed-section`
compiled this file in sandbox mode and at its library module name on the server,
1.4 seconds each, exit 0, no errors or unexpected warnings. All lines are at most
100 characters. No statement dispute, node fault, new node, or dependency module.

## Second reading by NN

A second pass by the same worker compared the opened node with the finished Lean
signature and the source passage. (The dispatcher explicitly forbids starting other
agents; independent review belongs to the maintainer.) Both directions use the same
objects; the residue-field condition is on the map induced by f, and the right side
requires both immersion and range membership as well as the commuting morphism s.
The Noetherian cover hypothesis agrees with Mathlib's characterization, while no
finite type strengthening or separation condition has slipped in. The equality
f y = x only identifies the residue-field source; it does not impose equality of
untransported field objects. No mismatch was found and no correction was made.
