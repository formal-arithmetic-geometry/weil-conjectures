## Worker report

The delivery states `AlgebraicGeometry.existsUnique_factor_through_point_blowup` in
`Sheaf.AlgebraicGeometry.PointBlowdownFactorization`. Its only proof is `sorry`.
There are no new definitions, dependency repairs, or statement corrections.
The existing Q07 review and merge concern the stage-1 split, not a Lean attachment:
the assigned node has no `lean` record on the read base. Thus this delivery supplies
its first Lean statement rather than re-recording the stage-1 result.

Hypothesis and conclusion correspondence:

- The scheme T is `(T : Scheme.{u})`.
- Noetherian means locally Noetherian and quasi-compact. The first conjunct of
  `hregular : IsRegularScheme T` is `IsLocallyNoetherian T`; `[CompactSpace T]`
  supplies quasi-compactness of the underlying space. No topological Noetherianity
  is substituted for locally Noetherianity.
- Regularity is the second conjunct of the same recorded predicate, the upstream
  `IsRegular T` asserting regular local stalk rings at every point. Thus every
  part of `IsRegularScheme` is accounted for without an additional hypothesis.
- Dimension exactly two is `(hdim : topologicalKrullDim T = 2)`, with Mathlib's
  extended-natural Krull dimension, not a local-dimension or equidimensionality
  condition.
- The closed point is `(x : T) (hx : IsClosed ({x} : Set T))`. The centre is
  `Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`. This is the actual radical
  quasi-coherent vanishing ideal of the closed singleton, so its closed subscheme
  is the reduced point, not an unspecified thickening or an arbitrary ideal with
  singleton support. The same expression is already used upstream in
  `WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint`.
- W and b are exactly this ideal's recorded `.blowup` and `.blowupMap` from
  `WeilConjectures.Blowup.Gluing`; they are written directly rather than supplied
  as arbitrary schemes or morphisms.
- The arbitrary target and morphism are `(Z : Scheme.{u})` and
  `(f : (...).blowup ⟶ Z)`. No separation, finite-type, reducedness, or base
  condition is imposed on Z.
- The exceptional fibre E is the topological inverse image
  `(...).blowupMap ⁻¹' {x}`. Its topological image is exactly one point:
  `himage : ∃ z : Z, f '' (...) = {z}`. This encodes both nonemptiness and
  constancy, as the node requires. Merely saying the image is subsingleton would
  incorrectly include the empty fibre.
- Existence, uniqueness, and the factorization identity are together
  `∃! g : T ⟶ Z, (...).blowupMap ≫ g = f`.
  Category composition `b ≫ g` is the node's `gb`.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`, asserting Noetherian coordinate rings
  on every affine open. Available through `IsRegularScheme`'s public import.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`, defined as
  `IsLocallyNoetherian X ∧ IsRegular X`; the latter class is read in
  `WeilConjectures.AlgebraicGeometry.Regular`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, the Krull dimension of `IrreducibleCloseds`.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, the glued affine blowup;
  `.blowupMap` is the corresponding structure morphism in that same module.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `.Hom`, the latter morphisms of underlying
  locally ringed spaces. Available through the public imports.
- The closed-point ideal uses Mathlib's existing
  `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, read in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` (imported by the blowup API).

The stated proof dependencies are imported without `public`:
`WeilConjectures.Blowup.Complement` (the complement-isomorphism theorem),
`WeilConjectures.Blowup.Proper` (properness for finite-generation on affine opens,
which also imports the proper-morphism definition), and
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (ringed-space morphisms and local
stalk maps). `lem-sfb-regular-point-blowup-functions` has no recorded Lean
statement on the read base; it is retained in the proof docstring, not invented
as an extra assumption. It is a proof input, not a notion needed to type this
statement. The module docstring cites Stacks resolve.tex Tag 0C5J, whose lemma
and proof were read in full. The declaration docstring reproduces all five
steps of the node's proof, including the canonical structure-sheaf isomorphism,
quotient topology, construction on opens, locality on stalks, and uniqueness.

Edge cases checked before writing:

- T empty is excluded by the bound point x and by dimension two.
- T can be disconnected, nonintegral, and non-equidimensional. In particular x
  need not have local dimension two: no such restriction is imposed.
- On a dimension-one regular component the reduced point is Cartier and the
  blowup is the identity. The factorization statement includes this case.
- On a dimension-zero component the blowup can remove that component and its
  exceptional fibre is empty. The singleton-image equality then has no witness,
  as required by the literal assertion that the image is one point. Replacing
  equality with pairwise constancy would have made the statement false here.
- The usual affine-plane point blowup has nonempty exceptional projective line;
  the stated hypothesis is constancy on its actual entire fibre.
- Z may be empty or nonseparated and z may be nonclosed: the formula adds no
  restrictions. An empty Z admits no witness to `himage`.
- All schemes and the actual blowup are in arbitrary `Scheme.{u}`, the existing
  category's universe convention; there are no independent test-object universe
  quantifiers or dimension bounds on individual components.

Searches actually run:

- `msearch.py leanfinder`: “A morphism constant on the exceptional fibre of a
  regular surface point blowup factors uniquely through the blowdown”. Eight
  hits concern open-immersion lifts, valuative criteria, rational maps,
  normalization, and equality along dominant maps; none matches the item.
- `msearch.py leansearch`: “A morphism from the blowup of a regular surface
  constant on the exceptional fibre factors uniquely through the blowdown”.
  Eight results: empty-source uniqueness, general regular-epimorphism uniqueness,
  valuative uniqueness, normalization factorization, and presheafed-space
  constructors; none states this point-blowup result.
- `msearch.py loogle` with `AlgebraicGeometry.Scheme.IdealSheafData.blowup,
  ExistsUnique` returned zero results and reported the project declaration
  unknown to Loogle; no match was inferred from that service's limitation.
- `msearch.py grep` with `blowdown|factor.*contract|constant.*exceptional` in
  Mathlib AlgebraicGeometry returned zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `blowdown|factor.*contract|lem-sfb-point-blowdown-factorization` found no item
  declaration. Relevant hits concern exceptional contractions of marked curves
  over valuation rings (`ValuationExceptionalBlowdown`,
  `ExceptionalContractionDiamond`) and have different hypotheses and conclusions;
  the displayed theorem signatures and docstrings were read.
- `rg` for singleton vanishing ideals and point ideals found the existing
  Mathlib construction and the upstream `Curve.ClosedPoint` use. The statement
  uses that construction without defining a second point ideal.

No STATEMENT-DISPUTED flag or node fault was found. The retained mathematical
statement is verbatim. The stage-1 merge was not evidence of a stage-2 delivery.

## Validation

Every compile is through `scompile.py` against the live published library.
Server compile and required delivery dry-run outcomes are recorded below after
completion. The maintainer supplies the independent review under the dispatch
brief; no independent second reading is claimed here.

`scompile.py` passed: sandbox elaboration 7.5 s and library module 5.3 s;
no errors or warnings were reported.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
