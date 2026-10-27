## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicResidueClosedPoint` states
`AlgebraicGeometry.Scheme.Hom.isClosed_singleton_of_isAlgebraic_residueField`.
Its only theorem has proof `sorry`; it introduces no definitions or helper nodes.
The node copy changes only `lean`.

Source checked: `literature/stacks-project/morphisms.tex`, lines 3564–3598,
`lemma-algebraic-residue-field-extension-closed-point-fibre` (Stacks 01TE), part (2).
The source allows an arbitrary scheme morphism and an algebraic, potentially infinite,
residue extension. The node's affine-specialization proof is recorded step by step in
the declaration docstring, including the polynomial formula for inverses.

Hypotheses and conclusion, clause by clause:

- Arbitrary schemes Y and S: `{Y S : Scheme.{u}}`, with explicit universe `u`.
- Arbitrary scheme morphism f: `(f : Y ⟶ S)`.
- A point y of Y: `(y : Y)`; the source point s is written directly as `f y`.
- Induced homomorphism κ(s) → κ(y): `(f.residueFieldMap y).hom`.
  Its `RingHom.toAlgebra` is passed explicitly to `@Algebra.IsAlgebraic`, ensuring
  that algebraicity refers to this exact homomorphism, rather than an arbitrary algebra.
- Closedness of {s}: `(hs : IsClosed ({f y} : Set S))`.
- Every element of κ(y) is a root of a nonzero polynomial over κ(s):
  `(halg : @Algebra.IsAlgebraic (S.residueField (f y)) (Y.residueField y) _ _
  (f.residueFieldMap y).hom.toAlgebra)`.
  `Algebra.IsAlgebraic.isAlgebraic` quantifies over every element, and `IsAlgebraic`
  is exactly `∃ p, p ≠ 0 ∧ Polynomial.aeval a p = 0`.
- Conclusion that {y} is closed: `IsClosed ({y} : Set Y)`.
- No local finite type, quasi-compactness, separatedness or Noetherian conditions:
  there are no such binders or instances. There is no restriction on characteristic,
  finiteness of the residue extension, reducedness or irreducibility.

Statement dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`, reexported by the public residue-field import.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, from `Mathlib.AlgebraicGeometry.ResidueField`.
  The latter is induced by `IsLocalRing.ResidueField.map (f.stalkMap y).hom`.
- `def-weil-algebraic-element`: `IsAlgebraic` and `Algebra.IsAlgebraic`, from
  `Mathlib.RingTheory.Algebraic.Defs`.
- `def-pc-field-extension`: `Algebra` and `RingHom.toAlgebra`, from
  `Mathlib.Algebra.Algebra.Defs`, available through the public imports.

The already stated proof dependencies are retained as plain imports:
`Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.isBasis_affineOpens`),
`Mathlib.RingTheory.Spectrum.Prime.Topology` (`PrimeSpectrum.closure_singleton`,
`PrimeSpectrum.pointsEquivIrreducibleCloseds`), `Mathlib.RingTheory.Ideal.Maximal`
(`Ideal.exists_le_maximal`), and
`WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`
(`spec_field_point_residue_field` and its affine-open/map/generic companions).
`def-weil-affine-spectrum` uses `AlgebraicGeometry.Spec` from the scheme module.
The residue-field and algebraicity proof dependencies are already public imports.

Edge cases checked before writing:

- Empty Y admits no y, so the quantification is vacuous. Empty S admits no morphism
  from a scheme with the supplied point. No nonemptiness assumption was added.
- For Spec L → Spec k with any algebraic extension L/k, including an infinite one,
  both point sets are singletons. Algebraicity does not impose finite type.
- Identity maps show closedness of the image cannot be omitted: the generic point
  of the spectrum of a DVR is not closed, although its identity residue map is algebraic.
- The generic point of the affine line over k maps to the closed point of Spec k
  but has residue field k(t); its transcendence explains why algebraicity is necessary.
- The affine-local specialization argument does not require separatedness or a
  Noetherian hypothesis. No finite-dimensionality or finite-generation surrogate is used.
- Zero and nonzero elements are both included in `Algebra.IsAlgebraic`; the inverse
  argument uses only nonzero elements, as the proof docstring specifies.

Searches actually run:

- `msearch.py ... leanfinder`: “For any scheme morphism a point with algebraic
  residue field over a closed image point is closed without finite type hypotheses”.
  Eight hits, including `isClosed_singleton_iff_isClosedImmersion`,
  `IsClosedImmersion.Spec_map_residue`, and
  `isClosed_singleton_iff_locallyOfFiniteType`. None states this criterion.
- `msearch.py ... loogle`: `"IsAlgebraic", "AlgebraicGeometry"`: zero hits.
- `msearch.py ... leansearch`: “A point of a scheme is closed if its image is closed
  and its induced residue field extension is algebraic”. Eight hits, primarily
  closed-point definitions and closed-immersion criteria; no exact match.
- `msearch.py ... grep` in AlgebraicGeometry:
  `IsAlgebraic|algebraic.*closed|closed.*algebraic`: 25 hits, no exact criterion.
- `rg` across both `lean/WeilConjectures` and `lean/Sheaf`, including algebraicity,
  residue-field closedness and the exact item id. The only relevant upstream theorem
  was `Scheme.Hom.isClosed_singleton_iff_isAlgebraic_residueField` in
  `WeilConjectures.AlgebraicGeometry.ClosedPointResidueField`; its full signature was
  read and requires a locally finite type morphism to a field spectrum. It is not
  the arbitrary-scheme theorem of this node. The Sheaf decent-space consumer only
  mentions this item in its proof docstring and does not declare the scheme result.
- Exact proposed declaration names searched in Mathlib and both project source trees:
  no collision found. `dag/lean_names_upstream.json` was included in the concept search.

No statement correction, disputed statement, missing notion, or dependency repair is needed.

## Second reading by Q14

The worker reread the node, source and final signature against the mapping above.
The explicit algebra argument fixes the structural map to the residue-field map;
`hs` concerns the image singleton in S, and the conclusion concerns the original
singleton in Y. The single universe is Mathlib's scheme-category universe, with no
extra equality of site or coefficient universes. No mismatch or extra hypothesis
was found. This is a worker self-check, not a claimed independent-agent review;
the dispatch brief prohibits starting agents and assigns independent review to the
maintainer after delivery.

Validation: the prescribed `scompile.py Q14 lem-sfb-scheme-algebraic-residue-closed-point`
compiled the delivered file both as sandbox and library module in 1.3 seconds each,
with exit status 0 and no unexpected warnings.
