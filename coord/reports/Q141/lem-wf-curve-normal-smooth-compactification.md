## Worker report

This delivery states `AlgebraicGeometry.exists_smooth_projectiveCompactification_normal` with
one postponed proof. It follows the current main-20261015 blueprint statement and all three
paragraphs of the reviewed DAG proof. No mathematical statement correction is needed.

Hypothesis-by-hypothesis correspondence:

- The arbitrary finite field `k₀ = F_q` is `{K : Type u} [Field K] [Finite K]`. No particular
  presentation or cardinality of the finite field is needed or fixed by this lemma.
- `U₀/k₀` is `{U : Scheme.{u}}` with structure morphism `p : U ⟶ Spec (.of K)`.
- Normality is `hU : ∀ x : U, IsDomain (U.presheaf.stalk x) ∧
  IsIntegrallyClosed (U.presheaf.stalk x)`, the same stalkwise interface used by the recorded
  `IsRegular.of_isIntegrallyClosed_stalk` and the upstream compactification theorem. This does
  not assume integrality in advance: integrality follows from normality and connectedness.
- Geometric connectedness is `[GeometricallyConnected p]`, the Mathlib definition quantified
  over field-valued base changes, as required by def-pc-geometrically-irreducible.
- Separatedness is `[IsSeparated p]`; finite type is `[LocallyOfFiniteType p] [QuasiCompact p]`,
  exactly the convention fixed by def-weil-pbc-scheme-conventions.
- Pure dimension one is `hdim : U.IsPureDimension 1`, using the already landed definition
  `AlgebraicGeometry.Scheme.IsPureDimension` from def-weil-pure-dimension. This existing node
  was added to stmt_deps; its node and module are not changed.

Conclusion clause-by-clause correspondence:

- `Smooth p` is the asserted smoothness of U over the finite field, with no additional relative
  dimension conclusion imposed in the formal statement.
- `∃ (C : Scheme.{u}) (pC : C ⟶ Spec (.of K))` introduces C₀ and its structure morphism.
  `IsSmoothProjectiveCurve pC` uses the dependency's exact existing class: an integral,
  separated finite-type scheme of dimension one, smooth and projective over K.
- `GeometricallyConnected pC` is the separate asserted geometric connectedness of C₀.
- `j : U ⟶ C` and the existential `IsOpenImmersion j` give the open immersion j₀.
  `j ≫ pC = p` makes it a morphism over the specified finite field.
- `DenseRange j.base` says the open image is dense.
- The closed subset `(j.opensRange : Set C)ᶜ` carries its canonical reduced induced structure:
  `Scheme.IdealSheafData.vanishingIdeal` is documented in Mathlib as the ideal cutting out the
  reduced induced subscheme on a closed set. `subschemeι` is the canonical closed immersion
  of its `subscheme`, the same recorded construction used by def-weil-pbc-scheme-reduction.
  The closedness proof is `j.opensRange.isOpen.isClosed_compl`. `IsFinite (...subschemeι ≫ pC)`
  asserts that this actual reduced boundary, with its inherited K-structure, is finite over K.
  There is no arbitrary boundary map or chosen thickening in this formulation.

Dependency declarations and source reading:

- def-weil-pbc-scheme-conventions is a convention-only node with no module or declaration; its
  recorded note delegates the properties to Mathlib. The statement uses `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, and `IsFinite` with those meanings.
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsSmoothProjectiveCurve` and its parent classes `IsIntegralCurve` and
  `IsVariety`. Their complete class declarations and docstrings were read in the published
  read-only source under lean/WeilConjectures.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` and `.Connected`:
  `GeometricallyIntegral`, `GeometricallyIrreducible`, `GeometricallyReduced`, and
  `GeometricallyConnected`. The four definitions and their docstrings were read; only the
  last predicate occurs in this statement.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and its imported `.Basic`:
  `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, `subschemeι`, and `vanishingIdeal`.
  Their definitions and docstrings were read. The reduction of the closed complement is
  represented directly by its radical vanishing ideal, rather than by reducing an arbitrary
  closed thickening.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, read in full. It measures
  every irreducible component with its subspace topology, without imposing nonemptiness.

The proof-plan imports include every recorded proof-dependency module:
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` (`Scheme.normalization`),
`WeilConjectures.AlgebraicGeometry.Regular` (`IsRegular.of_isIntegrallyClosed_stalk`,
`Scheme.normalization_properties`, `smooth_of_isRegular`),
`WeilConjectures.Mathlib.Topology.KrullDimension`
(`IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`),
`WeilConjectures.AlgebraicGeometry.Curve.Compactification` (`IsCurve.exists_projectiveClosure`),
and `Sheaf.AlgebraicGeometry.FiniteOverProjective` (`finite_over_projective_affineLocally`).
These occur as non-public imports; the declaration docstring follows the node's three-step
proof, including the affine-base case of the finite-over-projective result and connectedness
following every field extension.

Edge cases checked: the empty scheme satisfies pure dimension vacuously but cannot satisfy
geometric connectedness over the nonempty field spectrum. Zero-dimensional normal connected
schemes fail the pure-dimension-one hypothesis. A proper U is allowed: j may be an isomorphism,
its complement is empty, its vanishing ideal is the unit ideal, and the empty boundary is
finite over K. The boundary has no nonemptiness assumption. Finite fields of every characteristic
are covered, with no assumption on the prime or extension degree. The field and schemes share
the standard arbitrary universe u; the statement does not restrict fields to Type 0.

Existing-statement searches actually run:

- LeanFinder via msearch.py: query "normal geometrically connected finite type curve over a
  finite field has a smooth projective compactification with reduced finite boundary" returned
  eight Weierstrass-curve declarations, none an exact match.
- LeanSearch via msearch.py: query "normal one dimensional curve over a finite field has a
  smooth projective compactification" returned generic normalization, properness and
  Weierstrass-curve declarations, none an exact match.
- Loogle via msearch.py: query
  "AlgebraicGeometry.IsSmoothProjectiveCurve, AlgebraicGeometry.GeometricallyConnected"
  returned zero hits (unknown identifier AlgebraicGeometry.IsSmoothProjectiveCurve).
- Mathlib grep via msearch.py: `normal.*compactification|projective.*normalization` in
  AlgebraicGeometry returned zero hits.
- Direct rg over Mathlib, WeilConjectures, and lean/Sheaf checked the proposed declaration
  name and searched compactification/normalization terms. The proposed name has no conflict.
  Searching the item's blueprint id in the upstream source found the existing theorem
  `AlgebraicGeometry.exists_smooth_projectiveCompactification` in
  `WeilConjectures.AlgebraicGeometry.Curve.Compactification`. Its full signature and docstring
  were read in both source trees. It already has the same normal-stalk hypotheses, smoothness
  and projective compactification, but concludes only finiteness of the underlying boundary
  set, not finiteness over the field of its reduced subscheme. Thus it is a useful proof
  ingredient, rather than an exact existing binding for this node's full statement.
- The upstream-name index was also searched for `exists_smooth_projectiveCompactification`;
  it gave no match. The actual source search above supplies the declaration independently.

## Second reading by Q141

This is the author's self-check, not an independent second reading. The current workflow
assigns the independent review to the maintainer. Reading the node and final signature together
found two issues in the initial draft: it packaged the hypotheses through IsCurve plus global
dimension, and expressed the boundary existentially. The final signature now uses the landed
pure-dimension predicate, separate separated/finite-type hypotheses, and the canonical reduced
closed complement. Its conclusion states Smooth p exactly. Every hypothesis and conclusion
clause is matched above; no source statement is changed and no new definition is introduced.
