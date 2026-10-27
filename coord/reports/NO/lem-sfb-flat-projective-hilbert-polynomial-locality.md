## Worker report

The module `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality` states
`AlgebraicGeometry.ProjectiveHilbertPolynomial.flat_projective_hilbert_polynomial_locality`
and `projective_field_hilbert_polynomial`. Both proofs are `sorry`. Every helper has real
data. No mathematical statement or proof of the DAG node was changed.

Hypothesis and clause correspondence:

- Any scheme T and closed subscheme Z: `{T Z : Scheme.{u}}` and
  `(i : Z ⟶ RelativeProjectiveSpace.scheme T n) [IsClosedImmersion i]`.
- The integer n is nonnegative: `(n : ℕ)`. Coordinates are `ULift.{u} (Fin (n + 1))`,
  keeping n=0 and all scheme universes.
- The structural morphism is exactly `i ≫ RelativeProjectiveSpace.π T n`.
  Its flatness is the `Flat` instance on that composite. Its finite presentation is the
  three separately written instances `LocallyOfFinitePresentation`, `QuasiCompact`,
  and `QuasiSeparated`. No Noetherian, reducedness, connectedness, or nonemptiness
  assumption appears.
- `geometricPoint T t` is the composite of Spec of the algebra map into
  `AlgebraicClosure (T.residueField t)` and `T.fromSpecResidueField t`.
  `baseChangeEmbedding` is the map induced by the projective-space pullback universal
  property, with the actual pullback projections; no arbitrary map is substituted.
- The conclusion supplies an isomorphism `e` over T from the relative-Proj space to the
  upstream projective-space model. This is a witness identifying the two presentations of
  the ambient projective space, not a new hypothesis, a selected undefined construction,
  or a replacement of the relative-Proj input. The standard affine polynomial charts
  identify these models. Composing i with e transports the same embedded scheme.
  Isomorphisms over a field between projective spaces preserve O(1), hence preserve the
  coordinate Hilbert polynomial. There is no arbitrary morphism or extra polarization in
  this interface. The added statement dependency `def-nagata-projective-space-base-change`
  records the already landed second presentation.
- The homogeneous degree-d equations are the polynomials whose dehomogenization on
  every standard chart restricts to zero on Z. `equations` takes the span of precisely
  that subset of `MvPolynomial.homogeneousSubmodule ... k d`. This subset is already a
  submodule: chart evaluation is additive and k-linear. Thus taking its span adds no
  equations. `coordinatePiece` is its quotient, the degree-d homogeneous piece of the
  saturated coordinate ring; `coordinateDimension` is its actual `Module.finrank`.
  Saturated versus unsaturated defining ideals have the same eventual dimensions,
  as in the recorded coordinate-ring/Euler comparison proof dependency. This uses the
  canonical chartwise vanishing notion of the homogeneous-ideal node, not an arbitrary
  ideal or a chosen presentation with unknown data.
- `IsCoordinatePolynomial ... Q` is `∀ᶠ d : ℕ in atTop, Q.eval (d : ℚ) = ...`.
  For each t, `∀ Q, IsCoordinatePolynomial ... Q ↔ Q = P t` states existence and
  uniqueness: instantiate Q with P t for existence, and use the forward implication for
  uniqueness. Nothing chooses a polynomial before proving existence.
- Numerical: `∀ d : ℤ, ∃ z : ℤ, (P t).eval (d : ℚ) = (z : ℚ)`.
- Degree bound: `(P t) ≠ 0 → (P t).natDegree ≤ n`.
- Euler characterization at every integer: the next conjunct states evaluation equals
  `twistEuler ... d`. That definition uses the recorded `Scheme.Modules.tensorPullback`
  applied to the recorded `ProjectiveSpace.twist`, with `Scheme.Modules.eulerChar` and
  the structural morphism induced by the embedding. Its local instance is inside the
  definition and specifies this structural morphism explicitly; no file-local instance
  changes the meaning of any signature.
- Local constancy: `IsLocallyConstant P`.
- Arbitrary base change: the final universal quantifier allows every scheme T', every
  morphism h:T'→T and every t'. The coordinate-polynomial predicate is applied to
  `baseChangeEmbedding n (baseChangeEmbedding n (i ≫ e.hom) h)
  (geometricPoint T' t')`, which is the iterated pullback requested in the node, and
  identifies its unique polynomial with `P (h t')`. No embedding between chosen algebraic
  closures is assumed.
- Empty fibres: `P t = 0 ↔ IsEmpty ↥(pullback ... (geometricPoint T t))`. This explicitly
  includes the empty total scheme. The over-isomorphism equality identifies its structural
  composite with the original structural morphism.
- The final general field clause is also stated separately in
  `projective_field_hilbert_polynomial`: for every field k and every closed projective
  embedding it supplies the unique coordinate polynomial, its numerical/Euler/degree
  properties, and `P = 0 ↔ IsEmpty X`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, with the standard `QuasiCompact` and `QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`: `RelativeProjectiveSpace.scheme`
  and `RelativeProjectiveSpace.π`, retaining the recorded relative-Proj construction.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`,
  `ProjectiveSpace.liftBaseChange`; this is the added landed definition dependency.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`; the field embedding uses Mathlib's `AlgebraicClosure`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.condition`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback` by its public import of the existing construction.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`: `Scheme.Modules.eulerChar`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial`:
  `ProjectiveSpace.chartRingEquiv`; `MvPolynomial.dehomogenizeX` is the existing upstream
  dehomogenization. These give the literal F/z_i^d functions for homogeneous F.
- The Proj construction is Mathlib's recorded `AlgebraicGeometry.Proj`, with its standard
  opens. It is used in the proof plan, not replaced by a second Proj construction.

Proof-only imports include the recorded modules for projective morphisms, projective
properness, Snapper's numerical polynomial, coherent modules on locally Noetherian schemes,
and Mathlib's Noetherian and quasi-compactness results. The three proof dependencies
`lem-sfb-projective-closed-subscheme-homogeneous-ideal`,
`lem-sfb-projective-coordinate-ring-euler-polynomial`, and
`lem-sfb-proper-flat-sheaf-euler-local-constancy` have no recorded Lean declaration in the
read clone and supply no objects needed in the signatures; their full statements and proof
roles are documented in the theorem docstring. Their later modules can be imported once
they are stated. No downstream theorem is assumed as a hypothesis.

Edge cases checked before writing: n=0 gives one coordinate and a degree-zero polynomial;
the empty embedded scheme makes every homogeneous equation vanish, so the coordinate
quotients are zero; a nonreduced point can have positive length and is not declared empty;
T and T' can be empty, nonreduced, non-Noetherian, disconnected or non-quasi-compact;
arbitrary h includes identity maps and arbitrary field extensions; integer twists include
negative d; zero polynomials are included without relying on the natDegree of zero.

Searches made:

- msearch.py LeanFinder, query `Hilbert polynomial flat projective family locally constant
  arbitrary base change`: eight hits, including flatness/base-change instances, module
  projectivity and properness of Proj, with no family Hilbert-polynomial theorem.
- msearch.py Loogle, query `"hilbertPoly"`: twelve hits from
  `Mathlib.RingTheory.Polynomial.HilbertPoly`, concerning polynomials attached to rational
  power series. None is the scheme-family statement.
- msearch.py grep, query `hilbertPolynomial|HilbertPolynomial|eulerChar` in
  `AlgebraicGeometry`: no Mathlib hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for Hilbert-polynomial names, the item id,
  coordinate rings, relative projective spaces, and the new declaration names. No complete
  item-level match. Existing Modules.HilbertPolynomial and Modules.Ample concern individual
  proper schemes and their Euler polynomials, without this family-locality/base-change
  theorem. The coordinate-chart, twist, pullback and Euler declarations above were reused.

Sources read: perfect.tex, Tag 0B9T, including both clauses; varieties.tex, Tags 08AC and
08AE, with the Euler-characteristic definition between them. All definitions use existing
Mathlib/project definitions where present. The auxiliary coordinate functions are explicit
parts of the notion stated by this item and are listed in `lean.declarations`, each with
the owning blueprint tag. No new independent notion, no dependency repair, no statement
correction, and no STATEMENT-DISPUTED finding.

Validation: the module compiled separately as sandbox and library on the live server with
the prescribed scompile.py, without errors or warnings. An initial elaboration error in
the empty-fibre clause was repaired by explicitly coercing the scheme to its point type.
The final single-file compile took under three seconds in each mode.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
