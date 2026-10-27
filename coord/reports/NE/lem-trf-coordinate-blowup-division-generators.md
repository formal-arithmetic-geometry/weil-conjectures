## Worker report

The module `Sheaf.RingTheory.CoordinateBlowupDivisionGenerators` states
`MonomialDiagram.coordinate_blowup_division_generators` with a single `sorry`.
`CoordinateSupportedGeneration` packages the supported-generation hypothesis;
`CoordinateBlowupDivisionProperties` packages exactly the uniqueness, order estimate,
regularity and two generator conclusions. Both are fully written Prop definitions,
not new independent mathematical objects. Their names are listed in `lean.declarations`.
No statement correction, new node, or dependency repair is made.

Hypothesis-by-hypothesis correspondence:

- The arbitrary characteristic-zero coefficient field is `{L : Type u} [Field L]
  [CharZero L]`. `n s : ℕ` allow every number of variables and every finite generator
  family, including zero. The ring A and the target ring B are two roles of the same
  `MvPowerSeries (Fin n) L` carrier, with different coordinate interpretation.
- The ordered orthant vertices are `α : Fin s → Fin n →₀ ℕ` and
  `hα : IsOrderedVertexFamily (generated α) α`. This means exactly the minimal
  vertices of their union of orthants in ascending degree-lex order. It imposes no
  monotonicity and no essential-variable hypothesis. This is the ordered-vertex
  convention of BM (7.1), printed p.261. `generated α` is D,
  `(α i).degree` is d_i, and `quotientSupport α i` is Δ_i.
- The ideal and its chosen elements are `I`, `F`, and `hmem`.
  `horder` is total order exactly d_i, so it also excludes a zero generator.
- `hdivision` is `HasUniqueDivision (generated α) α H t` for every degree t.
  Here H is `truncTotal (d_i + 1) (homogeneousComponent d_i (F i))`.
  A homogeneous degree-d_i series is a polynomial, so truncating through d_i
  is exactly its full initial homogeneous form, not an approximation.
  The existing `DivisionIndex`, `divisionFamily`, and `HasUniqueDivision` retain
  the indexed quotient supports and complementary remainder monomials, including
  degrees below d_i. They assert existence and uniqueness, not just spanning.
- `hgen : CoordinateSupportedGeneration α I F` says for every f in I there is a
  finite expansion f = sum q_i F_i and every nonzero coefficient of q_i has
  exponent in `quotientSupport α i`. No arbitrary division operator is assumed.
- `J : Finset (Fin n)` and `hJ : J.Nonempty` are the nonempty coordinate center.
  Its order is rendered by `weightedOrder (fun j ↦ if j ∈ J then 1 else 0)`.
  This is the minimum J-degree of a nonzero monomial, infinity at zero. It equals
  sup {v : f ∈ (X_j : j ∈ J)^v}: membership in that finitely generated monomial
  ideal power says exactly that all coefficients of J-degree less than v vanish.
  Thus the weight convention is exactly the specified P-adic order, with no
  changed filtration. `hP` says this order of F_i is exactly d_i.

Conclusion-by-conclusion correspondence (unfold the conclusion Prop):

- Every f in I has a unique supported quotient family (`∃! q`), including f=0.
- For every nonzero f in I and every supported expansion, each i satisfies
  `ord_P f ≤ ord_P (q i) + (α i).degree`. Since ord_P f is finite this is
  exactly `ord_P (q i) ≥ max(0,v-d_i)` (or the equivalent integer lower bound
  in the node). Zero quotients retain infinite order. There is no weakening to
  a different filtration or only a chosen expansion.
- Every chart h in J and every direction ξ is quantified. ξ is a function on
  all coordinates for convenient notation, but its values at h and outside J
  never appear in the formula. Thus this is exactly arbitrary scalars on J\{h}.
- The actual `MvPowerSeries.subst` family is X_h at h, X_h*(C(ξ_j)+X_j) at the
  other coordinates in J, and X_j outside J. Every substituted variable has
  zero constant coefficient, and the variable set is finite, so Mathlib's
  `HasSubst` condition holds without an added hypothesis. This is the continuous
  homomorphism σ*, not an arbitrary map (or the dummy branch of subst).
- `∃ G` with `X h ^ d_i * G i = subst ... (F i)` states regularity of every
  displayed divided generator. Multiplication by X_h^d_i is injective by
  coefficient shifting over the field, so G is uniquely the requested quotient.
  No construction is chosen from an undetermined existence theorem.
- For each nonzero f in I, `∃ g` with `X h ^ (ord_P f).toNat * g = subst ... f`
  asserts the regular individual transform. `toNat` is used only for a nonzero
  series and hence a finite order; it is never used to divide the zero series.
- The membership equivalence for every g is exactly
  `g ∈ (σ*I)B:e^∞ ↔ g ∈ Ideal.span (Set.range G)`. The left is the node's
  definition `∃ m : ℕ, e^m*g ∈ Ideal.span (subst ... '' ↑I)`; extension of
  the image ideal is precisely this span. No radical or reduced transform occurs.
- The last equality identifies that same finite span with the ideal spanned by
  all individual transforms of all nonzero f in I. Thus both the individual
  generator assertion and the finite family assertion are present.
- The theorem then quantifies over every field E in an independent universe v
  and every field embedding `φ : L →+* E`. `I.map (MvPowerSeries.map φ)` is the
  ideal extended to E[[X]], not E tensor_L A. The conclusion preserves all total
  and P-orders of F_i, homogeneous division in every degree, supported generation,
  and the entire chart/order conclusion over E, for arbitrary directions in E.
- The supported division expansion itself maps coefficientwise (both its equality
  and its support containment). Together with uniqueness in the extended-field
  conclusion this says q_i(map f) = map(q_i(f)), without inventing a second choice
  of a division operator.
- The next clause is exact commutation of chart substitution with map φ for
  every original direction ξ and every series f. The next is equality between
  the coefficientwise extension of the saturated ideal and the saturation over E;
  saturation is written as the span of its explicit membership set (already an
  ideal), so this equality includes arbitrary new coefficients, not just image
  elements. The final clause maps exact division by any fixed exceptional power;
  uniqueness therefore identifies every extended divided generator with its map.

Dependencies used:

- `def-weil-pbc-multivariate-power-series` records Mathlib's `MvPowerSeries` in
  `Mathlib.RingTheory.MvPowerSeries.Basic`; full definition and docstring read.
  Additional standard APIs are `MvPowerSeries.order`, `weightedOrder`,
  `homogeneousComponent`, `truncTotal`, `subst`, `map`, `Ideal.span`, and `Ideal.map`.
- The already-landed `def-trf-supported-homogeneous-division` is added to
  stmt_deps, and its module `Sheaf.RingTheory.SupportedHomogeneousDivision` is
  publicly imported. The complete signatures/docstrings of `IsOrderedVertexFamily`,
  `generated`, `quotientSupport`, `DivisionIndex`, `divisionFamily`,
  `HasUniqueDivision` were read and used, with no private copy.
- Proof-only imports are `Mathlib.RingTheory.Flat.Basic` for
  `Module.Flat.lTensor_preserves_injective_linearMap`;
  `Mathlib.RingTheory.FiniteType` for `Algebra.FiniteType.isNoetherianRing`;
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct` for
  `AdicCompletion.flat_of_isNoetherian`; and
  `Mathlib.RingTheory.MvPowerSeries.Equiv` for `MvPowerSeries.isNoetherianRing`.
  Their recorded source declarations and docstrings were read.
- The two unstated proof dependencies, `lem-trf-coordinate-ratio-chart-completion`
  and `lem-trf-homogeneous-continuous-formal-division`, have no usable Lean module
  recorded; their imports are left to their later statement deliveries. They are
  not needed to type this statement. Their full statements and the item's full
  eight-step proof are read and the proof plan is retained in the theorem docstring.
- `FormalCoefficientTransformCriterion.lean` already names the chart variable,
  coefficient division, total transform, and localization-contracted saturation
  formulas. That node cites this item, so importing it would reverse the intended
  dependency and create a cycle. Here the canonical Mathlib operations are written
  inline, without redeclaring those helper definitions. Neither that downstream
  theorem nor a stronger chart/saturation assertion is assumed.

Edge cases checked: I=0 and s=0 give a vacuous nonzero-element condition, zero
spans, and zero saturation by injectivity of exceptional multiplication. A degree-zero
vertex allows a unit generator and unit transform and hence the unit ideal. Zero
quotients give infinity and satisfy the bound. v<d_i is represented by the
subtraction-free inequality and causes no negative exponent. A singleton J makes the
substitution the identity, with no direction scalars. Nonzero directions are allowed;
substituted variables still have zero constant term. Empty variable sets have no
nonempty J, exactly as in the source. No universe relation on L and E is imposed.
The characteristic-zero assumption is retained even though parts work more generally.

Searches made (all msearch calls use group NE and this item):

- LeanFinder: `coordinate adic order estimates for supported formal power series
  division and saturated blowup transform generators` returned 8 univariate
  Weierstrass division hits, no multivariate supported estimate or saturation result.
- Loogle: `MvPowerSeries.subst, Ideal.saturation` returned zero hits and the
  diagnostic unknown identifier Ideal.saturation. This is not used as an API.
- Mathlib grep: `coordinateIdeal|blowupSubstitution|strictTransform|supported.*[Dd]ivision`
  returned zero hits.
- LeanSearch: `coordinate blowup substitution saturation formal power series ideal
  quotient supported division` returned 8 hits, including native HasSubst/subst
  tools and unrelated univariate Weierstrass tools, no exact statement.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for coordinate/order,
  homogeneous division, supported expansion, and chart-substitution names found
  the existing supported homogeneous API and the downstream coefficient transform
  helpers above. Searching the item id in WeilConjectures and Sheaf found no theorem
  realizing this node. DAG searches found the owning definition node and no
  separate canonical coordinate-adic generator theorem.
- Read BM's journal PDF online, printed pp.261--262 and 269--270 (7.1), (7.2),
  Lemma 7.22, (7.23), Corollary 7.24, and the strict-transform convention preceding
  Theorem 7.20. Read the current blueprint unit in literature/blueprint/latest.

Verification: scompile.py compiled the final module on the server in 1.8 seconds
with no compiler diagnostic. Its local attempt reported ENOSPC and automatically
fell back to the successful prescribed server compile. No direct build was run.

## Second reading by NE

Author's clause audit only; independent review is the maintainer's review per the
current dispatcher brief. Reopened the node and complete Lean file. Added the
explicit uniqueness conclusion and the saturation base-change equality during this
reading. Checked that the homogeneous family uses initial homogeneous polynomials,
not raw generators; that total and P-orders are both equalities in the hypotheses;
that the estimate covers every supported quotient (and zero quotients); and that
both finite and all-individual generator spans occur. The exact multiplication
identities force the displayed divided series uniquely and allow all scalar directions.
The map of I is ideal extension, the saturation is e-power saturation, and field
extension is quantified in a separate universe. The field clauses cover new direction
scalars, mapped original directions, supported quotients, and exact divided generators.
The ordered-vertex hypothesis uses the existing minimal-vertex definition, without
adding monotonicity, last-coordinate essentialness, or a Hilbert-function hypothesis.
All theorem proofs are the single expected sorry; definition data are explicit.
