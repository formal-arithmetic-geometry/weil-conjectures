## Worker report

Item: lem-sfb-equation-count-closed-fibre-localization. The module
`Sheaf.RingTheory.EquationCountClosedFibreLocalization` states
`Algebra.exists_localization_relativeGlobalCompleteIntersection_preserving_reduction`.
Its only proof is `by sorry`, as required for stage 2. No new definitions, dependency
repairs, or statement corrections are needed; the node changes only in `lean`.

Source read directly: literature/stacks-project/algebra.tex, definition-relative-global-
complete-intersection (Tag 00SP), and lemma-localize-relative-complete-intersection
(Tag 00ST), statement and proof of assertion (1). Assertion (3), already formalized
upstream, is a different statement and does not provide the prescribed closed reduction.
The source's proof and the node's six proof steps are included in the theorem docstring.

Clause-by-clause correspondence (write S = R[y]/(f), and g = the class of h):

- The arbitrary commutative ring is `(R : Type u) [CommRing R]`, with universe u
  declared explicitly and `autoImplicit false`. There is no nontriviality, finiteness,
  Noetherian, or local-ring hypothesis.
- The arbitrary ideal is `(I : Ideal R)`; both zero and unit ideals are allowed.
- The nonnegative variable and equation counts are `(m c : ℕ)` and
  `(f : Fin c → MvPolynomial (Fin m) R)`. The displayed occurrences of
  `MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)` are precisely S, with its
  canonical R-algebra structure. No arbitrary presentation or map is substituted.
- The hypothesis about all nonempty fibres of S/IS over R/I is `hdim`, using the
  recorded `IsRelativeGlobalCompleteIntersectionPresentation` applied to
  `fun i ↦ MvPolynomial.map (Ideal.Quotient.mk I) (f i)`. These are the reductions of
  the given equations in `(R/I)[y]`. Their quotient is canonically S/IS: the coefficient
  quotient and quotient by the equation ideal commute, since the kernel of the
  combined polynomial map is the sum of the coefficient ideal and `(f)`. The induced
  coefficient-preserving isomorphism identifies every residue-field fibre over R/I.
  Thus this is exactly the stated fibre hypothesis, without an extra assumption.
- The definition's nontrivial-fibre premise guards BOTH `c ≤ m` and the dimension
  equality. Hence it encodes the INTEGER difference m-c. No global `c ≤ m` hypothesis
  is added, and a zero reduction is admitted even when c > m.
- The existential `h : MvPolynomial (Fin m) R` supplies the required lift. The required
  `g ∈ S` is explicitly `Ideal.Quotient.mk (Ideal.span (Set.range f)) h`; quantifying h
  rather than g loses nothing because the quotient map is surjective.
- The first conjunct applies the quotient map for
  `I.map (algebraMap R S)` to g and asserts equality to `1`. This ideal is IS, so the
  conjunct says exactly that g maps to 1 in S/IS, including the zero-ring case.
- The second conjunct is the SAME recorded presentation predicate, now on `Fin.snoc`
  of the renamed original equations and `rename Fin.castSucc h * X (Fin.last m) - 1`.
  The original variables occupy `Fin.castSucc`, the inverse variable occupies
  `Fin.last m`. Thus it concerns these m+1 variables and c+1 equations, not merely
  some complete-intersection presentation of an isomorphic ring.
- The final existential `e : T ≃ₐ[R] Localization.Away g` says the displayed enlarged
  quotient IS a presentation of S_g over R. Its two equations specify the canonical
  presentation map: old variables go to the localized old classes, and the new one
  to `IsLocalization.Away.invSelf g`. These formulas describe the presentation in
  00ST and the inverse-variable-presentation dependency; they do not impose a new
  geometric hypothesis.
- Empty fibres are allowed by the predicate's `Nontrivial (...) → ...` in both
  places, and no nonemptiness assumption appears anywhere else.

Dependency declarations used, after opening their full signatures and docstrings:

- def-weil-pbc-mv-polynomial-ring: `MvPolynomial`, with `MvPolynomial.aeval` and
  `MvPolynomial.algHom_ext` for its universal property, in
  `Mathlib.Algebra.MvPolynomial.Basic` / `Mathlib.Algebra.MvPolynomial.Eval`.
- def-weil-pbc-relative-global-complete-intersection:
  `Algebra.IsRelativeGlobalCompleteIntersectionPresentation` in
  `WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation`.
  This public-imports the original ring-map predicate as well. The exact recorded
  specified-presentation interface is used twice, with no copy of its definition.
- def-weil-ring-localization-away: `Localization.Away` in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, supplied through the ring-localization
  public import `Mathlib.RingTheory.Localization.Away.Basic`. The latter also supplies
  the ring structure, scalar tower, and `IsLocalization.Away.invSelf`.
- Already recorded proof modules are imported without `public`:
  `WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`
  (`Algebra.fibre_dimension_bounded_open_upstairs`),
  `WeilConjectures.Topology.DimensionSupremumLocalDimensions`
  (`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`),
  `WeilConjectures.RingTheory.EquationCountLocalizePresentation`
  (`Algebra.exists_localization_presentation`), and
  `WeilConjectures.RingTheory.PolynomialQuotientDimensionLowerBound`
  (`AlgebraicGeometry.sub_le_topologicalKrullDim_spec_mvPolynomial_quotient`).
  Mathlib's localization-base-change and presentation-base-change modules are also
  imported for the proof plan. The remaining elementary proof ingredients are supplied
  by these imports and their spectrum/ideal/tensor dependencies.

Edge cases checked before writing:

- If S/IS is zero, h = 0 gives g = 0 = 1 in the reduction. Inverting zero and the
  enlarged quotient with equation -1 are both zero rings; the fibre predicate is
  vacuous. This includes I = top, zero R, zero S, and c > m when allowed by hdim.
- If some closed-reduction fibre is nonempty, hdim explicitly forces c ≤ m, so
  subtraction in ℕ does not erase a negative expected dimension.
- For example m = 0, c = 1, f = 0 over a field with I = 0 fails hdim, as it should;
  it is not spuriously admitted by truncated subtraction. If instead f = 1, all
  quotients are zero and the statement allows it.
- I = 0 says the original specified presentation is already a relative global
  complete intersection. Then h = 1 preserves reduction and gives the standard
  inverse-variable presentation. Empty Fin 0 variable/equation families are accepted;
  in particular m = c = 0 presents R and then R[z]/(z-1).
- The usual jumping example R = k[t], I = (t), f = (y1(1-ty2), y2(1-ty2)), m = c = 2
  has the expected zero-dimensional reduction but an unwanted generic line.
  h = 1-ty2 reduces to 1 and removes that line. This illustrates why the conclusion
  is localization rather than an assertion about all fibres of S itself.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "A polynomial quotient with expected dimension fibres
  over R/I becomes a relative global complete intersection after localization at an
  element congruent to one modulo IS"`: 8 hits on standard smooth/submersive
  presentations and their localizations, no exact match.
- `msearch.py ... loogle "Algebra.Presentation, IsLocalization.Away"`: 2 hits,
  `Algebra.Presentation.localizationAway` and `relation_comp_localizationAway_inl`;
  they supply presentations but not the dimension hypothesis or reduction condition.
- `msearch.py ... grep "relativeGlobalCompleteIntersection|closed.*[Ff]ibre.*localiz"
  RingTheory`: zero Mathlib hits.
- `msearch.py ... leansearch "Localize a polynomial quotient with expected dimension
  fibres over a quotient of the base at an element congruent to one to obtain a relative
  global complete intersection"`: 8 hits on localization quotient equivalences,
  quotient finiteness, fibres, and standard smoothness, no exact match.
- `rg` over lean/WeilConjectures and lean/Sheaf for
  `relativeGlobalCompleteIntersection|IsRelativeGlobalCompleteIntersection|equation_count|closed_fibre`
  found the existing presentation definition and 00ST(3) theorem, which were opened
  and read. The latter localizes near ONE prime and does not require g = 1 modulo IS.
  Searches for this node id found only its use in the proof docstring of
  SyntomicAlgebraSurjectionLift, not a declaration of the item. Searches of
  dag/lean_names_upstream.json confirmed the recorded complete-intersection notions.
  No duplicate notion or exact theorem was found.

Validation: scompile.py compiled this file both as sandbox and final library module
against the live published server build (2.2 s and 2.9 s), without errors or unexpected
warnings. The module has one named postponed theorem and no hollow definitions.
No STATEMENT-DISPUTED issue found.

## Second reading by Q25

The dispatcher assigned a single worker and explicitly prohibited starting agents.
This paragraph records a second self-reading, not an independent-worker review;
the maintainer supplies the independent delivery review. I reopened the node and the
finished module and checked every binder and conjunct against the mapping above.
In particular the existing predicate guards c ≤ m only on nonempty fibres, the
hypothesis concerns the reduced equations over R/I, the chosen g reduces to 1,
and the complete-intersection conclusion concerns precisely the enlarged equations.
The algebra equivalence includes the canonical generator images, and the zero ring
is retained. No mismatch was found and no statement correction was made.
