## Worker report

The module `Sheaf.RingTheory.GrauertRemmertPowerbounded` states
`RestrictedSeries.grauert_remmert_powerbounded`, with its sole proof `sorry`.
No definition data or additional theorem is postponed. The node statement is unchanged.
The added statement dependency `def-trf-restricted-series-presentation` is already
landed and supplies `RestrictedSeries.constants` and the restricted-series convention.

Source read: Temkin, Stable modification of relative curves, arXiv:0707.3953v3,
Theorem 3.5.5, Step 2, printed p. 22 (PDF page index 21), lines 1490–1496 of the
online PDF extraction: https://arxiv.org/pdf/0707.3953v3 . It states the same
finiteness assertion over an algebraically closed complete height-one field, for a
reduced affinoid algebra and a topologically finite type integral model with generic
fibre the original algebra. The alternate university PDF endpoint timed out.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The field `K` has `[NontriviallyNormedField K]`, so the absolute value is
  multiplicative, real-valued (rank one), and nontrivial. `[IsUltrametricDist K]`
  is the nonarchimedean condition. `[CompleteSpace K]` and `[IsAlgClosed K]` give
  precisely completeness and algebraic closedness, with no characteristic restriction.
- The valuation ring is `V : ValuationSubring K`, with `hV` identifying its carrier
  with `{x | ‖x‖ ≤ 1}`. This uses Mathlib's valuation subring and its valuation-ring
  instance, rather than constructing another valuation ring.
- The affinoid algebra is `C : Type v`, with `[NormedCommRing C]`,
  `[CompleteSpace C]`, `[IsReduced C]`, and `[Algebra K C]`. The presentation
  `haff` gives a finite number `n` of variables, a surjective ring map from
  `MvPowerSeries.IsRestricted.subring` at polyradius one, scalar compatibility
  `q.comp (constants K n) = algebraMap K C`, and the quotient topology.
- The two open-set equivalences in `haff` and `hmodel` express the Gauss topology
  explicitly: a target set is open exactly when its inverse image contains a
  sufficiently small Gauss ball about each of its points. The ball condition is
  `gaussNorm (norm : R → ℝ) (fun _ ↦ 1) (t.val - s.val) < ε` for `R = K` or `V`.
  Thus no coefficientwise topology is silently substituted. No particular equivalent
  Banach norm on `C` is imposed: the existing `IsAffinoidQuotient` predicate fixes
  literal equality with a quotient norm, so the theorem spells out the topology
  instead, using the same existing restricted-series ring and constants. This is a
  formula in the theorem, not a second definition or a new analytic object.
- `[Algebra V C]` and `[IsScalarTower V K C]` specify the restriction of the scalar
  structure along the actual inclusion `V ⊆ K`. The tower identity forces this to
  be the canonical restriction; it is not an additional mathematical restriction.
- `D : Subalgebra V C` is the actual subalgebra, with the inherited norm topology
  from `C`. `hbounded` says for each `d : D` that all natural-number powers of its
  image are norm-bounded. This is exactly `D ⊆ C°`, including the zeroth power.
- `hmodel` is a scalar-compatible surjection from `V⟨T₁,…,Tᵣ⟩` to `D` and the
  quotient-topology equivalence for its inherited topology. There is no hypothesis
  that the kernel is finitely generated or that `D` has finite presentation.
- `hgeneric` supplies a ring isomorphism from `D ⊗[V] K` to `C` and characterizes it
  on every pure tensor as `d.val * algebraMap K C k`. Hence it is the natural
  generic-fibre map, not an arbitrary isomorphism of the underlying rings.
- The conclusion supplies `P : Submodule D C` whose elements are exactly those
  `c` with `∃ M : ℝ, ∀ m : ℕ, ‖c ^ m‖ ≤ M`, and asserts `Module.Finite D P`.
  Norm-boundedness is precisely boundedness in the affinoid Banach topology. The
  carrier identity pins `P` to `C°`; the action on it is actual multiplication
  inside `C`. This expresses the finite-module assertion without assuming closure
  or introducing a second definition of power-bounded elements. `P` is not an
  arbitrary module or a merely equinumerous copy.

Dependency declarations read and used:

- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE`,
  `Mathlib.RingTheory.Valuation.ValuationRing`, lines 60–64 and 407–416; read the
  class docstring and fraction-field equivalent characterization. Its bundled
  realization `ValuationSubring`, `Mathlib.RingTheory.Valuation.ValuationSubring`,
  lines 36–42, is used to retain the inclusion in `K`.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, lines 116–121, whose field is finite
  generation of the top submodule; this is the conclusion's finite generation.
- `def-trf-restricted-series-presentation`: `RestrictedSeries.constants`,
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, lines 26–33, including its
  docstring; also read the full signatures and docstrings of
  `IsTopologicallyFinitelyPresented`, `IsAffinoidQuotient` and
  `HasBoundedTopologicallyGeneratedImage`. Only constants and the underlying
  Mathlib restricted-series construction are needed; finite relations are absent
  from this node. `MvPowerSeries.IsRestricted` and `.subring` are read at
  `Mathlib.RingTheory.MvPowerSeries.Restricted`, lines 31–34 and 106–111.

The three analytic proof inputs (`lem-trf-affinoid-distinguished-presentation`,
`lem-trf-affinoid-powerbounded-integral`, `lem-trf-restricted-quotient-complete`)
have no recorded Lean modules at drafting time, so there are no proof-only imports
for them. Their names and all five proof steps are retained in the theorem docstring.
The finite-generation definition is already publicly imported through the
restricted-series module.

Edge cases checked: `C = 0` is allowed by `NormedCommRing`, `CompleteSpace` and
`IsReduced` and by all quotient maps; neither `Nontrivial C` nor injectivity of
`K → C` is assumed. In this case `D = 0`, its generic fibre is zero, and `P = 0`
is finite with the empty generating set. Both variable counts may be zero.
When the distinguished presentation has zero variables, the empty monomial is
`1`, as explained in proof step 5. Zeroth powers are included in all boundedness
conditions. The field has independent universe `u` and the algebra universe `v`;
there is no artificial equality of universes. Valuation rings need not be discrete.
For `C = K` and `D = V`, the conclusion is the rank-one finite module `V`.
No statement dispute or source correction was needed.

Searches actually run:

- `msearch.py leanfinder`: “Grauert Remmert finiteness power bounded elements affinoid
  algebra”: eight hits including `IsAlmostIntegral`, `spectralValueTerms_finite_range`
  and scheme finite-morphism lemmas; none states this analytic finiteness theorem.
- `msearch.py loogle`: `Module.Finite, ValuationRing`: zero hits.
- `msearch.py leansearch`: “Grauert Remmert finite module power bounded affinoid”:
  eight hits on finite modules, finite ring maps and polynomial finite generation;
  none proves affinoid power-bounded finiteness.
- `msearch.py grep`: `Grauert|Remmert|affinoid|power.bounded` in `Mathlib`: zero
  hits because that argument is relative to the Mathlib directory. Repeated with
  directory `Analysis`: nineteen hits on references to BGR in seminorm and spectral
  norm files, none the present theorem.
- Direct `rg` of `WeilConjectures` for `Grauert|Remmert|affinoid` found algebraic
  cohomological Grauert results only. The required node-id search found no match.
- Direct `rg` of `lean/Sheaf` for `affinoid|Affinoid|TateAlgebra|PowerBounded|powerBounded|
  RestrictedPowerSeries` located the existing restricted-series presentation module,
  the formal comparison using it, and prose in reduced-fibre normalization.
  Read those declarations rather than duplicate them.
- Direct Mathlib search for bounded powers found `isBounded_pow`, which concerns
  boundedness of fixed powers of a bounded set, not finiteness of the power-bounded
  subring. The upstream declaration-name index contains no matching node/theorem.

Validation: the prescribed `scompile.py` compiled this single module cleanly in
both sandbox and library module contexts (12.6 s and 3.4 s); no errors or warnings.
The maximum Lean line width is at most 100. Every variable and universe is explicit.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
