## Worker report

The module `Sheaf.AlgebraicGeometry.RetainedTestBoundaryRegularity` states
`AlgebraicGeometry.HilbertSamuel.retained_test_boundary_regularity` with proof `sorry`.
It defines no new notion. Only the item's `lean` field is changed.

Hypotheses and clauses, checked against the node:

- Rational ground field, with no size restriction on the schemes: the universe `u` is explicit,
  and `Embedded (ULift.{u} ℚ)` uses the rational field transported to that universe. This is the
  same ground-field convention as the landed coefficient-test modules.
- The closed embedding and smooth ambient at every stage are the fields `Embedded.i`,
  `Embedded.closed`, `Embedded.p` and `Embedded.smooth`. Initial finite type is
  `hfinite : LocallyOfFiniteType ((S 0).i ≫ (S 0).p)` together with `hcompact : QuasiCompact ...`.
  There is no reducedness or equidimensionality assumption.
- The raw length function, summation, residue-field transcendence degree and normalized
  Hilbert function are precisely the dependency's `localFunction`, `summation`, and `function`.
  Its `le` is equality or first-differing-index lexicographic strict inequality. No new numerical
  functions or alternative orders are introduced. `hbound` says the initial bound at every point.
- The actual presentation is `M : Marked (S 0)` and `hpresentation : Presents M`.
  Unfolding `Presents` gives the empty initial boundary and all finite-depth presentation tests.
  The level H0 is `(S 0).level`; no assumption that it is attained is added.
- A finite sequence of length `n`, including zero, is given directly by
  `S : Fin (n + 1) → Embedded ...` and `steps : ∀ a : Fin n, Step (S a.castSucc) (S a.succ)`.
  Every adjacent transition is the recorded test operation, and `hadmissible` requires each
  center to be admissible for the current retaining-level locus. By the supplied presentation
  this is the same as marked cosupport; no extra marked transforms have to be chosen.
- `Step.geometry` fixes the actual blowup or affine line, actual center, adapted normal
  crossings, labelled boundary strict transforms and newly appended exceptional/zero-section
  ideal. `Step.schemeTransform` uses scheme-theoretic strict transform for admissible blowups
  and an actual cartesian square in the other two cases. These fields are used unchanged.
- The prefix bound is the first conjunct for every `j : Fin (n + 1)`. The level written there
  is `(S j).level`: `Step.levelTransform` starts at H0, applies `summation` for a line step,
  and leaves the level unchanged for either blowup. Thus it is exactly the node's
  L_j = summation iterated r_j times, where r_j counts previous line tests. Using the supplied
  recursively transported level avoids introducing a second definition of this same level.
- The second conjunct covers every `x : (S j).X` whose intrinsic function equals that level.
  It quantifies every length `m` and every injection `labels : Fin m → Fin (S j).boundary.length`.
  This specifies any ordered subset of distinct boundary labels. The support condition says
  each selected hypersurface passes through the ambient image of x. In particular it excludes
  empty strict transforms and boundary components absent at x.
- `equations` ranges over all choices of ambient local defining equations: each selected
  boundary's actual `stalkIdeal` must equal `Ideal.span {equations a}`. Restriction to the
  intrinsic ring is the actual map `(S j).i.stalkMap x`; these images in their specified order
  form `List.ofFn ...`. Ambient equations are appropriate: they define the boundary
  hypersurfaces, and the node asks for their regularity on the intrinsic local ring.
- `RingTheory.Sequence.IsRegular ((S j).X.presheaf.stalk x) ...` includes both requirements
  explicitly present in the node: `regular_mod_prev` gives injectivity on every successive
  quotient, and `top_ne_smul` says the final module quotient is nonzero. It is not merely
  weak regularity. All subsets, all orders and all unit changes of local equations are covered.
- Earlier-center ideals are absent: the only boundary is `Embedded.boundary`, initially empty
  by `Presents`. No conclusion about component counts, dimensions or nonreturn of dropped
  levels is stated.

Dependency declarations and source inspection:

- `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`: `Embedded`, `Marked`, `Presents`,
  `Step`, `Step.Admissible`, and their full signatures, fields and source docstrings.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`: `localFunction`, `function`, `summation`,
  `lt`, `le`; `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `stalkIdeal` (available publicly
  through the presentation module). The normalized function uses `Module.length`,
  `Algebra.trdeg` and the structure map's `residueFieldAlgebraMap` exactly as recorded.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`. Closed immersion and smoothness
  are already fields of `Embedded`; their public imports come through the presentation.
- `Mathlib.RingTheory.Length`: `Module.length`;
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Hom.residueFieldMap`.
  Read the full defining declarations and docstrings, including the `IsLocalRing.ResidueField`
  construction and the local-homomorphism-induced residue map.
- `WeilConjectures.Compactification.StrictTransform`: `strictTransform`, `strictTransformMap`;
  `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`.
  These are the actual geometric constructions appearing in `Step`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`, whose full
  structure and parent `IsWeaklyRegular` were read. This is the recorded regular-sequence notion.

Recorded proof dependencies that have declarations are imported privately: `JetDiagramHilbertControl`,
`CoordinateSubspaceBlowupCharts`, `DiagonalTaylorFaithfulFlatness`,
`FormalCoefficientTransformCriterion`, and Mathlib's `Flat.FaithfullyFlat.Algebra`
(`Ideal.comap_map_eq_self_of_faithfullyFlat`). The presentation and regular-sequence dependencies
are already public imports. Four proof nodes currently have no recorded Lean declarations:
`lem-per-nonreduced-regular-hilbert-coefficients`, `lem-per-supported-exceptional-chart-packet`,
`lem-per-hilbert-boundary-supported-certificates`, `lem-trf-homogeneous-continuous-formal-division`.
They are named in the complete five-step proof docstring; no interface needed to state this
item is missing, and no proof-only prerequisite is restated.

Edge cases checked before writing: n=0 retains only the given upper bound and empty boundary;
m=0 asks that a scheme-point stalk itself be nonzero, which it is; an empty scheme has no
point assertions; a boundary absent at x is excluded by support; an empty retaining locus has
no regularity assertions but keeps the global upper bound; nonclosed points use the normalized
residue-field formula without a closed-point hypothesis; nonreduced X is allowed throughout;
line tests increment the level exactly once, while exceptional-intersection tests do not.
Repeated selection of the same boundary label is excluded. Any permutation is another allowed
injection. No arbitrary equation, unsupported ideal or noncanonical morphism is substituted.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder "Hilbert Samuel retained level boundary regular sequence after finite
  admissible test sequence"`: eight results, all regular-sequence definitions and algebraic
  regularity lemmas; no geometric finite-test boundary result.
- `msearch.py ... loogle "RingTheory.Sequence.IsRegular, HilbertSamuel"`: no hits; HilbertSamuel
  is unknown to the Mathlib search service. The directly inspected project definitions supply it.
- `msearch.py ... grep "retained.*boundary|HilbertSamuel.*regular|TestSequence"`: no Mathlib hits.
- `msearch.py ... leansearch "Hilbert Samuel upper bound and regularity of boundary equations at
  retained levels after admissible blowups and line tests"`: eight results, including local-ring
  regular-sequence and unrelated combinatorial bounds; none states the item's theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `retained_test_boundary_regularity|regular_test_boundary|HilbertSamuel.*IsRegular` and for
  retained-boundary alternatives: no existing theorem. `grep -rn` of the item's exact id in
  `lean/WeilConjectures` found no occurrence. Broader `stalkIdeal`, `Step.Transforms` and test
  sequence searches found the existing presentation and coefficient propagation APIs.
  `CoefficientTestSequencePropagation` was read; its theorem requires reducedness and supplied
  coefficient data, so it is not this node and is not rebound as an existing match.

Source: read BMT https://arxiv.org/html/0905.3580v1, especially sections 5.2, 6.1--6.3,
and the current blueprint ancestor `lem-per-artin-gabber-affine-curve` and its proof under
`literature/blueprint/latest`. The retained-boundary assertion is identified in the node as an
agent structural refinement, not a verbatim BMT theorem; the five-step docstring follows that
node's supplied refinement. No statement correction or disputed statement is needed.
The specified repair-note path has no entry for this item.

Validation: prescribed `scompile.py Q49 lem-per-retained-test-boundary-regularity <module>`
passed cleanly in both sandbox and library modes (1.8 s and 1.7 s); every universe/variable is
explicit and there are no overlength Lean lines. The sole postponed theorem has the matching
DAG node and its full natural-language proof. Dry run and delivery use the prescribed wrapper.

## Second reading by Q49

I reopened the node and Lean signature for a separate checking pass. This is a self-check;
the dispatcher expressly forbids starting another agent and supplies the maintainer's independent
review after delivery. No independent second worker is claimed here.

I checked the finite history endpoints (`castSucc` to `succ`), the initial finite-type pair,
the presentation's empty boundary, and the inclusion of prefix zero. The upper-bound clause and
the equality hypothesis use exactly the same recursively transported level. I checked that labels
are injective, support is tested in the ambient at the image of x, and equation generation is
there before restricting by the stalk map. Consequently arbitrary ordered subsets, rather than
only boundary-list prefixes, are covered. Finally I read `IsRegular` again to check the nonzero
final quotient, including m=0. No mismatch was found and no correction was made.
