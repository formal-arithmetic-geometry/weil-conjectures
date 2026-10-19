## Worker report

Item: `lem-a1-finite-etale-weil-fibre-comparison`. The delivery states the
finite-etale rational Weil fibre comparison in
`Sheaf.Paper.A1FiniteEtaleWeilFibreComparison`. All named theorem proofs are
`sorry`; definitions have explicit data. The inherited unfinished drafts are
retained under `scratchpad/` and are not delivery modules. The first dry run
found the missing node copy; this delivery supplies that copy and this report.

The primary theorem is `WeilConjectures.a1FiniteEtaleWeilFibreComparison`.
The owning node also records the auxiliary declarations that express its
point-free heart assertion, finite-stage coordinates, and local-operator clause.
No natural-language statement, dependency list, or proof plan was changed.
No new nodes or dependency repairs are needed: all helpers belong to this
node's residue-field restriction and its comparison map.

Hypotheses and objects, clause by clause:

- The finite field, its characteristic, cardinality, exponent, and fixed closure
  are `D : FiniteFieldDatum.{u}`. This is the recorded global datum, with real
  fields and algebra structure; the residue base retains the same closure.
- The coefficient prime is `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
  `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`
  is the specified algebraic closure of the coefficient field. Its universe `v`
  is independent of the scheme universe `u`.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` are the original models. The two pairs
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]` and the same for `Y₀`
  state finite type. The morphism is `g₀ : X₀ ⟶ Y₀`, with
  `[IsFinite g₀.left]` and `[Etale g₀.left]`. No structural separatedness of
  either model, nonemptiness, or surjectivity of the morphism is assumed.
- The geometric schemes are the recorded `D.geometricFiber X₀`,
  `D.geometricFiber Y₀`, and their morphism `zlFiberMap D g₀`.
- `F : sfCommonStageWeilSheaf D l hl X₀ Ω` is exactly a constructible heart
  object with invertible Weil structure in the common-stage fixed-pair category.
  Its image uses the recorded `sfModelWeilDerivedPush`, including the induced
  Frobenius mate. The primary theorem's first conjunct is the image's
  `sfCommonStageHeartProperty`. `a1FiniteEtaleWeilImage_mem` states the same
  assertion without any closed-point binder, covering an empty target too.
- A closed point is `y : {y : Y₀.left // y ∈ closedPoints Y₀.left}`.
  Its actual residue field is `Y₀.left.residueField y.val`; its degree is
  `localClosedPointDegree D Y₀ y`. The chosen embedding is `ι`, and `hι`
  says exactly that it respects the original k₀ structure map.
- `a1ResidueField_properties` gives finiteness, cardinality q^d_y, and the
  algebraic-closure property for the algebra induced by `ι`.
  `a1ResidueDatum` changes only the finite base to this actual residue field,
  with exponent `D.a * localClosedPointDegree D Y₀ y` and the same `D.k`.
- `a1FiniteFibreModel` is `Over.mk (pullback.snd g₀.left
  (Y₀.left.fromSpecResidueField y.val))`, literally Z₀ over L.
  `a1FiniteFibreModel_finite` is finite by base change. Its geometric fibre
  under `a1ResidueDatum` is Z. `a1FiniteFibreInclusion` is the geometric
  inclusion to X, explicitly built by `pullback.lift` from both projections.
- `a1ResidueInclusion_return` identifies relative-L Frobenius with the d_y-th
  original Frobenius after restriction. `a1ResidueWeilComplex` composes the
  specified pullback compositor with `constantExtensionWeilIterate` of index
  `d_y - 1`, whose exponent is d_y. Thus `a1FiniteFibreWeilSheaf` is the actual
  restriction G with the iterated structure, never an unspecified Weil sheaf.
  `a1FiniteFibreWeilComplex_mem` states that restriction stays in the heart.
- `a1FiniteFibreStalkPair` restricts the actual image to the residue point,
  retaining that same d_y-th return. Its degree-zero point fibre is the stalk
  in the statement, carrying the local F_y.
- `a1FiniteFibreBaseChange` constructs the comparison as the adjunct of the
  pullback of `a1FiniteFibreCounit`. The middle identification is the literal
  geometric square `a1FiniteFibreSquare`; its boundaries are the recorded
  `sfModelWeilDerivedPushForget`, normalized by its counit equation. No input
  comparison map or isomorphism is assumed. The primary theorem states
  `IsIso` of this precise arrow and its commuting square with the actual Weil
  structures. At the residue point the square is b_y F_y = F_(Z/L) b_y.
- The target of that canonical arrow is the ordinary proper image to Spec L.
  The heart assertion and its isomorphism, in Weil pairs, to
  `(commonStageCompactWeilCohomology ... (Compactification.ofIsProper ...)
  (a1FiniteFibreWeilSheaf ... F) 0).obj` identify it with the recorded H_c^0.
  This is a representation of the same proper cohomology, retaining Frobenius.
  The ordinary comparison arrow itself is explicitly defined before making
  that representation; it is never selected from a Nonempty existence claim.
- `a1FiniteFibreStageCoordinates` descends both Weil objects, their comparison,
  inverses and identities to one actual finite coefficient stage S. Its
  equality identifies the included arrow f with the specified counit mate,
  followed by its proper compact-cohomology presentation c. The conclusion
  supplies the coordinates; they are not extra hypotheses on F or g₀.
- In every such presentation `a1FiniteFibreLinearComparison` states that taking
  the exact degree-zero rational point fibre and extending scalars along
  `sfAdicCoefficientEmbedding l Ω S` makes f an isomorphism of Ω-modules and
  gives the equality with `localClosedFrobeniusCohomology` on both sides.
  The arbitrary presentation parameters are universally quantified only to
  express independence of the finite-stage coordinates. Existence is supplied
  by the preceding theorem. This avoids the older small `ModuleCat.{u} Ω`
  output imposing a hidden equality between coefficient and scheme universes.
- `a1FiniteFibreClosedPointMap` is the actual first projection to the set of
  points x above y. The primary theorem asserts its bijectivity and separately
  asserts that every point x over y is closed. It also asserts `IsIso` of the
  actual first-projection `residueFieldMap` at every point of Z₀. That map is
  the canonical residue-field identification, respecting L by scheme-map
  functoriality; no unrelated field equivalence is selected.
- `a1FiniteFibreRationalStalkIso` is H^0 of the recorded rational pullback
  compositor at each geometric lift. `a1FiniteFibreLocalFrobenius` states its
  equality with the local operator over L on G and the original operator at x
  over k₀, after extension to Ω. It quantifies over every finite coefficient
  field E, every embedding E → Ω, every closed fibre point z, and every
  compatible geometric lift rho. `a1FiniteFibreLocalReturn` uses the absolute
  degree of x, so the operator is the original F_x, not only a trace equality.
- `a1ResidueStageComparison` identifies finite-stage restriction with the
  actual common-stage restriction in Weil pairs; the underlying arrow is fixed
  to the explicit `a1ResidueStageCarrierIso`. Hence the finite-stage local
  assertion concerns G itself and is independent of its presentation.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilSheaf`, `sfWeilStageObject`,
  `sfWeilPrimeInvertible`, and the faithful fixed-pair forgetful functors.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`, inherited
  through the Weil-sheaf and direct-image imports.
- `Sheaf.Paper.SfCommonStageDirectImage`: `sfModelDerivedPush`,
  `sfModelDerivedAdjunction`, `sfModelWeilDerivedPush`,
  `sfModelWeilDerivedPushForget`; the latter's signature fixes its counit
  normalization and is used in both boundary identifications.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localClosedPointDegree`,
  `localClosedPoint`, `localPositivePower`, `localWeilIterate`,
  `localPointComplex`, `localFrobeniusCohomology`, and
  `localClosedFrobeniusCohomology`. The degree is the same finrank of the actual
  residue extension as `Scheme.Hom.degreeOver` in the point-counts node's
  recorded `WeilConjectures.ZetaSeries`; no point-count or degree is redefined.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`.
- `Sheaf.Paper.GlobalGeometricFrobenius`: global geometric-Frobenius convention;
  the relative-L compact action is retained in the actual cohomology Weil pair.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`:
  `sfWeilCohomologyPoint`, `commonStageCompactWeilCohomology`, with its specified
  higher proper/open image and the induced Weil action.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`:
  `constantExtensionWeilIterate`, reusing its prescribed pullback composition.
  This is used for the iterate, with no constant-extension or lissity hypothesis.

All recorded modules of the stated proof dependencies are imported as proof
imports (plain `import`), except where already public imports. The ten-step
natural-language proof of the node is reproduced in the main theorem docstring.
Each named postponed helper has its own source and complete proof docstring;
each belongs to the recorded statement's canonical restriction/comparison data.
Definitions contain pullback maps, functor compositions, or specified iterates;
postponed proofs supply only their stated compatibility or membership proofs.

Sources checked: local Stacks `etale-cohomology.tex`,
`proposition-finite-higher-direct-image-zero` (Tag 03QP), both numbered clauses
and its proof; main-20261015 blueprint
`sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-map-purity.proof.md`,
first paragraph and Frobenius-cycle argument. The node itself supplies the
rational/common-stage and residue-field refinement with the references to
Weil II (1.1.3), (1.1.7)--(1.1.10).

Edge cases checked before completing the draft:

- An empty target has no closed point: the separate point-free image theorem
  includes it. No existence of y is needed for that assertion.
- An empty fibre is allowed: finite products over zero sheets give the zero
  image and zero compact cohomology, and the closed-point bijection is empty.
- A non-surjective map is permitted; its omitted points are the empty-fibre case.
- Degree d_y is positive by the recorded `localClosedPointDegree_pos`, so the
  `d_y - 1` positive-power encoding retains degree-one points correctly.
- Disconnected fibres are represented by actual scheme pullbacks, with no
  ordering or connectedness assumption. The residue isomorphism uses the
  closed fibre immersion and does not introduce algebraic-closure equality.
- No purity, lissity, semisimplicity, arithmetic descent, or Frobenius-stable
  integral lattice is required. A common rational field suffices for the Weil
  isomorphism and its inverse.
- Scheme and coefficient universes are explicit and independent. Point
  realization explicitly supplies `frobeniusPointPrimeInvertible`; it does
  not equate the two universes to repair elaboration.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "finite etale direct image Weil sheaf stalk fibre
  compact cohomology Frobenius equivariance"`: eight results, including
  `IsArithFrobAt.arithFrobAt`, finite scheme fibre finiteness, and
  `LocallyOfFiniteType.stalkMap`; none states the rational Weil comparison.
- `msearch.py ... leansearch "finite etale pushforward stalk fibre cohomology
  Frobenius equivariant"`: eight results, principally
  `TopCat.Presheaf.stalkPushforward` and its germ formulas, and Witt-vector
  Frobenius equivariance; these use different categories and operators.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite"`:
  only `exists_etale_isCompl_of_quasiFiniteAt`, a neighbourhood splitting
  result, not the claimed cohomology or operator comparison.
- `msearch.py ... grep "finite.*Frobenius|Frobenius.*finite" AlgebraicGeometry`:
  zero matches. Earlier Mathlib searches are preserved in `searches.jsonl`.
- `rg` of `WeilConjectures` and `lean/Sheaf` for the item id,
  `finiteEtaleWeilFibreComparison`, and `a1FiniteEtaleWeil` found the finite-map
  purity consumer and the distinct lisse finite-image interface. The latter
  assumes separated models and concerns lissity; it does not state this node.
  Upstream finite-stalk isomorphisms are finite/ordinary etale coefficients,
  without the rational common-stage Weil restriction or local-return equality.

No STATEMENT-DISPUTED or source-based statement correction is claimed.

## Validation

The required scompile wrapper initially found the missing point-residue
invertibility instance in the inherited draft. Replaced it by the recorded
`frobeniusPointPrimeInvertible B l hB`. Removed theorem-statement `let` binders,
expanded their terms, and wrapped every Lean line to at most 100 characters.
The final scompile run passed cleanly: sandbox 53.4 s; named library module
53.6 s. No warnings remained. The required deliver2.py --no-push run printed
`OK (dry run): commit 62bbb4f15b passes the preflight and compiles; nothing pushed`.
The only delivered node-field change is `lean`; all 41 owned declarations are
listed there. The 16 postponed theorem proofs are named and documented.
No source checkout or live Lean library was edited.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
