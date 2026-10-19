## Worker report

Existing declaration delivery; no Lean module is added. The sole change to the item is its
`lean` record, binding
`AlgebraicGeometry.AffineBlowup.homogeneousAwayToChart_surjective` in
`WeilConjectures.Blowup.Affine.ChartAlgebra` (source lines 243–250).
The source was read both in the published project overlay and through
`scompile.py --source WeilConjectures.Blowup.Affine.ChartAlgebra`.

The current blueprint is
`literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/` followed by
`sk-def-nagata-sketch-data/lemma-nagata-homogeneous-away-to-chart-surjective.md`.
It says precisely “The constructed map θ_a is surjective.” The adjacent definition
`def-nagata-homogeneous-away-to-chart.md` introduces θ_a for a ∈ I and specifies
θ_a(x t^n/(a t)^n) = x/a^n for x ∈ I^n.

Hypotheses and conclusion, clause by clause:

- The ambient commutative ring is `{A : Type u} [CommRing A]`, with arbitrary universe u.
- The ideal is `(I : Ideal A)`.
- The chosen element is `{a : A}`, with the defining condition `(ha : a ∈ I)`.
  These are the section parameters of the existing declaration, not new hypotheses.
- “The constructed map θ_a” is `homogeneousAwayToChart I ha`, with source
  `HomogeneousLocalization.Away (reesGrading I) (reesX I a ha)` and target
  `chartRing I a`. The definition is the codomain restriction of the canonical evaluation
  and localization homomorphism. Its defining formula is
  `coe_homogeneousAwayToChart_mk` in the same module, so it is the specified map.
- “is surjective” is exactly
  `Function.Surjective (homogeneousAwayToChart I ha)`.

The original `stmt_deps` is empty. For mathematical identification I also read the recorded
map node `def-nagata-homogeneous-away-to-chart`, which binds
`AlgebraicGeometry.AffineBlowup.homogeneousAwayToChart` and
`AlgebraicGeometry.AffineBlowup.coe_homogeneousAwayToChart_mk` in the same module.
There is no private replacement for any notion. The existing proof follows exactly the
node's proof: use `mem_chartRing_iff` to write a chart element as x/a^n with x ∈ I^n,
and use `coe_homogeneousAwayToChart_mk` and `reesMonomial_mem` to exhibit its
homogeneous fraction as a preimage. This proof is already present upstream and is not
new proof work in this stage-2 delivery.

Edge cases checked by reading the definitions and proof: n = 0 gives the structural
image of A since I^0 = A; zero divisors require no cancellation; a = 0 or nilpotent a
is allowed (the localized rings collapse appropriately); I = 0 permits a = 0;
I = A is unrestricted; the zero ring is allowed because there is no Nontrivial assumption.
There are no finite-generation, Noetherian, domain, or nonzero-element restrictions.

Searches for an existing statement:

- `msearch.py ... leanfinder "surjective homogeneous away to chart"`: eight Mathlib
  hits, including `HomogeneousLocalization.mk_surjective` and
  `HomogeneousLocalization.Away.mk_surjective`; these concern representations of
  homogeneous fractions and do not assert surjectivity of θ_a onto the chart algebra.
- `msearch.py ... loogle "homogeneousAwayToChart_surjective"`: no hits; unknown
  Mathlib identifier.
- `msearch.py ... grep "homogeneousAwayToChart_surjective" WeilConjectures/Blowup`:
  no hits in the tool's searched source. Direct source inspection resolves this:
  the older local source checkout lacks ChartAlgebra, while the published overlay has it.
- `rg` for `homogeneousAwayToChart` and the node id in the older
  `WeilConjectures/` tree and `lean/Sheaf/`: no duplicate declaration there.
- `rg` in `dag/lean_names_upstream.json` finds this exact declaration under the item;
  the node's own slopmaster2 audit lists it as closed. Inspection of the entire current
  `lean/WeilConjectures/Blowup/Affine/ChartAlgebra.lean` confirms the full type,
  the blueprint-tagged docstring, the canonical map, and the normal-form proof.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED finding.
The prescribed delivery wrapper performs a real compiler `#check` of the existing
fully qualified declaration and server preflight before delivery.

## Second reading by NV

No second reading by a worker: the worker delivers directly under the supplied brief;
the maintainer's independent review is the only independent review.
