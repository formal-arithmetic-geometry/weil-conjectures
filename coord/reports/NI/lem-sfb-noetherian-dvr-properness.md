## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianDvrProperness` states
`AlgebraicGeometry.isProper_iff_unique_dvr_lift`, with exactly one postponed theorem and
no new definitions. The theorem's docstring includes all eight steps of the node's proof.
Its source is Stacks Project, limits.tex, Tag 0208, equivalence (1) and (3), read in the
local literature source. No node statement or dependency list was changed.

Hypothesis and clause correspondence:

- Schemes X and S and the named morphism f are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally Noetherian S is `[IsLocallyNoetherian S]`.
- Finite type of f is `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded
  interface of `def-weil-finite-type-morphism`.
- Properness is `IsProper f`, and the asserted equivalence is `↔`.
- Every DVR R is `∀ (R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's DVR excludes fields, just as the node does.
- Any fraction field K is `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`.
  It is not a specially selected fraction field. The algebra map supplies the canonical
  generic-point inclusion `Spec.map (CommRingCat.ofHom (algebraMap R K))`.
- The arbitrary top and bottom arrows are
  `(a : Spec (CommRingCat.of K) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ S)`.
- Commutativity is `a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b`.
- Unique existence of the extension is `∃! l : Spec (CommRingCat.of R) ⟶ X, ...`.
- The two extension equations are `l ≫ f = b` and
  `Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = a`.
- The final unrestricted-DVR clause is retained: there is no excellence instance, finite-type
  hypothesis on b or R, restriction on a's image, or hypothesis of separatedness on f.

Dependencies read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. Its affine-open characterization agrees with
  the node's existence of a Noetherian affine cover.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  its morphisms `Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with `AlgebraicGeometry.QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (imported transitively).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`. Its universal closedness implies quasi-compactness, so
  Mathlib's locally-of-finite-type properness class means the node's finite-type properness.
- `def-sc-discrete-valuation-ring`: the recorded mathlib_match
  `IsDiscreteValuationRing`, `Mathlib.RingTheory.DiscreteValuationRing.Basic`, with the
  separately bound `IsDomain`. Its class is precisely a nonfield local PID.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.

Proof imports retain the stated geometric tools: Mathlib's valuative criterion, and the
upstream `WeilConjectures.AlgebraicGeometry.ChowLemma` and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. Through their imports they also supply
the recorded Mathlib immersion, finite-type/base-change, pullback, qcqs and universal
closedness tools. The proof prerequisite `lem-sfb-noetherian-image-boundary-dvr` has no
recorded declaration at the time of writing, so there is no module to import yet; it is
not required to type the present statement. No dependency module or new node is needed.

Edge cases checked before writing:

- Empty X: no maps from a field spectrum to X exist, so the right side is vacuous;
  the empty morphism is proper. Empty S forces empty X and also causes no problem.
- Identity maps and finite maps satisfy the expected unique-lift condition.
- The punctured affine line inclusion over a field fails existence, detected by the
  local DVR at the missing origin. Thus the criterion does not accidentally discard
  DVRs whose generic point maps to a nongeneric point of S.
- The doubled-origin affine line over a field fails uniqueness for the local DVR at
  the origin. No separatedness assumption was added to hide this case.
- Fields are excluded as DVRs by Mathlib's nonzero-maximal-ideal condition, as required.
- Mixed and equal characteristic, nonexcellent DVRs and unrestricted bottom maps remain
  quantified. Universe u is shared with the schemes, following Mathlib's valuative-square
  convention; there is no independent smaller universe making the tests vacuous.

Searches made (2026-10-22):

- `msearch.py ... leanfinder`: “A finite type morphism to a locally Noetherian scheme is
  proper iff every discrete valuation ring square with its fraction field has a unique
  lift”. Eight hits, including `IsProper.of_valuativeCriterion` and `ValuativeCriterion.iff`;
  all use arbitrary valuation rings, not the Noetherian DVR reduction.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProper, AlgebraicGeometry.ValuativeCriterion`.
  Two hits: `IsProper.of_valuativeCriterion` and `IsProper.eq_valuativeCriterion`, neither
  the present theorem.
- `msearch.py ... leansearch`: “Properness over a locally Noetherian scheme can be checked
  by unique lifting for discrete valuation rings”. Eight hits on the general valuative
  criterion and its existence/uniqueness clauses, no exact match.
- `msearch.py ... grep`: `dvr|DVR|[Nn]oetherian` in
  `AlgebraicGeometry/ValuativeCriterion.lean`. The hit at line 29 explicitly lists the
  Noetherian DVR reduction as future work.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Noetherian/valuative,
  proper/DVR and `proper_iff.*discrete`, and exact-name searches for
  `isProper_iff_unique_dvr_lift`, found no matching statement. Broad DVR searches found
  specialization traits and local DVR facts, which do not assert this criterion.
- `grep -rn 'lem-sfb-noetherian-dvr-properness' lean/WeilConjectures` found no occurrence.

Assignment diagnosis: the previous BLOCKED report confused the 04:12 reviewer-approved
stage-1 split in `coord/ledger.md:24537` with a stage-2 statement delivery. The node has
no `lean` or `reviewed_lean` record on the read base. This delivery supplies its first
Lean statement; it does not repeat that stage-1 delivery.

No STATEMENT-DISPUTED issue or correction was found.

## Second reading by NI

I reread the node and module clause by clause after drafting. The three hypotheses on S
and f match the recorded interfaces, and the right side quantifies over every DVR,
every field-of-fractions presentation, and every commuting pair of maps. `∃!` applies to
the map satisfying both required equations, so it includes existence and uniqueness.
No restriction on excellence, characteristic, or generic image appears. There is no
new notion or dependency interface to audit. This is a single-worker rereading;
the maintainer supplies the independent delivery review prescribed by the dispatch brief.
