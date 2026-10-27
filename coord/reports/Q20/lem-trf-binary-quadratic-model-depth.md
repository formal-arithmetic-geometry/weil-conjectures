## Worker report

The new module `Sheaf.RingTheory.BinaryQuadraticModelDepth` states
`MvPowerSeries.binary_quadratic_model_depth`, with one postponed proof and no new
definitions. The existing node is unchanged except for its `lean` record.

The node and Lean correspond as follows:

- The arbitrary field is `(F : Type u) [Field F]`, with explicitly bound universe `u`.
- `S = F[[u,v]]` is `MvPowerSeries (Fin 2) F`, using the recorded Mathlib definition.
  The two parameters are `MvPowerSeries.X 0` and `MvPowerSeries.X 1`, with coefficient
  embedding `MvPowerSeries.C`.
- The three coefficients are `(a b c : F)`; not all zero is
  `habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0`.
- The introduced equation `Q = au² + buv + cv²` is rendered by `(Q : MvPowerSeries
  (Fin 2) F)` and its displayed defining equality `hQ`. This merely names the node's
  explicitly specified series: it is universally quantified with that equality,
  with no restriction on the coefficient triple beyond `habc`.
- The first conclusion is `IsLocalRing.depth (R := S) S = 2`.
- The ring `S/(Q)` is the actual Mathlib ring quotient `S ⧸ Ideal.span {Q}`.
  `∃ (_ : IsLocalRing ...), ...` concludes its local-ring structure; it is not an
  additional assumption. This structure also includes nontriviality.
- Its maximal ideal is stated equal to `Ideal.map (Ideal.Quotient.mk (Ideal.span
  {Q})) (Ideal.span ({X 0, X 1} : Set S))`, exactly the quotient image of `(u,v)`.
- The last conclusion uses `IsLocalRing.depth` with scalar ring the quotient itself
  and module the quotient itself, and equals `1`. Thus this is intrinsic ring depth,
  not merely depth as an ambient-ring module.
- There is no characteristic or discriminant assumption. Therefore every
  characteristic is included. A triple with `b² - 4ac ≠ 0` is not the zero triple,
  so the particular case stated in the node is included without a redundant conjunct.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.C`,
  `MvPowerSeries.X`; the full coefficient-family definition is used unchanged.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth` and `IsLocalRing.depth`;
  the latter is depth with respect to the maximal ideal and has the module/ring
  arguments described above.
- The additional public import `Mathlib.RingTheory.MvPowerSeries.Inverse` provides
  the existing local-ring instance for multivariate series over a local ring.

All stated proof dependency modules are imported privately:
`WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
(`MvPowerSeries.power_series_field_cohen_regular_complete`),
`WeilConjectures.RingTheory.DepthQuotSMulTop`
(`IsLocalRing.depth_quotSMulTop_of_isSMulRegular`), and
`WeilConjectures.RingTheory.DepthOverQuotientRing`
(`IsLocalRing.depth_over_quotient_ring`). The multivariate-series proof dependency
is already publicly imported. The remaining proof dependency
`lem-trf-regular-local-regular-sequence-depth` has no Lean record or Mathlib match
at preparation time, so has no module to import. It is needed for the future proof,
not to formulate this statement. Its proof step is preserved in the docstring.

Source checked: `literature/stacks-project/curves.tex`,
`lemma-fitting-ideal` (Tag 0C4C), especially (1) implies (3), and
`lemma-nodal-algebraic` (Tag 0C49), the binary quadratic completion. The node's
accepted split explicitly gives the nonzero-quadratic generalization through
regular local depth, nonzerodivisors, depth drop (090R), and scalar-ring comparison
(0AUK); all four proof steps are carried into the theorem docstring.

Edge cases checked mathematically: `Q = u²` (`a=1,b=c=0`), `Q=uv`, `Q=v²`,
and `(u+v)²` in characteristic two are nonzero nonunit hypersurfaces and retain
depth one even when nonreduced. In characteristic two, `b=0` is permitted and
`b≠0` gives the nonzero-discriminant case. The zero quadratic is excluded by
`habc`; otherwise its quotient would have depth two, so this exclusion matters.
There is no finite-field, algebraic-closure, separability, reducedness, or
characteristic restriction.

Searches actually performed with the prescribed `msearch.py` wrapper:

- LeanFinder: "The quotient of formal power series in two variables over a field
  by a nonzero binary quadratic form is a local ring of depth one": eight hits,
  including `MvPowerSeries.instIsLocalRing`, univariate DVR/Weierstrass results;
  none states the binary quadratic depth computation.
- Loogle: `MvPowerSeries, IsLocalRing.depth`: zero hits.
- Mathlib grep: `MvPowerSeries.*depth|depth.*MvPowerSeries|binary.*quadratic`:
  one hit, a binary quadratic forms heading in LegendreSymbol/Basic, unrelated.
- LeanSearch: "A nonzero binary quadratic hypersurface quotient of formal power
  series over a field has depth one": eight hits about Weierstrass division,
  univariate domains and dimension-one finite length; no matching depth theorem.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `binary.*quadratic|quadratic.*depth|depth.*MvPowerSeries`: related formal Jacobian,
  nodal and Morse statements, none asserting this general depth statement.
- Direct `grep -rn` for the exact item id in `lean/WeilConjectures`: no match.
- Direct `rg` for the proposed declaration and `binaryQuadratic` in both source
  trees and `dag/lean_names_upstream.json`: no declaration clash.

No new nodes, dependency repairs, statement corrections, or disputes are required.

## Second reading by Q20

Self-check with the node JSON and final Lean file open; no independent reader is
claimed here (the dispatcher forbids starting other agents and assigns the
independent review to the maintainer). The field, arbitrary universe, explicit
coefficient embedding, three-coefficient nonzero condition, and defining equality
for `Q` match the node's setup. The conjunction gives ambient depth two and a
local quotient with the stated maximal-ideal image and intrinsic quotient depth
one. In particular the final depth expression uses the quotient as scalar ring,
which avoids confusing module depth over `S` with ring depth of `S/(Q)`.
The local structure is concluded existentially, not assumed. No discriminant,
reducedness, characteristic, or separability hypothesis has been introduced.
No mismatch was found in this rereading; only an explicit public Basic import was
added to make the recorded statement dependency directly visible.

Validation: prescribed `scompile.py Q20 lem-trf-binary-quadratic-model-depth`
compiled the final file in sandbox and library module modes, both cleanly
(1.4 seconds each). The node diff changes only `lean`; Lean lines all meet the
100-character limit and `autoImplicit` is disabled explicitly.
