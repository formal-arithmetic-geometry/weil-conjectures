## Worker report

Stage 2, Q54, 2026-10-22. The delivery states
`IsLocalRing.exists_ringEquiv_regular_complete_coefficients` in
`Sheaf.RingTheory.RegularCompleteCoefficientCoordinates`. Its sole proof is `sorry`.
No definition, helper theorem, dependency module or new node is introduced. The node is
copied from the current repository and changed only in `lean`. Q74's existing review
and split are stage 1; they provide the proof outline, not an existing Lean statement.
There was no retained Lean module or node in the sandbox, only dispatch markers.

Source read: `literature/stacks-project/algebra.tex`, Tag 0C0S,
`lemma-regular-complete-containing-coefficient-field`, lines 45036–45066, including the
proof of (2). The source fixes the coefficient field map, evaluates at a cotangent
basis, proves surjectivity using 0315 and injectivity using 00KW. The node's arbitrary
d generators provide such a basis. No statement correction or dispute is needed.

Hypothesis and conclusion correspondence:

- The arbitrary field is `(k : Type u) [Field k]`; the target ring is
  `(C : Type v) [CommRing C]`. Nonzeroness is inherited from
  `IsRegularLocalRing C` through `IsLocalRing C`; a separate `Nontrivial C` binder
  was removed after the compiler reported overlapping instances. Universes u and v
  are independent.
- Noetherian, local and regular are exactly `[IsRegularLocalRing C]`, whose Mathlib
  class extends both `IsLocalRing C` and `IsNoetherianRing C`. The maximal ideal
  `maximalIdeal C` is the node's p. This uses the ring clause of the regular-scheme
  dependency's unchanged `mathlib_match`, not its scheme-only declaration.
- Finite dimension d is `(d : ℕ)` and
  `hdim : ringKrullDim C = (d : WithBot ℕ∞)`; no positivity assumption is imposed.
- Completeness for precisely p is `[IsAdicComplete (maximalIdeal C) C]`, including
  separatedness, with no auxiliary chosen topology or additional completeness hypothesis.
- The specified coefficient map is `(c : k →+* C)`. The hypothesis
  `hres : Function.Bijective ((residue C).comp c)` says that the induced map to
  the residue quotient is an isomorphism; it does not choose a different coefficient field.
- Every given length-d list is `(t : Fin d → C)`. Membership in p is `ht`, and
  generation is `hgen : Ideal.span (Set.range t) = maximalIdeal C`.
- The source is exactly `MvPowerSeries (Fin d) k`. The conclusion supplies a ring
  equivalence `e` with `∀ a, e (MvPowerSeries.C a) = c a`, the explicit compatibility
  making it a k-algebra isomorphism for the given c. There is no freely chosen algebra
  structure and no change in coefficients.
- `∀ i, e (MvPowerSeries.X i) = t i` fixes all parameter images. Together with the
  coefficient equation these characterize the canonical evaluation uniquely by the
  published `MvPowerSeries.exists_ringHom_of_isAdicComplete`. Thus the existential
  equivalence is pinned to the prescribed map, rather than an arbitrary abstract
  isomorphism or an unspecified Nonempty witness. No canonical data definition is
  obtained from an underdetermined existence theorem.
- Complete local and continuous in both directions is rendered without a second
  topology definition: for every r, `Ideal.comap e.toRingHom (maximalIdeal C ^ r)`
  equals `(Ideal.span (Set.range MvPowerSeries.X)) ^ r`. These ideal powers form the
  adic neighbourhood bases. Since e is bijective this equality also says that e maps
  the source ideal power onto the target ideal power; it proves continuity of the
  inverse as well as of e. At r = 1 it identifies the maximal ideals. This is an
  explicit equivalent formulation of the asserted complete local algebra isomorphism.
- The final clause `(d = 0 → Function.Bijective c)` explicitly renders the node's
  empty-list assertion that c itself is an isomorphism. The main equivalence also
  includes d = 0, rather than restricting to positive dimension.

Dependency declarations opened with signatures and docstrings:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (lines 192–197).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` (lines 47–54).
  The dependency node `def-weil-regular-scheme` records this exact ring notion in
  `mathlib_match`; `Sheaf.AlgebraicGeometry.IsRegularScheme` was also opened, and
  gives the distinct scheme clause that is not used by this ring statement.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` (lines 26–31).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (lines 45–56).
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` (lines 84–87), its
  coefficient map `MvPowerSeries.C` and its variables `MvPowerSeries.X`.

The proof imports are the modules of all already stated proof dependencies:
`WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
(`MvPowerSeries.power_series_field_cohen_regular_complete`),
`WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete`
(`MvPowerSeries.exists_ringHom_of_isAdicComplete`),
`Mathlib.RingTheory.AdicCompletion.Functoriality`
(`surjective_of_mk_map_comp_surjective`), and
`Mathlib.RingTheory.KrullDimension.Regular`
(`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`).
Their complete relevant signatures and proof documentation were read. The module's
statement docstring carries the node's five proof steps with the cited node ids.

Edge cases checked: d = 0 forces p = 0 from the empty generating range, and the
residue condition then makes c bijective. For C = k[[U]], a unit multiple of U is
allowed and produces the expected change of coordinates. No characteristic or
perfectness assumption is used: imperfect fields and positive characteristic remain
included. The zero ring is excluded exactly as the node requires. The singular
ring k[[U,V]]/(UV) has dimension one but needs two maximal-ideal generators, so it
cannot satisfy the dimension-one generation hypothesis; it is also not regular.
The ideal-power equation at r = 0 compares the two whole rings and adds no restriction.

Searches actually run for this delivery using the prescribed wrapper:

- LeanFinder: `A complete regular local ring with a specified coefficient field is
  isomorphic to a multivariate formal power series ring by any generating system of
  parameters` returned eight candidates, including Weierstrass preparation and
  `MvPowerSeries.instIsLocalRing`; none is this specified-coefficient coordinate theorem.
- Loogle: `"IsRegularLocalRing", "MvPowerSeries"` returned zero hits.
- Mathlib grep, RingTheory: `IsRegularLocalRing.*MvPowerSeries|MvPowerSeries.*IsRegularLocalRing|coefficient.*coordinates`
  returned zero hits.
- LeanSearch: `complete regular local ring with coefficient field is formal power
  series ring` returned eight candidates: univariate local, DVR and residue facts,
  Laurent-series completion equivalences and Weierstrass division. None has arbitrary
  complete regular local target C with prescribed c and t.
- Direct rg of `lean/WeilConjectures` for the exact node id returned no hit. Searches
  of the RingTheory modules for regular/complete/coefficient terminology found the
  existing Cohen presentation and full-parameter results. I opened
  `WeilConjectures/RingTheory/PowerSeriesFullCoordinatesField.lean`: its theorem
  `MvPowerSeries.exists_algEquiv_full_parameters_field` has a target already of the
  form `MvPowerSeries (Fin n) K`, and does not state this result for general C.
  Searches of `lean/Sheaf/RingTheory` found `RelativeCohenFlatPresentation` using
  the informal item in its proof, but no statement of the item.
- Direct rg of Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json` found no
  existing `exists_ringEquiv_regular_complete_coefficients` declaration.

All semantic search services answered successfully. Their exact calls and results
are in the wrapper-generated `searches.jsonl`. No search result is invented and no
failure is represented as an absence result.

## Second reading by Q54

I reread the node and the complete new module in a separate pass. This is the
single worker's second reading; the dispatch explicitly forbids starting another
agent, and the maintainer's independent review remains necessary.

I matched each hypothesis: arbitrary field; nonzero commutative target; the class
including Noetherian and local regularity; finite dimension exactly d; completeness
for its maximal ideal; the given ring map with bijective residue composite; each
of the d elements in that ideal; and generation of that ideal. The conclusion fixes
both constants and variables, so it concerns precisely the specified evaluation.
The ring equivalence plus its coefficient equation is an algebra equivalence for
c, and the comap equation on every power is the two-sided adic continuity and local
condition. The d = 0 implication is present explicitly. No hypothesis, characteristic,
universe equality, chosen alternative coefficient field or arbitrary coordinate
isomorphism was introduced. The ring clauses of the dependency records suffice;
there is no need to duplicate their definitions or modify a dependency.

The single theorem has `sorry` as its complete proof; no data is postponed. All
variables and universes are explicit under `set_option autoImplicit false`. There
are no private definitions, local notation or local instances. The compiler found an overlapping `Nontrivial C` instance binder; I removed
it because regular locality already supplies it, preserving the nonzero hypothesis.
I found no further semantic mismatch requiring a change in this second reading.

Validation: the prescribed `scompile.py Q54
lem-trf-regular-complete-coefficient-coordinates` compiled the final file in both
sandbox module mode and its library module path cleanly (3.9 s and 5.2 s). The only
node field changed is `lean`, and every Lean source line is at most 100 characters.
