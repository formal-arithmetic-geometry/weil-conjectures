## Worker report

Repair of the returned stage-2 delivery at immutable head `13545ff4b94a`.
The retained module and node were inspected first, and the prescribed saved-packet
`deliver2.py --no-push` was started before edits. The independent mathematical
return identifies four defects that a compilation alone cannot detect. All four
are repaired below. The current shared node and retained node differ only in
`lean`; the mathematical statement, dependencies, and proof remain unchanged.

`Sheaf.AlgebraicGeometry.LogSmoothLogRegular` packages the chart data in
`AlgebraicGeometry.InjectiveFSLogChart` and states the single postponed theorem
`AlgebraicGeometry.logSmooth_logRegular`. No theorem is proved. The helper is data
for the chart already specified by this node, not a second log-structure or
fine-saturation definition. Its fields have real types and no `sorry` data.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Locally Noetherian fs log schemes X and Y | `X Y : FineSaturatedLogScheme.{u}`, reusing its `locallyNoetherian`, `logStructure`, and `fineSaturated` fields |
| Morphism of log schemes f from X to Y | `f : EtaleLogHom X Y`, including its structural compatibility and naturality |
| Y log regular in the stratum and dimension sense | `hY : Y.IsLogRegular`, the actual strict-local quotient regularity and characteristic-rank dimension formula |
| Étale locally on X and Y | `hcharts` quantifies over every geometric `t` of X and supplies a chart `c` with `Nonempty ((Scheme.pointSmallEtale t).fiber.obj c.V)`; `c.V` and `c.W` are étale neighborhoods, related by `c.map` over f |
| Fine saturated chart monoids P and Q | `P`, `Q`, `instP`, `instQ`, with `fineP : IsFineSaturatedMonoid P` and `fineQ : IsFineSaturatedMonoid Q` |
| Charts into the given log structures | `chartY`, `chartX`, `chartY_isChart`, `chartX_isChart`; `IsChart` is the recorded associated-log pushout test at every geometric point of the neighborhood |
| Homomorphism g compatible with f | `g : P →* Q` and `chart_compatibility`, which equates `f.sectionMap W V map map_over (chartY p)` with `chartX (g p)` for every p |
| Compatibility with scheme structure maps | `y_chart` and `x_chart` require the pullback of each monomial `[p]` or `[q]` to equal the structural image of the corresponding log section; `Scheme.ΓSpecIso.inv` supplies the canonical monomial section on Spec |
| Monoid ring Z[S] | `MonoidAlgebra ℤ S`, whose basis elements are `MonoidAlgebra.single s 1`; the map for g is `MonoidAlgebra.mapDomainRingHom ℤ g` |
| The comparison to the specified fiber product | `comparison` has that pullback as target; `comparison_fst` and `comparison_snd` fix both projections to `map` and `x`, and hence fix the comparison uniquely |
| Injective map on group completions | `gp_injective` for `Algebra.GrothendieckGroup.lift` of g |
| Torsion-free cokernel | `cokernel_torsion_free`: for positive n, if z^n is in the image then z is in the image, equivalently no nontrivial n-torsion in the quotient group |
| Smooth or étale comparison | The single disjunction `Smooth c.comparison ∨ Etale c.comparison` in `hcharts`; the redundant copy formerly inside the structure was removed |
| X log regular | The first conclusion `X.IsLogRegular` |
| Its triviality locus is dense open | `U : X.scheme.Opens`, `hd : DenseRange U.ι`, and `X.logStructure.trivialityLocus = (U : Set X.scheme)` |
| Canonical identification by the structure map | The prescribed divisorial presheaf is a sheaf, and there is an isomorphism `e : X.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι` satisfying `e.hom ≫ divisorialStructuralMap U.ι = X.logStructure.alpha` |
| The complement pair is log regular | `IsDivisorialFineSaturatedLogRegularPair X.scheme U.toScheme U.ι hd`, with the open-immersion and locally Noetherian instances supplied explicitly |

The presheaf isomorphism is also a sheaf isomorphism because both presheaves are
sheaves. Its equality with the structural inclusion is essential: sectionwise,
the divisorial structure map is the subtype inclusion into regular functions, so
this equality determines `e.hom` uniquely. The statement does not merely assert
that two abstract sheaves happen to be isomorphic. Likewise the chart scheme maps
are determined by their prescribed values on the monomial generators, and the
two pullback projection equations determine the comparison. None of these is an
unconstrained comparison-map parameter.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogHom`, `EtaleLogStructure.IsChart`,
  `EtaleLogStructure.trivialityLocus`, `FineSaturatedLogScheme.IsLogRegular`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `IsFineSaturatedMonoid`, `divisorialLogPresheaf`, `divisorialStructuralMap`,
  `IsDivisorialFineSaturatedLogRegularPair` (available publicly through the first
  module and also imported for the proof plan).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- Mathlib's `MonoidAlgebra`, `MonoidAlgebra.mapDomainRingHom`,
  `Algebra.GrothendieckGroup`, `Scheme.ΓSpecIso`, and categorical pullbacks.

The theorem docstring now carries every proof step from the DAG, with each step's
named dependencies. Recorded proof dependencies have ordinary proof imports.
The two proof nodes without Lean records (`lem-trf-fs-face-sharpening` and
`lem-trf-formal-monoid-extension-model`) cannot yet be imported; their intended
uses remain explicitly documented in the proof. No additional statement
hypothesis is substituted for either missing proof.

Edge cases checked in the statement reading:

- Empty X: geometric chart coverage is vacuous, and the empty open satisfies the
  specified triviality-locus conclusion. This avoids requiring a single global
  chart even when X is empty.
- Disjoint components: one chart on one component is insufficient; the universal
  geometric-point quantifier requires a pointed chart on every component.
- Trivial log structure and empty boundary: U is all X, the divisorial monoid is
  the units, and the group cokernel may have rank zero.
- Identity chart `P = Q`, `g = 1`: zero cokernel is permitted. The exponent test
  includes n = 1 and excludes n = 0, exactly as torsion-freeness requires.
- Unit chart factors and non-sharp fs monoids: no sharpness, trivial-unit-group,
  characteristic-monoid injectivity, or characteristic restriction was added.
- A chart restricted to a proper neighborhood cannot imply global regularity:
  the repaired quantifier explicitly rules out that saved-packet defect.
- Arbitrary scheme maps into the monoid spectra and unrelated abstract log-sheaf
  isomorphisms fail the newly required monomial and structural-map equalities.

Sources read: the local ILO PDF, Exposé VI 1.1–1.9, printed pp. 69–71
(PDF pp. 75–77). Section 1.1 specifies étale fs charts and the standing locally
Noetherian assumption; 1.4 gives the dense triviality locus and the divisorial
identity; 1.8 gives preservation and 1.9 exhibits the injective torsion-free
chart test. No change to the node's mathematical statement is needed.

Searches retained from the packet include LeanSearch for divisorial recovery,
LeanFinder for log-smooth preservation, Loogle for `LogRegular`, and Mathlib,
WeilConjectures, and side-library text searches. None found this entire theorem.
For the repair, the following searches were repeated to check for a newly
available exact interface:

- `msearch.py ... leanfinder "An etale locally charted fs log morphism with
  injective group completion and torsion free cokernel preserves log regularity
  and canonically identifies its source log structure with the divisorial log
  structure"`: eight results, all ordinary scheme étale/smooth declarations;
  none contain logarithmic structures or divisorial recovery.
- `msearch.py ... loogle "LogRegular, LogSmooth, InjectiveFSLogChart"`: zero
  results, unknown identifier `LogRegular`.
- `msearch.py ... grep "LogSmooth|logSmooth_logRegular|InjectiveFSLogChart"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` for those names and the exact node id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf`:
  only the proof-plan citation in `LogRegularToricRefinement.lean`; no duplicate
  declaration. The existing `logRegular_divisorialStructure` was read: it is a
  proof input after regularity, not the present preservation theorem.

There are no new nodes, dependency-record repairs, or mathematical statement
corrections, and no `STATEMENT-DISPUTED` finding.

## Second reading by Q50

This is a separate self-check pass by the dispatched worker, not a claim that
another agent was started. The launcher expressly forbids starting agents. I
reopened the node, its four statement-dependency interfaces, and the revised
module, and matched every hypothesis and conclusion in the table above.

The returned head lacked fine-saturation on P and Q, log-chart compatibility
with f, monomial constraints on the two maps to monoid spectra, and compatibility
of the concluding isomorphism with the structural map. These were repaired by
`fineP`/`fineQ`, `chart_compatibility`, `y_chart`/`x_chart`, and the equation for
`e.hom`, respectively. Both projection equations are retained, so the resulting
comparison is the prescribed one.

This pass additionally caught that the saved packet asserted existence of just
one chart and did not identify its dense open with the actual triviality locus.
The first could be witnessed on a small neighborhood (even the empty scheme)
and say nothing about other points. It now quantifies over every geometric point
and requires a lift into that chart. The conclusion now uses an actual scheme
open U and equates it with `trivialityLocus`. The duplicate smooth-or-étale
hypothesis was removed, the presheaf/sheaf levels of the isomorphism were made
consistent, and the full proof docstring and proof imports were supplied.

The node's `lean.statement` is extracted verbatim from the final theorem
signature. Every variable and universe is explicit (`autoImplicit false`), all
Lean lines are within 100 columns, and the only postponed proof is the named
item theorem. The final `scompile.py` run passed for both the sandbox and library paths,
with no errors or warnings. The first repaired-packet dry run reported one
docstring-ending warning; the extra blank line was removed and the clean
compilation confirms that fix. Delivery preflight is run next with `deliver2.py`.
