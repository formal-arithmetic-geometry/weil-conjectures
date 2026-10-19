## Worker report

The module `Sheaf.TraceFormula.DivisorialLogChart` states
`AlgebraicGeometry.sncDivisorialLogChart`. It uses the existing smooth strict normal
crossings divisor predicate and the canonical open complement of `Z.subschemeι`.
The hypotheses are rendered by `(F : Type u) [Field F] [IsAlgClosed F]`, the scheme
morphism `(V : Scheme.{u}) (f : V ⟶ Spec (.of F)) [Smooth f]`, the finite-type
conditions `[LocallyOfFiniteType f] [QuasiCompact f]`, and
`(Z : V.IdealSheafData) (hZ : Z.IsSmoothStrictNormalCrossingsDivisor f)`. The
conclusion supplies the locally Noetherian structure and dense range of the canonical
open complement, then `IsDivisorialFineSaturatedLogRegularPair` for that complement.
For every geometric point `t : Spec (.of Ω) ⟶ V`, the existential `r`, pointed etale
neighbourhood `W,w`, and monoid map `β` render the `N^r` chart; `IsFineSaturatedMonoid`
and `IsDivisorialStalkChart` render finite saturation and the stalk pushout chart.
`χ : Associates (divisorialStalk ...) ≃* Multiplicative (Fin r → ℕ)`, together
with its compatibility on every chart germ, renders the characteristic monoid
identification induced by the chart. The `hA` conjunct renders strict-local
regularity. The clause `∃ s : List (strictLocalRing V t),
IsLocalRing.IsRegularSystemOfParameters ((List.ofFn ...) ++ s)` renders that
the ordered boundary tuple extends to a full regular system of parameters. The
following `IsRegularRing` quotient and
`ringKrullDim` equality render regularity of `A/(t₁,…,tᵣ)` and
`dim A = dim A/(t₁,…,tᵣ) + r`.

The statement dependencies used are `Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`),
`Sheaf.AlgebraicGeometry.LogRegularPair`
(`AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`,
`divisorialSections`, `divisorialStalk`, `divisorialGerm`, `strictLocalRing`,
`strictLocalGerm`, `IsFineSaturatedMonoid`, `IsDivisorialStalkChart`),
`Sheaf.RingTheory.IsRegularSystemOfParameters`
(`IsLocalRing.IsRegularSystemOfParameters`), and
`WeilConjectures.ConstructibleSheaf.OpenClosedStratification`
(`AlgebraicGeometry.Scheme.openComplementOfIsClosedImmersion`). Mathlib leaves are
used through these declarations and include `Smooth`, `LocallyOfFiniteType`,
`IsClosedImmersion`, `IsAlgClosed`, `ringKrullDim`, and `IsRegularRing`.

Edge cases checked are the empty divisor (`r = 0`, empty boundary list and
trivial characteristic monoid), a zero-dimensional strict local ring, a single
component, and a transverse two-component crossing. For an empty divisor on the
affine line at a closed geometric point, the boundary list is empty but the
remaining list `s` has length one. At a generic point the strict local ring is a
field and both lists are empty. In an ambient local ring of dimension `d` at an
`r`-fold crossing, the extension has length `d - r`; it may be nonempty even for
`r > 0`. The canonical empty-divisor complement is all of `V`.

Searches for an existing statement or definition found no match: `msearch.py Q85
lem-trf-snc-divisorial-log-chart leanfinder` with queries about smooth transverse
normal-crossings divisorial charts returned only generic smoothness declarations;
`msearch.py ... loogle "LogRegular, NormalCrossing, Divisorial"` returned no hits;
`msearch.py ... grep "normalCrossing|normal_crossing|logRegular|divisorial"`
and direct `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf` found no theorem
with this statement. The existing divisorial log-pair and smooth SNC definitions
were therefore reused rather than copied.

The earlier object-introduction issue was resolved by the recorded §1(C)
correction to use the canonical open complement and explicit chart data. There
is no unresolved statement dispute.

## Second reading by Q85

I reread the corrected node, its Lean signature, and every imported declaration.
`F`, smooth finite-type `f`, and the smooth strict normal crossings divisor `Z` are
exactly the geometric hypotheses. The existential `hU` is the canonical complement's
dense-range clause, and the following predicate is precisely the recorded divisorial
fine-saturated log-regular definition. The pointwise `r,W,w,β` conjunct gives the
étale-local free chart, its stalk pushout, characteristic, parameter prefix, regular
quotient, and dimension drop. The repaired parameter clause now existentially
supplies the remaining list
`s`: the boundary list is a prefix of the full parameter list. In particular,
`Fin 0` and `List.ofFn` give an empty boundary list without forcing dimension zero.
The natural statement correction is the
necessary introduction of `U`, its canonical morphism, and the explicit local objects;
all follow the cited ILO and Stacks source. The sole citer,
`lem-trf-nodal-pair-projective-resolution`, still holds because it uses the resulting
log-regular base pair.

## Statement corrected

The old statement referred to `(V,|Z|)` and its divisorial log structure without
introducing the open complement morphism required by the existing Lean definition,
and left the local chart objects implicit. Following ILO VI §§1.4--1.5(i) and Stacks
0BIA, the corrected statement uses `Z.subschemeι` and its canonical open complement,
asserts its dense range, and spells out the chart, characteristic, parameter,
quotient-regularity, and dimension clauses. Citer `lem-trf-nodal-pair-projective-resolution`
holds true: its use of the log-regular base pair remains valid.

## Repair of returned delivery (H3)

The returned review identified that the earlier `Nonempty (Associates ... ≃ Multiplicative ...)` clause was an unrelated type equivalence: it did not identify the characteristic class of any chart element. I replaced it with an explicitly supplied multiplicative equivalence
`χ : Associates (divisorialStalk j t) ≃* Multiplicative (Fin r → ℕ)` and the compatibility clause
`∀ x, χ (Associates.mk (((divisorialGerm j t W w).comp β) x)) = x.down`.
Thus the equivalence is induced by the actual divisorial chart: every chart monomial, including every standard basis element and its boundary parameter, is sent to its specified characteristic coordinate. The clause also handles `r = 0`, where the source and target monoids are trivial. The `IsDivisorialStalkChart` conjunct remains in place, so this compatibility is attached to the genuine pushout chart rather than an arbitrary equivalence.

The module was recompiled with `scompile.py`; the only diagnostic was the expected style warning, which was repaired by wrapping the compatibility expression. The node's `lean.statement` was regenerated verbatim from the repaired theorem signature, and the statement-change record notes this H3 repair.


## Repair of returned delivery (H3: parameter extension)

The immutable returned head `820f8389d3ad` asserted that the boundary tuple itself
was a full regular system of parameters. Reading the retained packet against the
current main node confirmed the same mismatch: the natural statement already says
"part of a regular system of parameters", while the Lean predicate requires the
whole list to generate the maximal ideal and have length equal to the dimension.
The initial saved-packet dry run passed at `9f501beee1`; this mechanical pass did
not resolve the mathematical H3 finding.

The signature now asserts the existence of a list `s : List (strictLocalRing V t)`
for which `IsLocalRing.IsRegularSystemOfParameters ((List.ofFn ...) ++ s)` holds,
using the actual boundary images in their original order. The quotient ideal and
the dimension equation still use only the boundary equations, not the extension.
No definition, hypothesis, chart-compatibility clause, or natural node statement
needed changing. The node's `lean.statement` is regenerated verbatim from this
signature. The `statement_change` record documents the repaired translation.

Source check: `literature/stacks-project/etale.tex`,
`lemma-strict-normal-crossings` (Tag 0BIA), explicitly chooses additional
`x_{r+1}, ..., x_n` after the component equations. This is exactly the list `s`.
The empty divisor on A¹ at a closed geometric point is now included: `r = 0`
and `s` supplies its one local parameter. If the boundary rank equals the local
dimension, `s` may be empty. If the ring has dimension zero, both lists may be
empty.

The citer audit was repeated over all DAG node files. The sole node naming this
item in `stmt_deps` or `proof_deps` is
`lem-trf-nodal-pair-projective-resolution`; its use still holds, because it needs
the characteristic identification and log regularity, both retained. Other text
hits do not cite this item in either dependency list. No citer was edited.

Validation of the parameter-extension repair: `scompile.py Q85
lem-trf-snc-divisorial-log-chart lean/Sheaf/TraceFormula/DivisorialLogChart.lean`
passed both sandbox and library file checks without diagnostics. The self-check
confirmed the exact recorded signature, explicit binders and universes, the
100-column Lean limit, and the single expected postponed theorem.
