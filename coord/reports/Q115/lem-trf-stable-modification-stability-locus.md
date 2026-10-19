## Worker report

The module `Sheaf.AlgebraicGeometry.StableModificationStabilityLocus` states
`AlgebraicGeometry.stable_modification_stability_locus` with `sorry` as its proof.  It also
adds two faithful encoding helpers in the same module:

* `MultipointedCurve.BaseChange` records a `MultipointedCurve` whose underlying
  `MultipointedPair` is exactly the canonical `MultipointedPair.baseChange`.
* `MultipointedCurve.BaseChangeHom` records a `MultipointedCurve.Hom` whose curve and marking
  maps are heterogeneously equal to the canonical maps induced by `Over.pullback.map`.

These helpers avoid replacing the canonical pullback by an arbitrary chosen map.  Their data is
only a presentation of the already specified pair and map; no existence proof is hidden in a
definition.

The theorem hypotheses render the node as follows.  `U₀` is `[IsIntegral U₀]`, and `t₀` has
`[LocallyOfFiniteType t₀]` and `[QuasiCompact t₀]`, giving the finite-type-over-`ℤ` base.  `L`
has `[Field L]`, `[Algebra U₀.functionField L]`, and `[IsSepClosure U₀.functionField L]`.
The valuation point `x : RiemannZariski.ValuationPoint U₀ L η` packages the valuation subring
`x.V : ValuationSubring L`, its centred map `x.centre : Spec x.V → U₀`, and the required generic
compatibility.  `X` and `Y₀` are the two `MultipointedCurve U₀` pairs, and `g : Y₀.Hom X` is the
compatible curve/marking morphism.  `[IsProper g.curve]` and `[IsProper g.marking]` render the
properness assumptions.  `hX` and `hD` are smoothness of the target generic curve and étaleness
of its generic marking, using the canonical generic map
`Spec L → U₀` through `U₀.fromSpecStalk (genericPoint U₀)`.  `hηcurve` and `hηmark` are the two
generic-fibre isomorphisms.  `hV` says that the canonical base changes along `x.centre` admit
presentations whose canonical map is `IsStable` over `Spec x.V`, with both proper component maps.

The conclusion produces an `RiemannZariski.QuasiModel U₀ L η`, a map
`l : Spec x.V ⟶ U.X`, and the equations `l ≫ U.map = x.centre` and
`Spec.map x.V.subtype ≫ l = U.generic`; these are the required factorization and compatibility
with the generic map.  It then supplies canonical base-change presentations over `U` and a
canonical-map presentation whose `hom.IsStable U.generic` gives the stable `η`-modification.
Finally it gives an open `V : U.X.Opens` containing `genericPoint U.X` such that both
`curveBaseChange V.ι` and `markingBaseChange V.ι` are isomorphisms.  The dense target opens and
schematic-density clauses are part of `IsStable`/`IsEtaModification`; the final `V` is the base
open requested by the node.

Dependencies used directly by the signature are:

* `Mathlib.AlgebraicGeometry.Properties.IsIntegral` (node `def-pc-integral-scheme`);
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType.LocallyOfFiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.QuasiCompact`
  (`def-weil-finite-type-morphism`);
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth.Smooth`, `...Etale.Etale`, and
  `...Proper.IsProper` (`def-sbc-smooth-morphisms`, `def-weil-etale-morphism`,
  `def-weil-proper-morphism`);
* `Mathlib.Topology.Sober.IsGenericPoint` and `Mathlib.CategoryTheory.Limits.pullback`
  (`def-sc-generic-point`, `def-pc-fibre-product`);
* `Sheaf.TraceFormula.MultipointedCurve.MultipointedCurve` and
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification.MultipointedCurve.Hom` with
  `Hom.curveBaseChange`, `Hom.markingBaseChange`, `Hom.IsStable`
  (`def-trf-multipointed-curve`, `def-trf-multipointed-curve-modification`);
* `Sheaf.AlgebraicGeometry.SemistableMultipointedPair.MultipointedPair` and its
  `ofCurve`/`baseChange` operations (`def-trf-semistable-multipointed-pair`);
* `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement.RiemannZariski.ValuationPoint` and
  `QuasiModel` (`lem-trf-riemann-zariski-finite-refinement`).

Edge cases checked: the multipointed-curve structure permits an empty marking and nonproper or
nonseparated curve; the fibre-dimension fields permit empty fibres; `x.V` may have height zero;
no characteristic or degree-prime-to-an-integer hypothesis was introduced; the generic open is
required explicitly to contain the generic point; and all universes are bound by the single
scheme/field universe `u` with `autoImplicit false`.

Searches made:

* `msearch.py ... leanfinder "constructible stable locus and dense isomorphism open for a
  spread modification"`: only rational-map dense-open and dominant-map results; no stable
  marked-curve theorem.
* `msearch.py ... loogle "MultipointedCurve.Hom.IsStable, RiemannZariski.QuasiModel"`: zero
  hits (unknown identifier in Mathlib, so the project declarations were inspected directly).
* `msearch.py ... grep "stable.*modification|MultipointedCurve" Mathlib/AlgebraicGeometry`:
  zero hits.
* `rg` in `WeilConjectures/` found no stable-locus theorem or duplicate helper; only generic
  category-base-change infrastructure.
* `rg` in the project found the landed declarations in
  `Sheaf.TraceFormula.MultipointedCurve`,
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`, and
  `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`.

No `STATEMENT-DISPUTED` issue was found.  `scompile.py` compiled the module cleanly with no
errors or warnings.

## Second reading by Q115

Independent maintainer second reading of immutable delivery
`7f697b6bf5da5144bca17c88ce516516ceac53cd`, completed 2026-10-18.
The second reader did not write the module. The original placeholder in this section has
been replaced by this actual review; the Worker report above is retained.

I read the item node and all 15 statement dependencies from the immutable snapshot,
the delivered module, and the exact imported declarations in the read-only group and
upstream clones. I also read the landed owners `def-trf-multipointed-curve`,
`def-trf-multipointed-curve-modification`, and `def-trf-semistable-multipointed-pair`.
These faithfully supply the notions defined inline in the item. No private replacement
of a geometric notion or new independent definition node is needed.

The hypothesis and conclusion correspondence is as follows:

* Integral finite-type integer base: `U₀`, `[IsIntegral U₀]`, `t₀`,
  `[LocallyOfFiniteType t₀]`, `[QuasiCompact t₀]`. The lifted integer ring is the
  size-correct copy of the same base. No separatedness of U₀ is assumed.
* Separable closure: `L`, `[Field L]`, `[Algebra U₀.functionField L]`,
  `[IsSepClosure U₀.functionField L]`. The displayed generic map uses the actual
  generic stalk/function field, not a separately chosen field.
* Centred valuation: `x : RiemannZariski.ValuationPoint ...` contains
  `x.V : ValuationSubring L`, `x.centre`, and the equation identifying its restriction
  along `Spec.map x.V.subtype` with the prescribed generic map. A valuation subring
  of a field has that field as its fraction field. No finite-rank assumption is added.
* Two multipointed curves: `X Y₀ : MultipointedCurve U₀`. I checked every structure
  field: curve/marking schemes and structure maps, marking immersion, compatibility,
  flatness, local finite presentation, quasi-compactness, quasi-separatedness, and
  pure fibre dimensions one and zero. The last two finiteness properties belong to
  finite presentation and do not impose separatedness.
* Compatible proper pair: `g : Y₀.Hom X`, with its two over-base equations and
  marking square; `[IsProper g.curve]`, `[IsProper g.marking]`.
* Smooth generic target, etale generic marking, and generic isomorphisms: `hX`,
  `hD`, `hηcurve`, `hηmark`. These use Spec L rather than Spec k(U₀). This is
  equivalent, since smoothness, etaleness and being an isomorphism both ascend and
  descend under the faithfully flat field extension k(U₀) → L. It adds no hypothesis
  and drops no case. The same observation applies to U.generic in the conclusion.
* Stable valuation pullback: `hV` supplies two `BaseChange` presentations and a
  `BaseChangeHom`. `asPair` fixes the entire canonical pair, including the structural
  maps and marking. The two `HEq` fields fix precisely the maps of the ordinary
  pullback functor; they do not allow arbitrary maps or conjugation by chosen
  automorphisms. Equalities transport the property proofs, so requiring these
  presentations is exactly the assertion about the canonical base change.
  `IsStable` includes properness, dense-open and generic isomorphisms, semistability,
  and absence of contracted exceptional components. The extra two properness
  conjuncts in hV are redundant, not stronger.
* The quasi-model is `U : RiemannZariski.QuasiModel ...`: its inherited integral
  scheme, separated finite-type map, generic-point condition and factorization are
  exactly those of the dependency node. The map `l` and the next two equations give
  both required compatibilities, including Spec L.
* Stability over U is `f'.hom.IsStable U.generic` on the canonical presentations.
  I unfolded `IsEtaModification`, `IsSemistable`, `specialPoints`, and `IsStable`.
  Schematic density is injectivity on sections on every open, on both target and
  source opens. The latter also follows from flatness over the integral base and
  the generic base open. Nodal completions are `Orgogozo.IsOrdinaryDoublePoint`,
  with its scalar-compatible equivalence to `MvPowerSeries (Fin 2) Ω / (uv)`.
  The etale marking and relative smooth-locus condition are present. Exceptional
  projective-line components are tested over the algebraic closure of each residue
  field, with at most two distinct special points and singleton contracted image.
* Final open: `V : U.X.Opens`, `genericPoint U.X ∈ V`, and the two `IsIso`
  clauses for the entire base restrictions. Because U.X is integral, this open is
  dense. No explicit redundant `Dense` conjunct is needed. The valuation lift is
  to U; it is not required to lie in this final isomorphism open.

Source checks: Temkin arXiv:0707.3953v3, §1.2 (printed p. 2), Remark 3.1.1
(pp. 14–15), Lemma 3.2.2 and Corollaries 3.2.5/3.2.7, Lemma 5.1(ii) (p. 34),
and the second paragraph of the proof of Theorem 1.5 (p. 36). I checked the two
separate limit applications and the flat schematic-density argument against Stacks
01ZM(2),(3), 05F4, and 081I. The source supports the given statement. There is no
statement correction and no citer audit is required.

Edge cases: empty marking and empty fibres are permitted; pure dimension is vacuous
on an empty fibre. The curve can be nonproper or nonseparated over the base. The
integral base and the quasi-model are nonempty. A height-zero valuation and a trivial
separable closure are allowed. All characteristics remain allowed. No additional
Noetherian, field perfection, discrete valuation or genus assumption occurs. The
universe u is bound; fields, spectra and schemes use the same scheme universe, and
there is no independent test universe that could make a condition vacuous. A separable
algebraic closure can be taken in this universe. There is no site-universe issue.

Duplicate checks: searched Mathlib/AlgebraicGeometry, upstream WeilConjectures, and
the group's AlgebraicGeometry/TraceFormula Lean modules for stable modification,
stability locus, multipointed base change and BaseChangeHom. I read the nearby
finite-presentation-spread theorem: it spreads data and does not assert this stable
locus result. Existing pair base change and Hom stability are reused. The two helpers
only present canonical existing data. I also checked the worker's recorded LeanFinder,
Loogle, LeanSearch and grep results. The report's claim of zero grep hits for the
very broad word constructible should not be read literally as an absence of generic
constructible-set APIs: those exist and are explicitly reused by the proof plan.

Findings and repairs:

* H8: the original short proof docstring omitted the separate centre-local and
  principal-neighbourhood applications of 05F4, field descent at every valuation
  point, the fibre criteria for the marking, and the density checks. The replacement
  module gives all seven steps, names the DAG inputs, and explains descent of the
  conditions expressed over L. It also makes source-open density explicit.
* H9 / brief-stage2 §3: available proof-dependency imports were missing. The
  replacement imports their recorded modules without public re-export, and publicly
  imports the pair definition actually used in the signature.
* H11 and the required report gate: the delivered second-reading section was only
  a statement that no reading occurred. This section supplies the independent
  clause-by-clause reading, edge cases, searches, source checks and all findings.

The two records contain real data/equalities and no sorry. The only postponed proof
in the module is the named theorem, whose entire proof remains `by sorry`. All three
declarations have source/blueprint docstrings. There are no lines over 100 columns,
no pro-etale replacement, and no dropped route-pivot dependencies or machinery. The
shared branch has no repair note for this item. The TeX statement and Lean signature
are unchanged; `lean.statement` equals the signature in the project's whitespace
normal form. The existing dependency records are usable; no §1(B) or §1(C) repair
is necessary. Unstated proof-plan lemmas are stage-3 inputs, not missing objects
needed to type this stage-2 statement.

Compiler evidence: I reproduced the original via
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q115
lem-trf-stable-modification-stability-locus
snapshot/lean/Sheaf/AlgebraicGeometry/StableModificationStabilityLocus.lean`:
rc 0, sandbox 3.0 s, library module 3.5 s, no errors or warnings. I also compiled
the complete replacement `fixes/StableModificationStabilityLocus.lean` via the same
wrapper: rc 0, sandbox 2.8 s, library check 2.8 s, no errors or warnings. The wrapper
uses its isolated server side overlay at this installation; its output confirms
60-second per-file limits and temporary `.lbuild` directories. The basename-only
fix is compiled under the wrapper's fallback module `Sheaf.Stage2.Check`.
No lake/global build, direct ssh command, clone edit, live Lean write, claim,
delivery or Git mutation was performed.
