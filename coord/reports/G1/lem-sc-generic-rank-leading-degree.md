## Worker report

The module `Sheaf.AlgebraicGeometry.GenericRankLeadingDegree` states
`AlgebraicGeometry.Scheme.Modules.exists_polynomials_coeff_eq_genericRank` with one
`sorry` and no new definitions. The item node changes only in `lean`.

Hypothesis and clause correspondence:
- Field K: `(K : Type u) [Field K]`.
- Integral proper K-scheme Y: `(Y : Scheme.{u}) [IsIntegral Y]`,
  `[Y.Over (Spec (.of K))]` and `[IsProper (Y ↘ Spec (.of K))]`.
- Dimension g: `(g : ℕ) (hdim : topologicalKrullDim Y = g)`; this is an
  equality in `WithBot ℕ∞`, so neither infinite dimension nor the empty
  scheme is inadvertently assigned dimension zero.
- Ample O_Y-module M: `(M : Y.Modules)` and
  `hM : IsAmple (Y ↘ Spec (.of K)) M`. The recorded IsAmple definition
  includes invertibility; no independent invertibility hypothesis is added.
- Coherent E: `(E : Y.Modules)` and
  `hE : RingedSpace.IsCoherent Y.toRingedSpace E`.
- Nonempty open U: `(U : Y.Opens)` and `hU : (U : Set Y).Nonempty`.
- Free restriction of rank r: `(r : ℕ)` and the isomorphism `e` from
  `E.over U` to `SheafOfModules.free` on `ULift.{u} (Fin r)` over the restricted
  structure sheaf `(moduleRings Y.toRingedSpace).over U`. This is restriction
  via the over-site, the same restriction used by the recorded coherence
  definition; it is not the upstream non-tensor module pullback.
- Numerical polynomials: existential rational polynomials `P Q`, with evaluations
  equal to the two integer Euler-characteristic functions at EVERY `m : ℕ`,
  including zero. This uses the exponent convention of the recorded
  `Scheme.Hom.exists_polynomial_hilbertFunction` (not merely eventual agreement).
  Integer-valuedness on this domain follows directly from the evaluation clauses.
  Polynomials agreeing on all natural numbers are unique over ℚ, so existential
  representatives do not permit an arbitrary choice of the coefficient.
- The m^g coefficient comparison: `P.coeff g = (r : ℚ) * Q.coeff g`.
  The factorial-scaled formulation in the node is explicitly labelled equivalent,
  not an additional claim: multiplying this equality by `(g! : ℚ)` gives it,
  and cancellation of this nonzero factor gives the converse.
  No bound or additional conclusion not stated in the item is imposed.

Dependency declarations read in full, with their docstrings:
- `WeilConjectures.AlgebraicGeometry.Modules.Ample`:
  `AlgebraicGeometry.IsAmple` (used), `Scheme.Hom.degree` (read; not needed for
  the direct coefficient statement), `Scheme.Hom.exists_polynomial_hilbertFunction`
  (recorded polynomial/exponent convention).
- `Sheaf.AlgebraicGeometry.Coherent`:
  `AlgebraicGeometry.RingedSpace.IsCoherent` (used directly).
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar` (used, provided by Ample's imports).
- `Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes`:
  `AlgebraicGeometry.Scheme.Modules.exists_coherent_filtration_integral_subschemes`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_add_of_shortExact`.
- `Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial`:
  `AlgebraicGeometry.Scheme.Modules.exists_mvPolynomial_eulerChar_tensorPowers`.
The last three are proof tools, not notions used by the signature. They are
not added as direct imports merely for the future proof. The docstring carries the item's two proof steps and
names each of these tools. The Euler-additivity record has explicit finiteness
and vanishing prerequisites, to be supplied from proper coherent cohomology in
stage 3; they are not extra assumptions of this statement.

Edge cases checked: r=0 allows E with lower-dimensional support and gives zero
coefficient at g; E=0 is included, with zero polynomial P. In dimension zero,
nonempty open in an integral scheme contains the sole generic point, and the
proper-support correction vanishes; using `coeff 0` gives the constant comparison.
For m=0 the tensor power is the tensor unit and evaluation is at zero. Empty Y
is excluded by the node's nonempty open (and integrality), not an extra assumption.
No algebraic closure or characteristic restriction appears. ULift preserves finite
rank while placing free modules in the same universe as Y.Modules.

Searches (2026-10-11):
- msearch.py leanfinder: "leading coefficient Euler characteristic coherent sheaf
  generic rank ample proper scheme": eight hits, all unrelated scheme section
  extension lemmas, no coefficient comparison.
- msearch.py loogle: "Polynomial.coeff, Polynomial.eval": twelve hits about
  polynomial evaluation/coefficients, no Euler-characteristic comparison.
- msearch.py grep: "fwdDiff_iter_eulerChar|generic.rank", Mathlib/AlgebraicGeometry:
  zero hits.
- rg of the same generic-rank patterns and of leading-coefficient/Euler patterns
  in WeilConjectures and lean/Sheaf: found the related upstream
  `Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow` in Modules/Ample.lean
  (lines 640–660), but no exact statement. Its signature requires
  `[E.IsFinitePresentation]`, uses upstream module pullback to express freeness,
  and concludes a forward-difference equality without existential polynomial
  representatives. It is not the recorded coherence/direct-coefficient statement
  and therefore cannot be recorded as an exact existing declaration here.
- grep -rn of the item id in WeilConjectures: no matches.
- rg of the new declaration name in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

The local literature/stacks-project/varieties.tex is absent on this machine.
Read the primary sources directly: https://stacks.math.columbia.edu/tag/0BEN
(the generic-length comparison and its coherent-filtration proof) and
https://stacks.math.columbia.edu/tag/0BEM (the polynomial existence/support bound).
They support the item's generic-rank specialization. No statement correction,
new node, dependency module, or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the single module on the server in 3.7 seconds,
exit code 0, with no warnings. The delivery dry run is the final validation;
the independent second reader supplies their own reading and delivers.


## Second reading by G1

Independent reading of the repository node, sandbox node and module, with the
recorded dependency declarations open. Verdict: the Lean says what the node
says; no signature or node correction is required.

Source check: read Stacks varieties.tex from the primary Stacks repository,
retained only in scratchpad/varieties.tex. Read the Numerical intersections
section introduction, lemma-numerical-polynomial-from-euler (0BEM),
lemma-numerical-polynomial-leading-term (0BEN), and
lemma-degree-finite-morphism-in-terms-degrees (0BEX). The section assumes proper
schemes over a field and coherent modules, not algebraic closure, smoothness,
or geometric integrality. 0BEN gives the lower-degree difference using generic
lengths; on integral Y its generic local ring is a field and the length is the
rank r. For rank zero use the support bound in 0BEM instead. Thus the item's
specialization, including r=0, is faithful to the source.

Object, hypothesis and conclusion checklist (each verdict: exact):
- K is a field: `(K : Type u) [Field K]`.
- Y is an integral proper K-scheme: `(Y : Scheme.{u}) [IsIntegral Y]`,
  `[Y.Over (Spec (.of K))]`, `[IsProper (Y ↘ Spec (.of K))]`.
  No separate finite-type or Noetherian assumption is added.
- Its dimension is g: `(g : ℕ) (hdim : topologicalKrullDim Y = g)`.
  Equality is with the natural number coerced into WithBot ℕ∞, not a
  default-to-zero conversion of an empty or infinite dimension.
- M is an ample O_Y-module: `(M : Y.Modules)` and
  `(hM : IsAmple (Y ↘ Spec (.of K)) M)`. Opened Ample.lean at IsAmple:
  invertibility and a positive very ample power are built into this recorded
  definition. Its proper-scheme meaning is the source's ample line bundle.
- E is coherent: `(E : Y.Modules)` and
  `(hE : RingedSpace.IsCoherent Y.toRingedSpace E)`. Opened Coherent.lean:
  finite type and finite-type kernels of maps from finite free modules on
  every open, exactly the dependency's definition; no merely finite-
  presentation or private coherence predicate is substituted.
- Nonempty open U: `(U : Y.Opens)` with `(hU : (U : Set Y).Nonempty)`.
- Rank r and the restriction isomorphism: `(r : ℕ)` and
  `e : E.over U ≅ SheafOfModules.free ... (ULift.{u} (Fin r))`, with
  `R := (moduleRings Y.toRingedSpace).over U`. Opened Mathlib's overFunctor,
  over and free: over is restriction to the open's over-site and free is
  the coproduct of r copies of its unit module. ULift changes no rank.
  An explicit isomorphism binder is equivalent to the stated existence
  assumption since the conclusion does not depend on which witness is used.
- The two numerical polynomials: `∃ P Q : Polynomial ℚ` and both `∀ m : ℕ`
  evaluation equalities. P represents χ(Y,E⊗M^m), Q represents χ(Y,M^m),
  using the recorded eulerChar, whose definition in Cohomology/Defs.lean is
  the alternating sum of cohomology finranks. Proper coherent finiteness
  and vanishing make those values the usual Euler characteristics.
  Natural exponents follow the recorded Hilbert-polynomial declaration;
  agreement is for all m, including 0, not just eventual agreement.
  Infinite agreement uniquely determines P and Q, so the existential form
  really compares the functions' coefficients. Integer values follow from
  the evaluation clauses. The node asserts the coefficient comparison,
  not an extra degree bound; none is silently added to the conclusion.
- Top coefficient: `P.coeff g = (r : ℚ) * Q.coeff g`.
  The node labels the factorial-scaled version equivalent: multiplication
  and cancellation of the nonzero rational g! gives precisely that version.
  No additional conjunct is needed.

Also opened the signatures and docstrings of degree in Ample.lean,
exists_polynomial_hilbertFunction, exists_coherent_filtration_integral_subschemes,
eulerChar_eq_add_of_shortExact, and exists_mvPolynomial_eulerChar_tensorPowers.
The filtration's Noetherian assumption follows from properness over a field;
the Euler-additivity tool's finite-dimensionality and vanishing prerequisites
are proof obligations, not additional hypotheses here. Snapper uses the same
coherence and eulerChar and bounds degree by stalk support. No new nodes or
dependency modules are included, so there are no H12/H13 additions to audit.

Edge cases: Fin 0 is empty and the free module is zero; r=0 admits a nonzero
E with proper support and forces the g-th coefficient to vanish. E=0 is
included. For g=0 a proper closed support in integral Y is empty and both
polynomials are constant; coeff 0 is the required constant term, and 0!=1.
For m=0 tensorPow is the tensor unit. Empty Y or U is excluded exactly by
integrality/nonempty U already stated in the node. No characteristic
restriction occurs: ℚ is the polynomial coefficient field, not the base field.
The universe u is arbitrary, and ULift puts the finite free index in that
universe; no test category or algebra is quantified in a smaller universe.

Independent searches (2026-10-11), using different wording from the worker:
- msearch leanfinder, "Hilbert polynomial top coefficient equals rank of
  sheaf times degree": eight hits about algebraic Polynomial.hilbertPoly,
  no sheaf Euler-characteristic comparison.
- msearch loogle, "Polynomial.coeff": twelve elementary coefficient hits,
  no match to the item.
- msearch grep, "hilbert.*rank|rank.*hilbert|coeff.*euler|euler.*coeff":
  three unrelated Hilbert-space/rank-one hits, no match.
- msearch leansearch, "Euler characteristic of coherent sheaf leading
  coefficient generic rank": service unavailable (Internal Server Error);
  no mathematical verdict inferred from that search failure.
- rg on Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf for
  coeff/Euler/Hilbert, genericRank, generic rank and forward differences:
  only the related Scheme.Hom.fwdDiff_iter_eulerChar_tensorObj_tensorPow
  in Ample.lean. Read its full signature: it assumes IsFinitePresentation,
  uses upstream pullback on U.ι, and concludes a forward-difference equality.
  It does not provide the exact recorded-coherence/direct-polynomial
  statement. No exact existing declaration replaces this delivery.

H5/H6/H8/H9: no definitions or hollow data; the only theorem proof is sorry;
module and theorem docstrings cite 0BEN and the correct blueprint id; the
proof docstring follows both node proof steps, including exact tensoring,
rank count, proper-support contributions, coefficient comparison and g=0.
No local notation, local instance, private definition, hidden let/show binder,
extra hypothesis or unbound universe appears. The node's lean.statement
matches the file signature verbatim.

Changes: left the correct Lean and node unchanged. Corrected the worker
report's inaccurate wording that the three proof-tool modules were imports:
they are not direct imports of this statement module. Appended this reading.
Validation: independent scompile.py single-file server compile passed in
3.0 seconds, exit code 0, with no errors or warnings.
