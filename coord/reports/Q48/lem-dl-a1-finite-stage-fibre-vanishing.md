## Worker report

The module `Sheaf.DeligneLaumon.FiniteStageFibreVanishing` states
`WeilConjectures.DeligneLaumon.finite_stage_fibre_vanishing`, with `sorry` as its
whole proof. The four other declarations have real bodies: two composites defining
point evaluation, one predicate packaging the node's lisse hypothesis, and the
composite giving ordinary pullback followed by sections. They introduce no new
coefficient category, pullback, realization, point functor, or local-freeness notion.
The natural-language statement and proof are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. The chosen prime distinct
  from `D.p`, and its algebraic closure, are `c : D.CoefficientDatum`.
- A finite subextension of that closure is
  `E : Padic.FiniteCoefficientFields c.l c.Qbar`; the field used is `E.val`.
  This retains its embedding, rather than quantifying an unrelated coefficient field.
  Its valuation ring and uniformizer are the recorded `Padic.coefficientExtensionIntegers`
  and `Padic.coefficientExtensionUniformizer`, used by the imported categories.
- The separated finite-type k-scheme is
  `T : LisseRealization.Base D c.l c.different` and
  `[IsSeparated (T.scheme ↘ Spec (.of D.k))]`. `Base` packages a structure map,
  `LocallyOfFiniteType`, and `QuasiCompact`. Its residue-prime invertibility is
  derived by the existing `LisseRealization.baseInvertible`, not added as a hypothesis.
- Objects F belong to the recorded `sfRationalHeart c.l E.val T.scheme`.
  Its objects are rational constructible objects in both standard degree-zero halves.
- The immersion is `b : C.scheme ⟶ T.scheme`, `[IsImmersion b]`, and
  `[b.IsOver (Spec (.of D.k))]`. Reduction is `[IsReduced C.scheme]`.
  `[ConnectedSpace C.scheme]` includes nonemptiness. `C` has the induced finite-type
  base presentation, a consequence of being a locally closed subscheme of finite-type T.
- Completed derived pullback is exactly `LisseRealization.pull`, an abbreviation of
  the dependency's `rationalDerivedPullback`, never ordinary pullback in disguise.
- The continuous realization on C is supplied as
  `a : LisseRealization.At D c.l c.different E.val C`. This is the existing
  normalized presentation of J on the intrinsic raw category: `a.integral` identifies
  it with actual derived scalar extension; `a.completion_residues` fixes completion
  by every quotient projection; `a.localization_unit` fixes localization; and
  `a.fractions` fixes the scalar formula on rational morphisms. This is the ordinary
  module-sheaf presentation of the continuous realization, rather than another choice
  of coefficients or an arbitrary functor. The condensed realization's `At.scalarExtension`
  uses this same construction after its `moduleEncoding` and integral presentation
  equivalences. Quantifying normalized realization data avoids defining an object by
  choosing from a bare existence theorem. Existence of this data is already supplied
  by `LisseRealization.lisse_rational_realization`.
- The hypothesis that `J_C(Lb*F)` is a lisse sheaf of constant rank r is exactly
  `finiteStageLisseRestriction`: an iso to its H⁰ placed in degree zero, and
  `SheafOfModules.IsFiniteLocallyFreeOfRank r` for that H⁰. The latter uses local
  generators on a cover of the small pro-etale site. It asks for no global basis.
- The rational k-point is `x : Spec k ⟶ C.scheme` with `[x.IsOver (Spec k)]`;
  `LisseRealization.point` has underlying scheme `Spec (.of D.k)`.
- `finiteStagePointComplex T (x ≫ b)` is precisely the recorded `pointRationalFibre`
  applied after completed pullback to the heart inclusion. Its finite-dimensional
  derived target is only forgotten to the ambient derived category.
- `finiteStagePointFibre` is its H⁰, lifted in carrier size to `ModuleCat.{u+1} E.val`
  by the already recorded `LisseRealization.fibre`. The theorem explicitly states
  the point complex is isomorphic to its degree-zero complex, so it does not mistake
  H⁰ for the whole fibre without a concentration assertion.
- `finiteStageOrdinaryPointSections` is `Gamma(s,x* H⁰ J_C Lb*F)`:
  `a.sheaf`, ordinary coefficient module pullback `ordinaryPull`, then `sections`.
  The last uses evaluation on the final pro-etale object with E-action restricted
  along the constant-continuous-function map `pointConstants`.
- The identification is a natural isomorphism between these two functors on the FULL
  subcategory of the heart satisfying the lisse-restriction hypothesis. Thus naturality
  in F is stated, not replaced by unrelated objectwise linear isomorphisms.
- Its dimension is `Module.finrank E.val (...) = r`. The fibre is already in the
  finite-dimensional point category, and the carrier lift preserves dimension.
  The comparison identifies the sections dimension with the same r.
- The local implication uses `Subsingleton` of the actual fibre vector space and
  concludes `IsZero ((LisseRealization.pull ... b).obj F.obj.obj)`, i.e. Lb*F = 0.
  It is quantified at each x, so vanishing at any single supplied point suffices.
- The final conjunct quantifies every F in the full constructible rational heart.
  Vanishing is `IsZero` of the recorded point complex at every k-rational y, and the
  conclusion is `IsZero F.obj`. No lisse assumption occurs in this global conjunct.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum` (including
  its coefficient-prime and algebraic-closure instances).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, re-exporting the actual ring and uniformizer.
- The scheme-morphism convention has no module/declaration of its own: use Mathlib's
  `IsImmersion`, `IsReduced`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`, `sfRationalHeartProperty`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback` (via `pull`).
- `Sheaf.Paper.CondensedERealization`: its `At.scalarExtension`, `moduleEncoding`,
  and `condensedE_realization` specify the continuous construction used here in the
  intrinsic ordinary-module presentation. Imported publicly as a statement dependency.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre` with its original
  `DerivedCategory.pointFiniteDimensional` target.
- Added already-landed statement dependency `def-real-lisse-realization-data`, module
  `Sheaf.Paper.LisseRationalRealizationData`: `Base`, `At`, `At.sheaf`, `pull`,
  `ordinaryPull`, `point`, `sections`, `fibre`. Each is reused, with no private copy.
- Added already-landed statement dependency `def-weil-finite-subextension-directed-set`,
  module `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `FiniteCoefficientFields`.
- `Sheaf.Paper.GeometricFieldProEtaleEvaluation`,
  `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`,
  `Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance`,
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`,
  `Mathlib.AlgebraicGeometry.Noetherian`, and
  `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` are plain proof imports.
  The proof nodes `lem-tw-lisse-point-sections-realization` and
  `lem-dl-a1-heart-connected-lisse-strata` have no Lean record in the read base, so
  have no module to import; their proof roles are retained in the theorem docstring.

Edge cases checked before writing:

- T empty: no nonemptiness hypothesis on T; the universal point condition is vacuous,
  and the conclusion correctly says every constructible heart object there is zero.
- r = 0: r is an unrestricted natural; rank-zero local generators and the zero vector
  space are included. No positive-rank hypothesis or basis choice appears.
- The zero object on any T satisfies the claims. Disconnected ambient T is permitted;
  connectedness is imposed only on the local stratum C, exactly as in the node.
- A nonreduced ambient T is permitted (`IsReduced` only on C); the proof plan reduces
  T via topological invariance before reduced open-closed induction.
- A nontrivial locally free sheaf on C is permitted; local generators do not require
  a global basis. A constant rank-r sheaf on Spec k gives exactly E^r on sections.
- The global quantifier includes all k-rational points and is restricted to the
  constructible rational heart, never arbitrary pro-etale sheaves.
- The small pro-etale site retains objects in u+1 and morphisms in u; ordinary module
  carriers are in u+1, and the prescribed point target is in u with an explicit carrier
  lift when compared to ordinary sections. No universe equality has been imposed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Constructible rational adic sheaves vanish if fibres at all
  algebraically closed rational points vanish; lisse rank computed by point sections"`:
  eight hits about rankAtStalk for commutative-ring modules; no adic point-section result.
- `msearch.py ... loogle "Module.finrank, SheafOfModules"`: zero hits.
- `msearch.py ... leansearch "Constructible rational adic heart objects are zero if their
  fibres at all rational points of an algebraic closure vanish"`: eight hits about
  algebraic adic completion and p-adic valuations; no match.
- `msearch.py ... grep "finite.stage.*fibre|lisse.*rank|point.*vanish" AlgebraicGeometry`:
  one irrelevant scheme-section hit in Mathlib/AlgebraicGeometry/Scheme.lean:738.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for lisse/rank and point/conservativity
  found the generic etale point results, classical Weil-sheaf rank results,
  `AdicHeartPullbackFibres`, `RawHeartAdicLisseStratification`, and the normalized lisse
  realization interface; none is this theorem. In particular the classical results
  concern different coefficient presentations or hypotheses, and the normalized
  realization states comparisons without this constructible point-detection conclusion.
- `rg` for `lem-dl-a1-finite-stage-fibre-vanishing` in `lean/WeilConjectures` found none.
  `rg` for all five proposed names across Mathlib, WeilConjectures, and Sheaf found none.

Sources read: the current `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/`
`sk-p-dl-a1-exact/p-dl-a1-exact.proof.md` Steps 1 and 5, and Bhatt--Scholze PDF
Definition 6.8.3, Proposition 6.8.14(2), and Remark 6.8.15 using pdftotext.
No statement dispute or correction was needed. No new nodes or dependency repairs.

Validation: every compile uses scompile.py against the published live library, in
module mode. The initial compile found only one long-line warning, repaired by wrapping
its rank hypothesis. Final clean compile and deliver2.py preflight are recorded by the
delivery wrapper. No local build, global build, or direct Git operation was run.

## Second reading by Q48

This dispatcher assignment forbids starting other agents and assigns independent review
of the delivery to the maintainer. This section records the worker's explicit rereading,
not a claim that another worker reviewed it.

I reopened the node and the finished signature and checked both conjuncts: local connected
reduced strata have the degree-zero lisse assumption, a natural vector-space comparison,
constant rank, and single-point vanishing; global detection has all constructible heart
objects and all k-rational points, including the empty scheme. The two site universe
levels and the small point derived target remain intact. The sole formatting mismatch
found by compilation was the 103-character local-freeness line; it was wrapped. The
natural-language statement, source, proof, and proof dependencies were not modified.
