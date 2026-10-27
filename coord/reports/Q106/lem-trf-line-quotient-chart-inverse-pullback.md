## Worker report

The delivery states `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.line_quotient_chart_inverse_pullback`
in `Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback`. The one theorem has proof `sorry`.
Its seven helpers contain actual data or fully expanded predicates for this node's own clauses;
there is no new independent notion, new DAG node, dependency repair, or statement correction.
The module docstring and every declaration identify this node and Stacks Constructions,
Tags 01OA (section-projective-bundle) and 01O4 (lemma-apply-relative).
I read constructions.tex lines 4656–4754 and 4116–4158: arbitrary quasi-coherent modules,
the normalized surjection, the two inverse constructions, and representation on test schemes.

The input describes F_h(L,q) by the fraction formulas of the recorded dependency. The Lean
universally quantifies over `ψ,F` with `ψ.ExtendsLineQuotient ... q` and
`ψ.HasQuotientFractionCharts ... F`. This does not assume the inverse theorem or change its
objects: `line_quotient_homogeneous_fraction_map` already asserts existence and uniqueness
of precisely these ψ and F for every invertible quotient. Thus it states the result for the
specified morphism without introducing another choice or an arbitrary map as its replacement.
The extra binders are the graph of the canonical construction, not new geometric assumptions.

Hypotheses and clauses, in the order of the node:

- S is `Scheme.{u}`, E is `S.Modules` with `[E.IsQuasicoherent]`. There is no finite-type,
  coherence, local-freeness, or nonzero assumption on E. P and p are the existing
  `(SymmetricAlgebraSheaf.gradedAlgebraData E).relProj` and `.relProjHom` throughout.
- D is an arbitrary `TautologicalQuotient E`, not the datum chosen by the parent existence
  theorem. Its existing `line`, `quotient`, `invertible`, `surjective`, `chart`, and `generator`
  fields express exactly the normalized datum required here.
- All test schemes T and morphisms h are universally quantified. The forward quotient has
  `L.IsInvertible` and `Epi q`. For modules, categorical epimorphisms are surjective sheaf
  homomorphisms; they do not require surjectivity on sections over every open.
- For every a over S, `ha : a ≫ p = h` is the over-base condition. The first block concludes
  `((tensorPullback a).obj D.line).IsInvertible` and `Epi (pulledQuotient D h a ha)`.
  The existing `pulledQuotient` uses the section-normalized composite-pullback comparison.
- The forward block produces `θ : (tensorPullback F).obj D.line ≅ L` and
  `pulledQuotient D h F hF ≫ θ.hom = q`. This is the first inverse identity, with the
  source transport from h^*E included, rather than an ill-typed bare F^*q_P equation.
- `tautologicalGenerator` is D.quotient in adjoint section form. D.generator identifies it
  with iota(m)/1 in O(1). `pulledTautologicalGenerator` really pulls this section back with
  `tensorPullbackSection` and restricts it. Thus the e in the formulas is the normalized
  tautological frame, not a fresh chosen frame.
- `InverseLineChartNormalization` quantifies over every affine U and W over U and every
  frame l (`IsFreeGenerator`). It concludes θ(e)=b_m*l on every smaller open V. In particular
  it applies to W_m=D(b_m), whose inclusion into W is canonical. Where b_m is a unit, it
  concludes that the pulled e is a frame and gives exactly `(b_v/b_m) • (b_m • l)` for
  each v. `Ring.inverse` is used only under an explicit `IsUnit` hypothesis, so this means
  inversion in the ring of functions, not a field structure or division by a nonunit.
- In the same predicate, whenever b_n is a unit on V the transition relation is
  `e = (b_m * Ring.inverse b_n) • f`. On the double generator open this is precisely
  e/f pulling back to b_m/b_n. All equalities concern restrictions of one global θ,
  which records agreement on every overlap and under frame or affine-base refinement.
  The fraction-map dependency already supplies the corresponding functions f/e and
  their scalar, frame, source-restriction and affine-base-restriction formulas.
- Conversely, for every ψ and F characterized by the pulled quotient's fraction formulas,
  the first block concludes `F = a`. `RecoveredQuotientFrame` takes l to be the actual
  pulled normalized e and concludes `quotientGeneratorCoefficient ... m = 1` whenever
  this is a frame. In particular it applies on a^{-1}(D_+(e)).
- `RecoveredFractionCoefficients` includes every natural degree d and homogeneous c.
  A factorization k of a into `Spec (A_e)_0` is the precise condition for a chart over
  D_+(e). It equates ψ's coefficient in the pulled e frame with k's ring map applied
  to `degreeOneQuotientFraction ... d c`. `Scheme.ΓSpecIso` and `W.topIso` are the canonical
  identifications between affine functions and sections. This writes a^*(c/e^d), not
  merely equality of the final scheme morphisms. The fraction chart has b_m=1, so its
  denominator contributes no extra factor.
- For `v : L ≅ L'` and `q ≫ v.hom = q'`, the next block concludes `F' = F` and equality
  of all coefficients in the frames l and `v.hom.app W l`, in every degree. The specified
  quotient isomorphism supplies invertibility and surjectivity of the new pair; these
  are not imposed again as stronger hypotheses.
- Every T' and every `u : T' ⟶ T` is allowed. `lineQuotientPullback h u E L q` is the
  actual composite `(tensorPullbackSectionComp u h).hom.app E ≫ (tensorPullback u).map q`.
  The result asserts its epimorphism property and invertibility of u^*L, so applicability
  of the fraction-map dependency after pullback is part of the conclusion.
- For every characterized F' after this pullback the result produces `hFF : F' = u ≫ F`.
  The equality for line isomorphisms includes `eqToIso` for this map equality, then
  `tensorPullbackSectionComp u F`, then `(tensorPullback u).map θ.hom`. Thus it is
  exactly θ_{q'}=u^*θ_q under the canonical identifications. It applies to every
  quotient-compatible θ', hence in particular to the θ' supplied by the same theorem
  for the pulled pair. Cancellation of the pulled epimorphism makes that θ' unique;
  there is no extra choice or additional existence hypothesis.
- The pulled θ' also satisfies `InverseLineChartNormalization`. Its frame equation is
  e mapping to the pulled quotient of m, namely u^*q(m).
- `QuotientFractionNaturality` gives b'(z)=u^*b(z) in every degree, and b'_m=u^*b_m,
  in the actual pulled frame on each affine W' over W. Its localization homomorphism β
  is prescribed on every scalar by u.appLE; this determines it uniquely. The displayed
  equality with `Localization.mk` is exactly
  β(b(z)/b_m^d)=u^*b(z)/(u^*b_m)^d. No flatness, finite generation, finite cover, or
  restriction on the characteristic is introduced.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `.Scheme.Hom`, and `Spec`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded
  `Scheme.Modules.IsQuasiCoherentFiniteType` was read; it is the conjunction of the
  imported `SheafOfModules.IsQuasicoherent` and finite type. This item only needs the
  quasi-coherent clause of pqf-def-coherent, so it uses `E.IsQuasicoherent`, without
  imposing finite type. The node itself separately defines these notions.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData`, its actual symmetric grading and restrictions.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj`, `relProjHom`, `relProjι`; I also read the full
  `GradedAlgebraData` signature in its defining module.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`
  and its ordinary pullback preservation theorem. The tensor-pullback preservation
  assertion remains a conclusion, avoiding an extra instance hypothesis.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionAdjunction`, and
  `tensorPullbackSectionComp`. This is the recorded canonical tensor pullback interface.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `TautologicalQuotient`, `pulledQuotient`, and the read `Classifies` relation. The former
  two occur directly. The proof of its parent classification theorem is not used.
- `Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap`:
  `line_quotient_homogeneous_fraction_map`, `RelativeGradedLineMap.ExtendsLineQuotient`,
  `HasQuotientFractionCharts`, `quotientGeneratorCoefficient`, `quotientCoefficient`,
  `quotientSymmetricGenerator`, and `degreeOneQuotientFraction`. The full source and
  docstrings of this dependency were read. Its charts supply the denominator opens,
  all-degree fraction and scalar formulas, overlap units, and independence of frame/base.

The stated proof dependencies are imported as proof imports where not already statement
imports: the module-map hom-cover gluing theorem, affine tensor section comparison,
Proj twist, normalized/general composite pullback, scheme morphism gluing, Proj standard
open charts, and epimorphism preservation by adjoints. I read their recorded declarations,
including the Mathlib-match declarations for epimorphism preservation and scheme gluing.
The theorem docstring preserves all eight accepted proof steps with those node citations.

Edge cases checked mathematically before writing, and again against the final signatures:
E=0 (P is empty; a line quotient forces T empty), the empty base or test scheme, a rank-one
E, arbitrary infinitely generated E, and generators with zero or nilpotent coefficients
(empty principal charts). No choice of a finite generating set occurs. Degree zero is
included in each coefficient and fraction quantifier. On the empty open the zero ring's
0=1 makes the coefficient-one formula valid. The unit hypotheses in overlap formulas
cover actual double-generator charts. Non-flat u (for example reduction modulo 2) is allowed
and the formulas still send coefficients by the actual ring map. Identity u and composite
u use the same section-normalized tensor comparisons. Affine intersections are handled by
arbitrary smaller opens and affine refinements, never assumed affine.

Searches actually run for an existing statement:

- msearch leanfinder: "Pullback of the tautological quotient of Proj symmetric algebra
  recovers a line quotient with inverse identities natural under arbitrary pullback".
  Eight results: absolute `Proj.pullbackAwayιIso` and its component identities; no relative
  line-quotient inverse or naturality statement.
- msearch leansearch: "projective bundle invertible quotient inverse pullback tautological
  quotient naturality". Eight results, including `Module.Invertible.instProjective`,
  projective-resolution naturality, vector-bundle pullback, and tensor inverse lemmas;
  no match for this sheaf-theoretic assertion.
- msearch loogle: `AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict`.
  One result in Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic; read the actual
  declaration around lines 495–505. It is restriction of the absolute construction,
  not either relative line-quotient inverse identity.
- msearch grep: `tautological|line_quotient|quotient.*pullback`, in AlgebraicGeometry.
  One unrelated IdealSheaf.Subscheme result at line 706; no match.
- Direct rg of the project Sheaf source for `line_quotient|quotient_chart|theta|inverse_pullback`
  found the fraction-map dependency and finite-free projective-bundle base-change material.
  The parent `projective_bundle_quotient_geometry` asserts existence and classification
  for some D; it does not state this node's every-normalized-D result with all inverse
  charts and arbitrary-pullback isomorphism normalization, so it is not an existing match.
- Direct rg of WeilConjectures for the item id, `line_quotient`, and `TautologicalQuotient`
  found no match. Direct rg across Sheaf, WeilConjectures, Mathlib and
  dag/lean_names_upstream.json for each proposed new full-name component found no collision.

Validation: the statement module compiled via scompile.py in both sandbox and library
module mode with no errors or non-sorry warnings. The node copy changes only `lean`;
the existing accepted statement, dependency lists, proof and every other field are retained.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
