## Worker report

The module `Sheaf.Paper.PointSectionsDerivedReduction` states
`WeilConjectures.point_sections_derived_reduction`. It has one postponed theorem,
with the node's ten-step natural-language proof in its docstring. All helper definitions
have real data. The statement of the DAG node is unchanged.

The earlier sandbox attempt was incomplete: it compared integral sections directly to
restricted reduced sections, without reducing the left side, and omitted the
constructibility domain, the quotient-module category, the cone description, and the
cohomology clause. It also redeclared imported instance names. This delivery replaces
that attempt and supplies all clauses.

Hypotheses and clauses, in source order:

- The fixed tuple p,a,q,k_0,k is `D : FiniteFieldDatum.{u}`. Its primality,
  positive exponent, cardinality, base field and fixed algebraic closure are exactly
  the recorded structure fields. `pointReductionDatumAlgClosed D` extracts algebraic
  closedness from `D.isAlgClosure`; it is not a new hypothesis.
- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`, and the theorem explicitly
  takes `_hl : l ≠ D.p`.
- The finite extension is `E : Type u` with `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. Its valuation ring, chosen uniformizer, ideal powers
  and quotients are `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, `Padic.coefficientExtensionIdeal` and
  `Padic.coefficientExtensionRing`, imported unchanged from the dependency modules.
- The node's positive exponent is written `n + 1` with `n : ℕ`. This is the exact
  existing indexing of `scalarReductionDerivedExtension` and the coefficient sheaf
  system. Every positive exponent occurs, including exponent one at `n = 0`.
- The point s is `Spec (.of D.k)`; both recorded section functors evaluate at
  `op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))`, the actual final site object.
- The domain is precisely `sfIntegralConstructibleCategory l E (Spec (.of D.k))`.
  The functor inclusion `(sfIntegralConstructible ...).ι` in both sides retains
  derived completeness, constructibility of every positive reduction, and the one
  common cohomological interval. There is no K-flat or flat-term input assumption.
- Integral derived sections are `(pointIntegralSections l E D.k).mapDerivedCategory`.
  `pointIntegralSections` is the recorded evaluation followed by scalar restriction
  through `pointIntegralSectionMap`, constructed from `integralConstantToCompletion`
  and the constant-sheaf unit. Thus the completed coefficient sheaf is retained;
  it is not replaced by the discrete constant O_E sheaf.
- The left side `pointReductionTensorSections D l E n` applies the ordinary-module
  derived tensor `pointReductionModuleTensor l E n` to these sections. Its coefficient
  map `pointReductionQuotient` is `RingHom.ulift (Ideal.Quotient.mk ...)`. Its second
  tensor factor is the quotient ring as a module over itself, in degree zero.
  Its first-variable derived tensor is chosen from the existing universal
  `exists_derivedTensor_second_factor_functor`, whose counit and K-flat computation
  determine it up to canonical compatible isomorphism. This is derived tensor,
  without an exactness assumption on ordinary quotient tensor.
- The right side `pointReductionSectionsTensor D l E n` applies the recorded
  `scalarReductionDerivedExtension` along the completion projection, then
  `(pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n+1))).mapDerivedCategory`.
  Thus it has the actual quotient-module action through the constant-section map.
- The first conjunct `Nonempty (pointReductionTensorSections ... ≅
  pointReductionSectionsTensor ...)` is an isomorphism of functors on the full
  integral constructible category. Its components have exactly the displayed source,
  target, and direction, and naturality is part of the natural-isomorphism type.
  Both functors land in `DerivedCategory (ModuleCat.{u+1}
  (ULift.{u+1,u} (Padic.coefficientExtensionRing l E (n+1))))`.
- The second conjunct quantifies over `N` in the same subcategory and every ordinary
  coefficient complex `C` representing its integral sections. Given
  `Nonempty (DerivedCategory.Q.obj C ≅ Gamma(N))`, it asserts that restriction of the
  left side along `pointReductionQuotient` is isomorphic to
  `DerivedCategory.Q.obj (CochainComplex.mappingCone
  ((ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n+1)) • 𝟙 C))`.
  This is precisely the cone of multiplication by the uniformizer power on a
  representative of Gamma(N). It does not give the unreduced cone terms an A-action.
- The last conjunct quantifies over all `r : ℤ` and gives a natural isomorphism from
  `pointReductionTensorSections ... ⋙ DerivedCategory.homologyFunctor _ r` to
  inclusion, derived sheaf reduction, sheaf cohomology in degree r, and finite point
  sections. It renders exactly the consequent cohomology assertion, with its A-action.

The `ULift` rings are the same size transports used by the recorded finite and integral
section functors. They are ring-isomorphic to the original coefficient rings, and the
quotient map is the transported original quotient map. The site still has object universe
u+1 and morphism universe u. No equality between these universes is imposed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.PointProEtaleSectionsExact`:
  `AlgebraicGeometry.ProEtale.pointModuleSections` and
  `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact`.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and `sfIntegralConstructibleCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm`: `integralConstantToCompletion`,
  with the imported completion, quotient sheaves, and projections from
  `Sheaf.Paper.CompletedIntegralCoefficients`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`, and `scalarReductionDerivedExtension`.
- `Sheaf.Paper.PointSectionsFiniteness`: `pointConstantSectionMap`,
  `pointIntegralSectionMap`, `pointIntegralSections`, and `pointFiniteSections`.
  Its node is added to `stmt_deps` because these published evaluation interfaces are used.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor` (already a proof dependency).
- Mathlib's `ModuleCat.restrictScalars` and general-universe exactness instances from
  `ChangeOfRingsExact`, `HomologicalComplex.single`, `DerivedCategory.homologyFunctor`,
  and `CochainComplex.mappingCone` supply the ordinary module constructions.

All other recorded proof modules are imported without `public`, following the stage rule.
No dependency is replaced, and no new independent definition node is required: the small
helper definitions construct precisely the functor composites and quotient tensor already
occurring in this node. The sole postponed theorem corresponds to this DAG node.

Edge cases checked: the zero integral object and zero complexes, all integer cohomology
degrees including negative ones, the first quotient (n=0 in this encoding), arbitrary
larger positive powers, and unbounded complex representatives. No termwise boundedness
or flatness was added. The finite-field datum makes the point nonempty and algebraically
closed; the empty scheme is not an object of this statement. The excluded equal-prime
case remains explicitly excluded by `_hl`. No finite-Tor-amplitude assumption is added.

Searches made for an existing full statement:

- `msearch.py`, leanfinder: "Exact sections of an algebraically closed proetale point
  commute with derived reduction modulo a uniformizer power". Eight hits, concerning
  standard etale algebras and perfectoid quotient coefficients; none state this theorem.
- `msearch.py`, loogle: `"mapDerivedCategory"`. Twelve hits, including the exact-functor
  descent, shift and composition comparisons, without the completed-coefficient reduction.
  The full exact-functor source was read and is used rather than reimplemented.
- `msearch.py`, grep: `sections.*reduction|reduction.*sections|derivedTensor`, restricted
  to Mathlib/Algebra/Homology. Zero hits.
- `rg` in the upstream WeilConjectures sources for the item id: no match. Searches for
  derived reduction, point sections, scalar extension and coefficient quotients found
  adjacent etale constructions, not this pro-etale completed-coefficient statement.
- `rg` in `lean/Sheaf` for `derived_reduction`, sections/reduction pairs, and
  `pointCompletedDerivedSections` found the recorded reduction and sections definitions,
  plus scalar-extension comparisons, but no full reduction/sections comparison.
- `scompile.py --source Sheaf.Paper.PointSectionsDerivedReduction` reported that the
  module was unavailable, confirming that the earlier sandbox attempt was not published.

The blueprint source at `sec-poincare-duality/sk-lem-finite/prop-cohomological-finiteness.md`
was opened, particularly Steps 2 and 4. The DAG supplies the explicit ten-step proof
of the passage used there; that proof is carried into the theorem docstring.

No STATEMENT-DISPUTED condition or statement correction was needed. The theorem is a
statement with `sorry`, not a claimed completed proof. The independent second reader
will perform and record the separate second reading after this worker's dry run.

## Second reading by Q04

I did not write the statement. I opened the original DAG node, its sandbox copy,
the delivered Lean module, and the recorded dependency declarations. I read the
blueprint source `sec-poincare-duality/sk-lem-finite/prop-cohomological-finiteness.md`,
including its initial coefficient conventions and Proof Steps 2 and 4. The auxiliary
Stacks sources were also read in `sites-modules.tex`, Constant sheaves, Tag 093M,
and `sites-cohomology.tex`, Tags 06YS, 06YY and 0946. These require respectively a
Noetherian coefficient ring, a ringed site, a morphism of ringed topoi, and a weakly
contractible evaluation object. Here Noetherianity follows from the recorded DVR
result; the completed-to-finite projection is the same-site ring morphism; the
point is algebraically closed. None of these becomes an extra input hypothesis.
The blueprint's separated finite-type scheme and Weil complex concern the parent
finiteness proposition; this reduction lemma concerns its coefficient point and
does not require a new scheme or Weil structure.

Here is my independent list of the node's objects, assumptions and conclusions,
matched against the actual Lean. Each row passes.

| Node item | Lean rendering and verdict |
| --- | --- |
| Fixed prime p, positive a, q=p^a, finite field k_0 and fixed algebraic closure k | `D : FiniteFieldDatum.{u}`. I read its fields `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, `field_closure`, `algebra_closure` and `isAlgClosure`. These are the stated datum, not an arbitrary field substitute. |
| Prime l distinct from p | `(l : ℕ) [Fact l.Prime]` and theorem binder `(_hl : l ≠ D.p)`. The inequality is present even though the mathematical comparison also holds more generally. |
| Finite extension E of Q_l | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. No coefficient-field restriction such as E=Q_l is imposed. |
| Valuation ring, chosen uniformizer, positive power and quotient | Existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`, and `coefficientExtensionRing`. I read `CoefficientExtension.lean`: the ideal is `(span {uniformizer})^(n+1)` and the ring is its quotient. The index `(n : ℕ)` means the source exponent n+1, hence exactly all positive exponents. |
| s=Spec k, and sections at the final small pro-etale object | `Spec (.of D.k)` and the imported `pointModuleSections`, evaluating at `op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))`. Its definition is sheaf-module forgetful functor followed by presheaf-module evaluation. |
| Completed integral coefficient sheaf, with the canonical O_E action on sections | `pointIntegralSections l E D.k`, read in `PointSectionsFiniteness.lean`, restricts evaluation along `pointIntegralSectionMap`. I traced that map through `integralConstantToCompletion` in `CompletedIntegralCoefficientGerm.lean`: it is the limit lift of the constant quotient maps. `CompletedIntegralCoefficients.lean` constructs the actual inverse limit; no identification with a discrete constant integral sheaf is assumed. |
| N in precisely D^b_c(s,O_E) | Domain of both comparison functors is `sfIntegralConstructibleCategory l E (Spec (.of D.k))`. I read `sfIntegralConstructible`: derived completeness, constructibility of every positive reduction, and a single finite integer interval containing all reduction supports. The inclusion `.ι` imposes exactly these conditions and no termwise boundedness or flatness. |
| Sheaf derived reduction along the completed coefficient projection | `scalarReductionDerivedExtension l E (Spec (.of D.k)) n`. I read its source and target abbreviations, actual coefficient projection, existence construction, and universal counit. It is the recorded K-flat-computed derived scalar extension, with the original quotient ring sheaf. |
| Ordinary-module derived reduction of integral sections | `pointReductionTensorSections D l E n`: inclusion, exact integral derived sections, then `pointReductionModuleTensor l E n`. The latter uses the recorded `exists_derivedTensor_second_factor_functor` with coefficient map `pointReductionQuotient` and second factor the quotient module concentrated in degree zero. I read that theorem's universal left-derived and K-flat computation clauses; the choice is of a functor characterized up to compatible isomorphism, not arbitrary data from mere existence. |
| Isomorphism in D(A), natural in N | First conjunct is `Nonempty (pointReductionTensorSections D l E n ≅ pointReductionSectionsTensor D l E n)`. Both land in `DerivedCategory (ModuleCat.{u+1} (ULift.{u+1,u} (Padic.coefficientExtensionRing l E (n+1))))`. A functor isomorphism supplies precisely all components and naturality for the full domain. The right side first reduces the sheaf object and then applies the exact finite sections functor, with action through the actual constant-section map. |
| Restriction of the left side represented by Cone(uniformizer power on Gamma(N)) | Second conjunct quantifies over every `N` and every integral coefficient complex `C` with `Nonempty (DerivedCategory.Q.obj C ≅ Gamma(N))`. It asserts the required isomorphism after `(ModuleCat.restrictScalars (pointReductionQuotient l E n)).mapDerivedCategory`, to `DerivedCategory.Q.obj (CochainComplex.mappingCone ((ULift.up uniformizer ^ (n+1)) • 𝟙 C))`. The cone lives over O_E, as required; it does not claim an A-action on its unreduced terms. I checked Mathlib's mapping cone definition as well. |
| Every integer r: reduced section cohomology equals sections of reduced cohomology | Last conjunct `∀ r : ℤ, Nonempty (...)` is an isomorphism of functors: left comparison functor followed by `DerivedCategory.homologyFunctor _ r`, versus inclusion, sheaf reduction, sheaf homology, then `pointFiniteSections`. This also retains the quotient-module action. Its naturality follows the node's final proof step and introduces no mathematical strengthening. |

The exactness instances in the new file are projections of
`point_proEtale_sections_exact` or instance synthesis for its composite with
`ModuleCat.restrictScalars`. I checked the latter's arbitrary-universe exactness
instances in Mathlib `ChangeOfRingsExact.lean`. They introduce no new theorem or
hypothesis. `pointReductionDatumAlgClosed` extracts algebraic closedness from
`IsAlgClosure`; `pointReductionModuleDerived` is the standard localization. I read
Mathlib `DerivedCategory.Basic` and `ExactFunctor`: `mapDerivedCategory` is the
termwise descent at quasi-isomorphisms, so this is the node's derived sections.

Edge cases: the zero object and any zero representative are included; every integer
cohomology degree is covered, including negative degrees. Lean n=0 is exponent one,
not an omitted first quotient; exponent zero is outside the node's n>=1 range.
Complex representatives in the cone clause can be unbounded and have arbitrary
terms. There is no index family to exclude the empty family. The empty scheme is
outside the fixed `Spec k` datum; no nonempty hypothesis was added on a variable
scheme. The characteristic condition is exactly l!=p. The site has object universe
u+1 and morphism universe u; modules and lifted coefficient rings occupy u+1.
The ULift quotient homomorphism transports the original quotient homomorphism,
and no site-universe equality or smaller module universe has been imposed.

Independent searches (using words other than the first worker's initial query):

- LeanSearch through `msearch.py`: "Global sections commute with derived tensor
  reduction modulo a power of a uniformizer on an algebraically closed pro-etale
  point". Eight results about structure sheaves and ordinary affine sections;
  none supplies this statement.
- LeanFinder through `msearch.py`: "Derived base change for global sections on a
  weakly contractible point and quotient scalar extension". Eight affine
  structure-sheaf/localization results, none a match.
- Loogle: the initial two-string query was syntactically invalid, so I reran the
  valid `"mapDerivedCategory"` query. It returned the exact-functor descent,
  composition, shift, and localization comparison interfaces, not this comparison.
  Their source was opened and the existing descent is used.
- Grep through `msearch.py` for `sections.*reduction|reduction.*sections`: no hits.
  Independent `rg` on Mathlib, slopmaster2 `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for derived-reduction/sections phrases, the node
  id, `pointReduction`, and `point_sections_derived_reduction`: no existing full
  statement or helper-name collision. Broader searches found the recorded section
  functors, tensor constructions and ordinary ringed-space point comparisons;
  these have different domains and do not state this completed-coefficient
  small-pro-etale assertion. I also checked the supplied pro-etale framework
  manifest and its module-object derived sources; no matching statement appeared.

There are no new definition nodes or dependency modules in this delivery, hence no
additional stage-1 new-node review is required. The extra statement dependency
`lem-weil-point-sections-finiteness` is already landed and records the canonical
section-map helpers used here; brief-stage2 section 5 permits adding this recorded
node. Its dependency lists do not cite this item. No finiteness assertion from its
theorem is used as a hypothesis of this statement. All original dependencies are
retained and their recorded notions are used.

No mismatch was found and I left the correct Lean and natural-language statement
unchanged. No statement correction or citer audit is needed. The module and every
declaration have source/blueprint docstrings; the theorem docstring carries all ten
proof steps, including the unbounded quotient-cone calculation, resolution
independence/naturality, scalar-forgotten cone, and cohomology consequence. There is
one theorem with one whole-proof `sorry`; definitions have real data and instances
only use existing proofs. No new result is proved. The node differs from the base
only in `lean` and the added recorded dependency. Its `lean.statement` is verbatim
the theorem signature, and all Lean lines have at most 100 characters. All binders
and the sole universe variable are explicit.

Validation: `scompile.py Q04 lem-pod-point-sections-derived-reduction` on the sole
delivered module passed both sandbox and library-path checks (14.0 s and 12.2 s),
with no errors or warnings. The only second-reader change is this appended review.
