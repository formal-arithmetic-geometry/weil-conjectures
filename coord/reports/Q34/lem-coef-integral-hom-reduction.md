## Worker report

This stage-2 delivery states `WeilConjectures.integralHomReduction`. Its only
postponed proof is that theorem. All helper data are actual constructions or
records of the canonical constructions on complex representatives. No arbitrary
internal-Hom functor, scalar map, tensor comparison, or completion is substituted.

The item's earlier dispatcher note concerns Q23's **stage-1** split and review.
The current node is split and has no stage-2 Lean record; that supersession does
not remove this stage-2 task.

### Clause-by-clause reading

* `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]` are precisely the prime
  and finite coefficient-field extension. The valuation ring, its uniformizer
  ideal, and all quotients are those of the recorded completed coefficient
  sheaf, not new choices in this file.
* `Y : Scheme.{t}` is arbitrary. `D : FiniteFieldDatum.{d}` and `hl : l ≠ D.p`
  supply the existing coefficient API's characteristic context. The coefficient
  constructions ignore this auxiliary datum, as their unrestricted versions
  make explicit. No finiteness, separation, smoothness, or noetherian hypothesis
  on Y occurs.
* `completedIntegralCommRingSheaf l E Y D hl` is the recorded inverse-limit
  sheaf B. `Modules` is just an abbreviation for Mathlib's `SheafOfModules` on
  the actual small pro-etale site. Its object universe is t+1, its morphism
  universe t, and its coefficient/module universe max u (t+1).
* `IntegralHom.hom` is the recorded
  `CategoryTheory.derivedInternalHomOfUniverses.{t+1,t,u}` and uses the standard
  derived localization. `K L : completedIntegralDerivedCategory ...` range over
  the entire unbounded categories. No condition is imposed on K.
* `n : ℕ` denotes the positive exponent n+1, exactly as the recorded reduction
  and quotient interfaces do. `integralDerivedReduction ... n` is the canonical
  left derived scalar extension along B → B_n.
* `TensorPresentation` supplies ordinary uncompleted derived tensor, its
  K-flat representative comparison, and the tensor/internal-Hom adjunction.
  Its evaluation equation fixes the counit by actual local Hom-complex
  evaluation, with the Koszul sign for P tensor Hom(P,I). The theorem supplies
  this structure existentially; it does not assume a new tensor or adjunction.
  The representative equation ranges over every K-flat source and test complex
  and every K-injective target, so it fixes the evaluation of arbitrary derived
  morphisms via localization.
* `ReductionPresentation` supplies the canonical tensor comparison. Its
  normalization on every K-flat pair identifies the ordinary chain map by
  `(1 tensor x) tensor (1 tensor y) ↦ 1 tensor (x tensor y)` on every local
  homogeneous section. `reductionUnit` uses the recorded normalized ordinary
  extension adjunction, and `reductionCounit` uses the recorded universal derived
  counit, including the homotopy/derived localization factorization maps.
  This is not an arbitrary natural isomorphism.
* `comparison` is defined as the finite-coefficient adjoint transpose of
  `mu.inv ≫ F.map evaluation`. Its source is F H_B(K,L) and its target is
  H_Bn(FK,FL), and `IsIso (comparison ... K L)` is the assertion that the
  canonical comparison, not merely these two objects, is invertible.
* The next equality is the exact evaluation compatibility equation, obtained
  by evaluating after `id ⊗ comparison`. The final universally quantified
  equation, for every T and f:T→H_B(K,L), says that reducing f and then composing
  with this comparison equals the transpose of the reduced original pairing
  through the inverse canonical tensor comparison.
* `IsDerivedComplete ... L → IsDerivedComplete ... (hom.obj (op K,L))`
  uses the recorded Roos completeness predicate and requires no completeness,
  boundedness, constructibility, compactness, or perfection of K.

The existential presentation records are model data for the canonical operations,
normalized on representatives. They do not replace canonical maps by witnesses
of bare `Nonempty` isomorphisms. All displayed equations are part of the theorem's
conclusion, so no additional hypothesis is hidden in a record parameter.

### Recorded dependencies used

* `Sheaf.Paper.CompletedIntegralCoefficients`: completed and finite coefficient
  CommRing sheaves, `completedIntegralModuleSheaves`,
  `completedIntegralDerivedCategory`, and `completedIntegralRestrictScalars`.
  The current record also publicly reexports these through
  `Sheaf.Paper.CompletedIntegralCoefficientGerm`.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.ProEt` and its topology; the recorded
  `Scheme.proEtaleDerivedCategory` is its constant-scalar specialization.
* `Sheaf.Paper.IntegralDerivedReduction`: `integralReductionChangeOfRings`,
  `integralDerivedReduction`, and `integralDerivedReductionCounit`.
  These are the D,hl specializations of the same unrestricted scalar-extension
  witness now recorded in `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
* `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionExtensionAdditive` and
  `scalarReductionExtension_adjunction`, whose unit is fixed to 1 tensor x.
* `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, the recorded derived restriction
  interface (used in the proof plan through coefficient adjunction).
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses`, its inversion theorem, and its actual
  `Localization.fac` comparison. `homModelMap` composes the actual Hom map to
  the fixed K-injective replacement with this factorization comparison.
* `Sheaf.Paper.DerivedComplete`: `WeilConjectures.IsDerivedComplete`.
* `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients` and the existing independent
  coefficient tensor/zero-preservation instances. No K-flat predicate is copied.
* `Sheaf.Algebra.Homology.HomComplex` and `HomComplexProjections`:
  `CategoryTheory.homComplex`, `homComplexFunctor`, and
  `homComplex_projections_exists`, with their product/differential specification.
  Mathlib's `map₂HomologicalComplex` and `ιMapBifunctor` give the total complex.

All stated proof-dependency modules are imported privately. The docstring gives
the node's eight-step proof, including the two-term perfect coefficient model,
restriction/extension adjunction, Yoneda identification, K-flat/K-injective
representatives, signed chain isomorphism, identification of the specified map,
and the actual Roos triangle.

### Edge cases

The index zero means reduction by the first power, never B/(1). The zero objects
and the empty scheme give zero evaluations and comparisons. No boundedness of
P is used: each coefficient model has only two terms, so the finite coefficient
sum commutes with the Hom products. Uniformizer torsion in L retains the
negative-degree Tor term; the statement uses derived reduction and never the
underived quotient. The completeness implication assumes only completeness of L.
Independent t,u,d universes are retained. The older `ProEtaleTensorModel`
interface fixes the coefficient universe to t+1; the representative record here
retains max u (t+1) and additionally characterizes the evaluation adjunction.
It is not a second underlying tensor or Hom construction. Evaluation uses the identity slice
object and all local homogeneous sections, rather than only global sections.

### Searches

* msearch LeanFinder: `Derived internal Hom on a ringed site commutes with
  reduction modulo powers of a uniformizer and preserves derived completeness`:
  eight hits about ordinary completion/de Rham constructions, no exact match.
* msearch Loogle: `CategoryTheory.ihom, CategoryTheory.Functor`: twelve generic
  closed-monoidal hits, no exact statement on these sheaves or completion.
* msearch grep: `derivedComplete.*[Hh]om|[Hh]om.*[Rr]eduction|internalHom.*[Cc]omplet`:
  no exact match.
* msearch LeanSearch: `Derived internal Hom commutes with integral adic reduction
  on the pro-etale site`: service returned HTTP 500 (unavailable, no result).
* rg in upstream WeilConjectures and side-project lean/Sheaf, and exact node-id
  grep upstream: `SixFunctors/Etale/Derived/IntegralCoefficients.lean` contains
  `nonempty_iso_reductionModIdeal_derivedHom` and `derivedComplete_derivedHom`.
  These concern small etale constant scalars and identify the comparison only
  after restriction. They do not state this completed-small-pro-etale theorem
  with the specified coefficient morphism and its pairing compatibilities.
* Read the recorded dependency declarations in full, including server sources
  where local compiled interfaces lagged. A stale compiled KFlat interface was
  handled by using its existing equivalent independent-coefficient instances;
  no shared file was modified and no dependency copy is delivered.

No statement correction or disputed mathematical statement is proposed.


## Second reading by Q34

I independently opened the sandbox node and all 446 lines of the module before
making changes. The source blueprint is physically available in
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-integral-hom-reduction.md`;
the repository's corresponding literature path is absent on this machine.
I read that blueprint and, in the same literature tree, the Stacks sources
`sites-cohomology.tex` (labels `lemma-internal-hom`, `lemma-section-RHom-over-U`,
`lemma-pullback-tensor-product`, `lemma-adjoint`), `sites-modules.tex`
(`lemma-completion-flat`), and `derived.tex` (`definition-derived-limit`).
The Hom and adjunction results assume a ringed site/topos, not a noetherian
scheme, bounded complex, or perfect first argument. Noetherianity in the
completion lemma concerns the valuation ring, already a DVR.

Here is my object/hypothesis/conclusion inventory and its matching Lean.

1. A prime ell different from p, finite E/Q_ell, valuation ring and its
   uniformizer: `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`,
   `[FiniteDimensional ℚ_[l] E]`, `D : FiniteFieldDatum.{d}`, `hl : l ≠ D.p`.
   The datum is the completed-coefficient dependency's global convention;
   it imposes no property on Y. The valuation ring and quotient powers are
   precisely `Padic.coefficientExtensionRing l E (n+1)` in that dependency.
   Verdict: exact; no independently chosen ring or uniformizer.
2. An arbitrary scheme X and its small pro-etale site: `Y : Scheme.{t}` and
   `Scheme.ProEt.topology Y`. I read the Mathlib site declaration, the recorded
   `ProEtaleDerivedCategory` interface, the current upstream
   `ProEtale.ModuleDerivedCategory` source in the shared clone, and
   `coord/pefw-upstream-framework.md`. The constant-scalar derived categories
   of those interfaces are not incorrectly substituted for modules over B.
   Verdict: exact; no assumption on the scheme's characteristic or geometry.
3. B is the inverse limit of the constant finite quotient sheaves, B_n the
   constant quotient sheaf: `completedIntegralCommRingSheaf l E Y D hl` and
   `integralCoefficientCommRingSheaf l E Y n`. I read their actual definitions
   in `CompletedIntegralCoefficients`, including the underlying RingCat sheaf,
   inverse sequence, limit, and projection. Forgetting commutativity recovers
   the very module-ring data used by `completedIntegralModuleSheaves`.
   Verdict: exact; not the discrete constant sheaf of the valuation ring.
4. D(B), D(B_n), arbitrary K and L, and ambient internal Hom:
   `completedIntegralDerivedCategory`, `IntegralHom.Modules`,
   `IntegralHom.Derived`, and `IntegralHom.hom`, the latter an abbreviation of
   `derivedInternalHomOfUniverses.{t+1,t,u}`. I read that declaration's
   localization body, its quasi-isomorphism inversion theorem and comparison
   with K-injective representatives, and the Hom-complex projection theorem.
   All K and L binders range over the whole unbounded derived category.
   Verdict: exact; no constructibility, boundedness or perfection restriction.
5. Every n >= 1, F_n, U_n, K_n and L_n: `n : ℕ` means exponent n+1,
   `integralDerivedReduction ... n` is the canonical left derived scalar
   extension, and `.obj K`, `.obj L` give K_n and L_n. I read its universal
   counit construction and the unrestricted scalar-extension adjunction.
   The node's U_n is termwise exact restriction, supplied by
   `Functor.mapDerivedCategory`; it occurs in the underlying completeness
   and coefficient interfaces rather than as a gratuitous new parameter.
   The newer unrestricted reduction record and this specialized reduction
   use the same defining existence witness (the auxiliary D,hl are ignored).
   Verdict: same positive reductions and canonical coefficient map.
6. The canonical comparison in D(B_n): `IntegralHom.comparison` is literally
   `m.target.adjunction.homEquiv` applied to `m.mu.inv.app ...` followed by
   reduction of the source counit. Its type has exactly the displayed source
   F_n H_B(K,L) and target H_Bn(F_n K,F_n L). `IsIso` asserts invertibility of
   that morphism, not a bare object isomorphism. Verdict: exact.
7. Canonical pairing and all transposes: `TensorPresentation.representative`
   identifies the tensor with the existing signed total tensor on K-flat
   complexes; `evaluation` uses the actual Hom product projection on every
   local section and the sign (-1)^(i*j) for P tensor Hom(P,I).
   `ReductionPresentation.normalization` fixes the inverse tensor comparison
   on all pure tensors of ordinary extension units, with the actual derived
   counit and localization factors. Thus its scalar multiplication formula
   is the canonical one; this is not an unconstrained isomorphism witness.
   All presentations are existentially supplied in the conclusion, not
   assumptions on the input. The evaluation equality and the last `∀ T f`
   equality are precisely evaluation compatibility and compatibility of
   every transpose, with the same tensor ordering. Verdict: exact.
8. If L is complete, H_B(K,L) is complete: the first conjunct is
   `∀ K L, IsDerivedComplete ... L → IsDerivedComplete ... (hom.obj (op K,L))`.
   I read the actual Roos predicate in `DerivedComplete`: its first map is
   the canonical reduction augmentation, not an arbitrary comparison with
   a homotopy limit. The newer unrestricted predicate is an existential
   wrapper around this very predicate for an irrelevant finite-field datum.
   Verdict: exact; completeness of K is not assumed.

Quantifier order is valid: a single normalized tensor/evaluation presentation
works for all K,L, and for each n a single normalized coefficient comparison
works for all K,L,T,f. These are constructions associated to the coefficients,
not additional uniformity assumptions on the complexes. Definitions have real
data or choose from specifications that determine the relevant construction;
there is only one postponed theorem, `integralHomReduction`, with its complete
eight-step proof docstring. No new DAG definition nodes, dependency repair
modules, statement correction, or citer audit are needed in this delivery.

Edge cases: n=0 is exponent one and is included; the node does not request
exponent zero. Zero complexes and the empty scheme remain in the quantifiers.
No auxiliary family is required nonempty. Ell=2 and arbitrary residue
characteristics different from ell are allowed; Y is not required over D's
field. Independent scheme, coefficient-field, and global-datum universes
`t,u,d` remain independent, and coefficients/modules have universe
`max u (t+1)` on a site with object universe t+1 and morphism universe t.
Uniformizer-torsion L retains the Tor term because reduction is derived.
The two-term coefficient resolution is perfect even for unbounded K,L.

Independent searches, in addition to opening the dependencies:

- LeanFinder via msearch: `Derived internal Hom tensor with a perfect two-term
  quotient complex over a ringed site` returned Ext, sheaf cohomology, and Tor
  infrastructure, with no matching theorem.
- Loogle via msearch: `"derivedHom"` returned no hits.
- LeanSearch via msearch: `Internal Hom preserves adic completeness and
  commutes with reduction by a uniformizer` returned ordinary adic completion
  declarations; no derived ringed-site statement.
- msearch grep: `RHom.*quotient|internalHom.*reduc|derivedHom.*complet`
  returned three unrelated free-monoidal/invariant-ring hits.
- Direct rg of Mathlib homological algebra, upstream WeilConjectures, and
  the project's Sheaf modules found the existing etale theorems
  `nonempty_iso_reductionModIdeal_derivedHom_obj`,
  `nonempty_iso_reductionModIdeal_derivedHom`, and `derivedComplete_derivedHom`.
  I opened their signatures and proofs/docstrings: they concern constant
  etale scalars, and the comparison after restriction is only Nonempty.
  They do not give this completed pro-etale coefficient morphism or its
  evaluation/transpose clauses. `ProEtaleTensorModel` was also opened: it
  fixes coefficient universe t+1 and has no normalized evaluation adjunction.
  The present record extends representative specifications at independent
  universes and reuses Mathlib tensor and the recorded Hom, not a new
  underlying tensor or Hom construction.

Mismatch repaired: the first module omitted explicit private imports for
`lem-galois-yoneda-fully-faithful` and
`lem-weil-pbc-right-adjoint-preserves-limits`, both used in its proof plan.
Added `Mathlib.CategoryTheory.Yoneda` and
`Mathlib.CategoryTheory.Adjunction.Limits`. No mathematical signature changed;
the node's `lean.statement` was checked verbatim against the theorem signature.

Validation: `scompile.py Q34 lem-coef-integral-hom-reduction
lean/Sheaf/Paper/IntegralHomReduction.lean` passed via its prescribed server
confirmation: the delivered module compiled in 27.0 seconds, nice 19, two
threads, 60-second limit, without errors or warnings. The local attempt
timed out and was automatically checked against current server sources.
The final file has no overlong lines, `autoImplicit false`, one theorem
proof `sorry`, and a verbatim matching `lean.statement` record.
