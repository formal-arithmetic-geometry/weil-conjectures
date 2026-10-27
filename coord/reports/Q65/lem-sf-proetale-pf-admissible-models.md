## Worker report

The module `Sheaf.Paper.ProEtalePfAdmissibleModels` states
`AlgebraicGeometry.ProEtale.proEtale_pf_admissible_models`, with one postponed theorem.
All other declarations are aliases, inherited instances, or explicit proposition definitions
owned by this node. There is no new DAG notion and no dependency repair or statement correction.

The ambient objects use ordinary `Sheaf (ModuleCat A)` categories on the original small
etale and pro-etale sites. The small pro-etale site retains distinct object and Hom sizes;
coefficients and sheaf values live in the common universe `u+1`.

Hypotheses and conclusions are matched as follows.

- The global datum is `D : WeilConjectures.FiniteFieldDatum`; `l`, `[Fact l.Prime]`, `_hl`,
  `E`, `[Field E]`, `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`
  give precisely the stated coefficient data. `n : ℕ+` means an integer level at least one.
  `pfModelCoefficients l E n` is the actual quotient
  `ULift (Padic.coefficientExtensionRing l E n)`. The lift changes only its universe.
  Its finiteness instance applies the recorded positive-level finiteness theorem.
- `X.Over (Spec ... D.k)` and `Y.Over ...`, with `LocallyOfFiniteType` and `QuasiCompact`
  on their structure maps, say that X and Y are finite-type k-schemes. `f.IsOver ...`
  makes f a k-morphism; `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`
  give separatedness and finite type.
- `j`, `[IsOpenImmersion j]`, `r`, `[IsProper r]`, and `_hjr : j ≫ r = f` are exactly
  the fixed compactification. No properness or flatness of f is substituted for these.
- `K` and `L` are objects of the ordinary bounded-below derived categories, with explicit
  membership `_hKb`, `_hLb` in `DerivedCategory.TStructure.t.bounded`. This is an
  equivalent presentation of Db, retaining its underlying D+ object for the recorded
  witness structure. `_hKc` and `_hLc` test the intrinsic recorded constructibility
  predicate on every cohomology sheaf, not an etale-origin substitute.
- `c0 d0 a b`, `_hcd`, `_hab`, `_hKTor` and `_hLTor` are the ordered intervals and
  the recorded pro-etale Tor predicates, against all degree-zero module sheaves.
- `pfAdmissibleOriginAssertions` first gives actual origin pairs `WK`, `WL` of type
  `Scheme.FixedEtaleOriginWitness`, with bounded constructible antecedents and the
  two etale `hasTorAmplitudeIn` assertions in exactly the same intervals.
  The structures retain `.complex` and the specified `.iso` of the canonical comparison.
- Its universal clause quantifies over every `WK`, `WL`, assuming only that their
  antecedents are bounded constructible. It concludes the same Tor bounds and all
  model assertions. Thus preassigned representatives and isomorphisms are covered;
  no existential choice is used to alter their witnesses.
- `∀ u0 v0`, `u0 ≤ v0` and the displayed vanishing of
  `DerivedCategory.homologyFunctor` give every cohomological support interval of K0.
- `pfAdmissibleModelAssertions` existentially supplies complexes `C`, `P`, with
  `Nonempty (DerivedCategory.Q.obj C ≅ K0)` and its P analogue. C is zero outside
  `[u0,v0]`; P is zero outside `[a,b]`, and every P term satisfies the recorded
  `exactFunctor` condition for the actual sheaf tensorRight.
- `RP` is exactly termwise `Etale.upperStar ... r`; `JC` is exactly termwise
  `Etale.openImmersionLowerShriek ... j`. The `quasiIso.kFlat` predicates assert
  K-flatness of P and RP, using the recorded ordinary-module interface. The mapping
  cone criterion and signed symmetry identify this with acyclic total-tensor K-flatness.
- `RL0` is the exact derived constant-coefficient inverse image, hence Lr*L0.
  The RP representation isomorphism has that endpoint. `M0` is the exact derived j!K0;
  JC represents M0 and has the same `[u0,v0]` support.
- `T` is literally `CochainComplex.mapBifunctor JC RP (curriedTensor _)`, the recorded
  signed direct-sum total tensor. Its definition has degree-m sum over i+h=m and
  differential d_C tensor 1 plus (-1)^i times 1 tensor d_P. Q0 is literally the
  recorded `Etale.derivedTensor` of M0 and RL0. The representation isomorphism
  and support `[u0+a,v0+b]` are asserted for this actual T.
- `TStructure.t.plus M0` and `.plus Q0` assert bounded-below membership, and
  `QuasiCompact r ∧ QuasiSeparated r` gives precisely the direct-image comparison
  input conditions, including quasi-compactness of the diagonal. The statement
  does not assert any bounded-above property of proper direct images.

Dependency declarations used publicly are: `FiniteFieldDatum` (Sheaf.Paper.FiniteFieldFiber),
`Padic.coefficientExtensionRing` and `finite_coefficientExtensionRing`
(Sheaf.NumberTheory.Padics.CoefficientExtensionFinite), Mathlib's scheme
`LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsSeparated`, `IsOpenImmersion`,
ordinary `Etale.DerivedCategoryModule` (WeilConjectures.AlgebraicGeometry.DerivedCategories),
`comparisonUpperStar.mapDerivedCategory` and its Plus restriction
(Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed),
`IsConstructibleProEtaleFixedModuleSheaf` (Sheaf.Paper.ProEtaleFixedModuleConstructible),
`HasFixedCoefficientProEtaleTorAmplitude`
(Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations),
`isBoundedConstructible` (WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes),
`FixedEtaleOriginWitness` (Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness),
`hasTorAmplitudeIn` (publicly provided by Sheaf.AlgebraicGeometry.EtaleTorAmplitude),
Mathlib's `CochainComplex`, `mapBifunctor`, `DerivedCategory.Q`, cohomology and t-structure,
`exactFunctor` (publicly provided by Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite),
`MorphismProperty.kFlat` (publicly provided by
Sheaf.Algebra.Homology.KFlatIndependentCoefficients),
`Etale.openImmersionLowerShriek`
(WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs),
`Etale.upperStar` and its exact derived functor
(WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar),
and `Etale.derivedTensor` (WeilConjectures.SixFunctors.Etale.Derived.Tensor).
The recorded ProEtaleFiniteModules module is publicly retained for its coefficient
presentation and its equivalence with ordinary fixed-module sheaves.
Every available recorded proof-dependency module is imported privately; the
seven-step theorem docstring gives their use and the full natural-language proof.

Sources read: sites-cohomology.tex, lemma-tor-amplitude (08G1), both implications
and the truncation proof; proetale.tex, lemma-compare-constructible-derived (09AL),
and the current blueprint thm-sf-pf-proetale proof's finite-coefficient transport paragraph.

Edge cases checked mathematically: zero complexes and empty schemes; singleton
intervals c0=d0, a=b and u0=v0; arbitrary negative support bounds; level n=1;
identity open/proper maps; arbitrary prescribed origin automorphisms; non-flat proper r.
No flatness of C or constructibility of its or P's terms is asserted. When a total
summand is nonzero, u0<=i<=v0 and a<=h<=b imply u0+a<=i+h<=v0+b, including negative bounds.
The intrinsic positive-stratification predicate permits empty strata on the empty scheme.

Searches for an existing statement:

- msearch.py leanfinder: "Bounded constructible pro-etale complexes admit etale origins
  with the same Tor intervals and bounded flat models for compactification tensor inputs".
  Eight results concerned etale morphisms and algebra descent; none gave this assertion.
- msearch.py loogle: "CochainComplex, CategoryTheory.Sheaf". Zero hits.
- msearch.py grep: "proetale.*(Tor|flat)|etale.*flatModel|extensionByZero.*[Bb]ounded".
  Zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for the node id, pf_admissible_models and
  admissibleModels: no existing declaration. Broader bounded-flat-model searches
  found generic flat-model and pullback-line results, which do not assert this
  combined origin existence/all-witness compactification statement.

Validation: scompile.py compiled both the sandbox probe and the delivered library module
cleanly (32.8 seconds and 21.9 seconds), with no errors or warnings.
The required deliver2.py --no-push dry run passed preflight and per-file compilation
(commit e106687b974). Only the item node's lean field, its module and this report are delivered.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
