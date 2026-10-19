## Worker report

Repair of the returned immutable head 680829c4686b. The sandbox was empty on this
attempt. This packet supplies actual stage-2 Lean rather than the stage-1 split:
`Sheaf.Paper.DerivedReductionResolutionIndependence`, with primary declaration
`SheafOfModules.PrincipalReduction.Setup.resolution_independence`, and one authorized
§1(B) dependency interface. Every theorem has proof `by sorry`. Definitions contain
real data, or choose an object determined by a uniqueness or universal-property
statement; no arbitrary comparison map or comparison invertibility is assumed.
All explicit declarations are listed in the respective `lean.declarations` records.
Both node copies are made from the current shared repository; only `lean` changes.
In particular no `mathlib_searches` change is part of this stage-2 repair.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small site is `{C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]` with
  `J : GrothendieckTopology C`. Site object and Hom universes stay separate.
  The sheafification and sheaf-compose instances give the abelian categories in
  coefficient/module universe r, as in the recorded K-flat interface. These are
  infrastructure, not a flatness, boundedness or geometric restriction.
- The final object U and finality are `Setup.U` and `Setup.terminal`.
- O and O' are `Setup.O` and `Setup.S`, sheaves of commutative rings. The coefficient
  homomorphism is `Setup.ρ : R →+* O(U)` and the principal element is `Setup.t`.
- Exactness of Gamma on abelian sheaves is `Setup.sectionsExact`, using exactly
  `(sheafSections J AddCommGrpCat).obj (op U)` and `exactFunctor`.
- The multiplication arrow is `sectionMultiplication O U terminal (ρ t)`, uniquely
  characterized on every section V by multiplication by the restriction of ρ(t).
  It is not an arbitrary endomorphism. `Setup.φ` is the ring-sheaf quotient arrow.
  `Setup.zero` and `Setup.shortExact` express the full short exact sequence on
  underlying additive sheaves, including injectivity and epimorphy. This expresses
  O'=O/tO as a ring sheaf; no sectionwise surjectivity is added to the hypotheses.
- `Setup.A` is literally `R ⧸ Ideal.span {t}`. `quotientMap` is its canonical map.
  `quotientSectionsMap` is `Ideal.Quotient.lift` of φ(U) composed with ρ; its
  well-definedness theorem follows from the displayed coefficient sequence.
- The two ordinary section functors are Mathlib's module evaluation followed by
  restriction along the two specified coefficient maps. `sections_exact` transfers
  abelian exactness to modules. `G` and `G'` are their `mapDerivedCategory` functors.
  The four derived localization Hom universes wO,wS,wR,wA are independent.
- `extension` selects the universal pair from the repaired recorded change-of-rings
  dependency. Its ordinary `E` is fixed on objects by `obj_eq` and maps by `map_eq`.
  `quotientComplex` is E applied termwise, representing P/tP, and `T` is the
  universal derived extension. `modelIso P hP` is exactly its counit on P, made
  invertible by the recorded K-flat computation, with no arbitrary model isomorphism.
- `tensorFamily` comes from `exists_derivedTensor_second_factor_functor`;
  `L` is its value at the regular quotient module in degree zero (`quotientSingle`).
- The actual counit `pointwiseCounit` comes from the recorded
  `exists_mixedTensor_pointwise_leftDerived`. `c` transports it to the specified L
  by `Functor.leftDerivedUnique`, then uses `tensorSingleIso` to identify tensor
  with A[0] with termwise scalar extension (the ordinary quotient C/tC).
  This construction applies to every C, with no K-flatness hypothesis on Gamma(P).
- `quotientSection M x` is constructed using the module-sheafification unit on
  `1 tensor x`, followed by the prescribed E-object equality. Thus it is the actual
  quotient section, not a supplied map.
- `theta P hflat` is the uniquely determined complex isomorphism whose degree-i map
  sends `a tensor x` to `quotientSectionsMap(a)` times that quotient section.
  The theorem `existsUnique_theta` includes this normalization for every i,a,x;
  pure tensors generate, so it determines the entire isomorphism. Its source is
  termwise scalar extension of Gamma(P), representing C/tC; its target is
  Gamma(P tensor_O O'), representing Gamma(P/tP). The flat-term hypothesis uses
  the recorded `IsFlatOnSite` in every integer degree.
- `alpha P hP hflat` composes the G localization factor, c, Q_A(theta), the inverse
  G' localization factor, and G' of the inverse K-flat counit. Hence its source is
  LG(QP) and its target is G'T(QP), with exactly the canonical identifications in
  the node. It is a real composite, not an arbitrary morphism or a hypothesis.
- The first conjunct of `resolution_independence` quantifies every chain map h,
  two K-flat predicates and both flat-term predicates. It states
  `alpha_P ≫ G'T(Qh) = LG(Qh) ≫ alpha_P'`, the node's naturality equality in Lean
  composition order. It imposes no quasi-isomorphism hypothesis on h.
- The second conjunct quantifies every complex M and both supplied augmentations
  p,p' with `QuasiIso` instances, and both K-flat and flat-term hypotheses. Its
  `resolvedComparison` is `LG((Qp)^(-1)) ≫ alpha_P ≫ G'T(Qp)`. Equality of the two
  such morphisms has exactly source LG(QM) and target G'T(QM) in D(A).
  No inverse of alpha appears, and neither conjunct asserts alpha invertible.

The nine recorded statement dependencies are used as follows:

1. `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
   `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
2. `def-pc-cochain-complex-modules`: `Mathlib.Algebra.Homology.HomologicalComplex`,
   `CochainComplex` and its ordinary chain-map category.
3. `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
   `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`.
4. `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlat`,
   `CochainComplex.IsKFlatIndependentCoefficients`.
5. `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
   `SheafOfModules.IsFlatOnSite`.
6. `def-pur-sheaf-tensor-product`:
   `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` publicly reexports
   `TensorProductOfUniverses`, which reexports `TensorProduct`; the actual maps here
   use `SheafOfModules.changeOfRings`, `changeOfRingsHom`, and
   `changeOfRingsPresheaf` with the module-sheafification unit, precisely the canonical
   change-of-rings clause of this recorded notion. No new tensor is defined.
7. `lem-pur-derived-change-of-rings`: the §1(B) module described below, retaining the
   original recorded independent-coefficient source import.
8. `lem-pc-derived-tensor-second-factor-functor`:
   `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`,
   `DerivedCategory.exists_derivedTensor_second_factor_functor`.
9. `lem-pc-mixed-tensor-pointwise-left-derived`:
   `Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived`,
   `DerivedCategory.exists_mixedTensor_pointwise_leftDerived`.

The proof-only `Sheaf.Algebra.Homology.DiagramKFlatReplacements` import retains the
strict-cospan proof plan (`CochainComplex.exists_diagram_isKFlatResolution`). The
main docstring spells out all six DAG proof steps, including the equalities qa=pr
and qb=p'r', two-out-of-three, and both cancellation calculations.

Edge cases checked: unbounded complexes in either direction; zero complex and
identity resolutions; an arbitrary chain map h (not necessarily a quasi-isomorphism);
zero ring sheaves and zero quotient ring; t a unit (zero quotient); t=0 (the
coefficient monomorphism then forces O=0); R with t-torsion (no regularity on R is
assumed); distinct source and target localization universes; a site with different
object and Hom universes. Exactness is on abelian sheaves, and none of the definitions
requires ordinary quotient tensor to be exact on arbitrary R-modules. The only
invertible comparison used inside alpha is the sheaf derived counit on a K-flat model.
A site without a final object is outside the stated hypotheses, as it should be.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: "exact global sections sheaf K-flat principal quotient derived tensor
  comparison independent of resolution". Eight hits concern ordinary-module flat
  exactness and faithful flatness; none states this sheaf derived coherence.
- Loogle: "CategoryTheory.Functor.leftDerivedNatTrans, ModuleCat.extendScalars".
  No hits. The actual leftDerivedUnique API was read in Mathlib's LeftDerived.lean.
- Mathlib grep: "extendScalars|tensor.*single|single.*tensor" in
  Algebra/Category/ModuleCat. Returned ordinary scalar-extension constructions and
  adjunctions. Those are used, but no exact-sections resolution-independence theorem.
- LeanSearch: "exact sections commute quotient tensor derived counit K-flat resolution
  naturality". Eight hits include projective-resolution naturality and the generic
  totalLeftDerivedCounit; none is the statement for unbounded sheaf K-flat models.
- rg in upstream WeilConjectures and the current Sheaf tree for this item ID,
  pointSections/PointSections/exactSections/ExactSections, and then
  resolution_independence/existsUnique_theta/sectionMultiplication. Existing point
  reduction statements concern a particular pro-etale point and coefficient rings,
  not this arbitrary small-site lemma. No declaration with the new names was found.
  Read PointSectionsDerivedReduction, the independent coefficient change-of-rings
  source (also via scompile.py --source), KFlat, FlatOnSite, SiteTensorFunctoriality,
  MixedTotalTensor, MixedTensorPointwiseLeftDerived and DerivedTensorSecondFactorFunctor.
- Read Stacks sites-cohomology.tex lemma-derived-base-change (06YY), sites-modules.tex
  definition-flat (03ER), and more-algebra.tex construction and lemma-derived-base-change
  (06Y6), including its explicit A[0] specialization.

No statement correction, new independent notion, or STATEMENT-DISPUTED flag is needed.
The setup, scalar maps, normalized quotient comparisons and composites are helpers of
this node's own notion, listed in lean.declarations with source/blueprint docstrings.

## Dependency modules

`lem-pur-derived-change-of-rings` receives
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`. The recorded theorem
`derivedChangeOfRingsIndependentCoefficients` requires one common localization Hom
universe w for both sheaf derived categories and only exposes the counit after the
homotopy quotient. That interface cannot be used for the independent wO and wS in
this statement. The repair's `DerivedChangeOfRingsCochainModel` specifies the ordinary
functor on objects and maps, additivity, K-flat quasi-isomorphism preservation,
the universal left-derived pair, triangulatedness and the invertible K-flat counit.
`nonempty_derivedChangeOfRingsCochainModel` states existence with a complete proof plan.
Its cochain formulation is equivalent to the homotopy formulation and supplies the
canonical comparisons, including their compatibility through the one universal pair.
The model is chosen only from this universal property, which determines it up to
unique counit-compatible isomorphism. The dependency's lean.note explains the repair;
no other dependency field changes. No site-universe equality is imposed.

## Second reading by NZ

A separate second pass reopens the current DAG statement and the actual module.
The returned H1/H2 defects are repaired by actual modules, complete lean records,
verbatim primary signatures and this Worker report; no stage-1 search-field delta
is delivered. H8 is repaired by source/blueprint docstrings and the six-step proof
plan. H10 is checked by per-file scompile.py and the required delivery dry run.
The second pass verifies each Setup field against the corresponding hypothesis,
the full principal coefficient sequence, actual R/(t) coefficient action, both exact
section functors, both recorded universal tensor interfaces, the normalized theta,
the counit formula for alpha and both equality clauses. It checks the domain and
codomain of every factor in alpha and resolvedComparison and confirms that no
invertibility of alpha was added. It also reads the dependency module against both
clauses of its DAG statement, including its canonical K-flat computation.

Mismatches repaired during elaboration: the additive-sheaf forgetful functor is the
actual composite CommRingCat -> RingCat -> AddCommGrpCat, not a nonexistent direct
forget₂ instance; sheaf-composition infrastructure is explicit in the coefficient
universe; definitions on Setup live in its namespace so their projected applications
resolve; the formula for theta uses the induced coefficient map explicitly on the
right-hand side. The localization universes remain separate after these repairs. Exact module-section
functors additionally receive their inherited additive instances from preservation
of binary products and zero morphisms, using Mathlib rather than a postponed proof.
