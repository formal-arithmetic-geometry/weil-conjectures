## Worker report

Q76 states `lem-trf-completed-stalk-frobenius-reduction` in
`Sheaf.Paper.CompletedStalkFrobeniusReduction`, with main declaration
`WeilConjectures.CompletedStalkFrobenius.completedStalkFrobeniusReduction`.
Its proof is `sorry`. The other eighteen declarations are concrete helpers for this
same assertion, listed in `lean.declarations`. There are no additional postponed
lemmas, new nodes, dependency-record replacements, or changes to the mathematical
statement.

Source read: blueprint main-20261015,
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.md`
(the coefficient conventions and stalk-normalization paragraphs), and its
`.proof.md`, clause (4). The node's six proof steps are carried into the main
theorem's docstring. The completed target is written in direct-composite-pullback
coordinates. The canonical integral composition comparison identifies this with
`S(L(g_gamma^m)^*K)`; the finite transport explicitly includes the corresponding
finite pullback compositor. This is the same target and normalized transport.

Hypotheses and objects, in the order of the node:

- Finite-field data `p,a,q,k₀,k` are bundled by `(D : FiniteFieldDatum.{u})`.
- The coefficient prime and its exclusion from the characteristic are
  `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The recorded coefficient constructors
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionRing l E (n + 1)` supply the valuation ring,
  selected uniformizer and its quotient, exactly as the coefficient conventions
  specify. No independent coefficient ring or arbitrary quotient is introduced.
- The scheme is `(X₀ : Over (Spec (.of D.k₀)))`, with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]`.
  The first two instances express finite type; the third expresses separatedness.
  `X` is `(D.geometricFiber X₀).left`.
- `K : sfIntegralConstructibleCategory l E X` is precisely the recorded bounded,
  derived-complete integral constructible category. Its reductions are
  `(scalarReductionDerivedExtension l E X n).obj K.obj`. The binder `_hK` in
  each component of `ReductionStatement` requires
  `finiteTorConstructible l E (n+1) (Nat.succ_pos n) X` for every reduction.
  The naturality component imposes the same condition on `L`.
- `(m : ℕ) (hm : 1 ≤ m)` covers all allowed positive iterates, including
  nonminimal periods. `(y : D.extensionPoints X₀ m hm)` is the rational point.
  Its induced geometric point is `localExtensionPoint D X₀ m hm y`, as in the
  source's stalk normalization. `LocalFrobeniusTransport.fixedEquation` supplies
  its `Phi^m` fixed-point equation. The geometric Frobenius power is
  `(End.of (D.geometricGaloisFrobenius X₀)) ^ m`.
- Good complexes `P` and isomorphisms `e : DerivedCategory.Q.obj P.obj ≅ K.obj`
  only present the canonical completed construction. Every such presentation is
  universally quantified; none is imposed as extra structure on the input K.
  The identity-morphism naturality case also compares different presentations.
- Invertibility of l on the point and on X is derived inside `ReductionStatement`
  from `frobeniusPointPrimeInvertible` and
  `D.schemeFrobeniusCoefficientInvertible X₀ l hl`. These are definitions of the
  Prop, not added hypotheses or theorem-statement let binders.

Each assertion of the node:

1. The completed stalk is `integralFibreLarge D l E v`: the inclusion of integral
   constructible objects, then the recorded `integralDerivedPullback l E v`,
   then exact point sections. `finiteFibre D l E v n` uses
   `proEtaleConstantRingDerivedPullback` and the recorded finite sections.
2. The canonical reduction isomorphism is `reduction D l hl E v K P e n`.
   Its first factor is `sectionsReduction`, the uniquely unit-normalized
   comparison selected from `pointReductionUnitNormalization`; its second factor
   is exact sections applied to `integralPullbackReductionIso`. The latter is
   the recorded projection-adjoint comparison. An arbitrary isomorphism with the
   same source and target is never substituted.
3. `finiteTransport` is the published
   `LocalFrobeniusTransport.finiteNormalized`, followed by the canonical finite
   compositor and canonical localization-size comparisons. The published map
   is `finiteRho` followed by fibre pullback of `finiteKappa`; these are exactly
   the fixed-point iota and the specified scheme/Galois kappa.
4. `integralTransport` uses the published
   `LocalFrobeniusTransport.integralNormalized`, with the same canonical size
   comparisons. That definition uses `integralModel`, the whole strict quotient
   tower map `strictMap true`, and the full two-component `integralOperationsRoosMap`.
   Thus it is the specified derived-limit realization, not a chosen lift of maps
   in a triangulated category and not a degree-zero replacement.
5. The first conjunct of `ReductionStatement` is the reduction square:
   `tensor.map integralTransport ≫ reduction_target.hom =
   reduction_source.hom ≫ finiteTransport`. This includes every positive exponent.
6. The second conjunct treats every `a ≤ b` and both source and target stalks.
   `restrictedModel` identifies the finite stalk, restricted to the valuation
   ring, with the actual term of the strict quotient tower. `transition` is the
   actual tower arrow, transported through these canonical identifications.
   `reductionAdjoint` is `unit ≫ restriction.map reduction.hom`. The equation
   `reductionAdjoint_b ≫ transition_ba = reductionAdjoint_a` is the transposed
   quotient-coherence square. Under the normalized successive-quotient
   adjunction, this says exactly that two successive derived scalar extensions
   give the direct reduction. It uses the actual units and tower arrows, not
   faithfulness of the restriction functor. No flatness of A_a over A_b is used.
   Together with the first square this also gives quotient coherence for tau.
7. The third conjunct quantifies every `f : K ⟶ L` and every pair of good
   representatives. Its first equation is integral transport naturality; its
   second is reduction naturality at both stalk maps and every positive n.
   Consequently the full reduction squares commute with every integral morphism.

Derived-category sizes: the point-fibre API uses the small Grothendieck
localization of coefficient modules, whereas the unit-normalized reduction API
uses `HasDerivedCategory.standard`. `moduleSizeLift` is the derived functor of
the identity exact functor between these localization models.
`integralSectionsSize` and `finiteSectionsSize` are the canonical composition
comparison followed by the identity-functor unitor. No equality of site universes
is imposed and no coefficient action is forgotten. `integralSectionsLarge`,
`finiteSectionsLarge`, `integralSectionsLargeFactors` and `moduleQLarge` merely
make this canonical size transport explicit; they do not introduce a second
mathematical stalk or a different coefficient construction.

Dependency declarations read and reused (names are in namespace
`WeilConjectures` unless qualified otherwise):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions`, and its finite-field/coefficient data.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `FiniteFieldDatum.schemeFrobeniusIterate`, `geometricGaloisFrobenius`,
  `schemeFrobeniusCoefficientInvertible`.
- `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructibleCategory`, `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteCoefficientPoint`:
  `pointFibreIntegralAmbient`, `pointIntegralSections`, `pointFiniteSections`
  and their exactness declarations.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `integralDerivedPullback`, `constructibleIntegralPullback`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`:
  `integralPullbackFiniteComparison`, `integralOperations_preserve_constructible`.
- `Sheaf.Paper.PointSectionsDerivedReduction`:
  `pointReductionModuleTensor`, `pointReductionTensorSections`,
  `pointReductionSectionsTensor`, `point_sections_derived_reduction`.
- `Sheaf.SixFunctors.SelectedSchemeGaloisComparison`:
  `FiniteFieldDatum.canonicalSchemeGaloisComparison`, used by the published kappa.
- `Sheaf.Paper.LocalFrobeniusTransportNormalization`:
  `LocalFrobeniusTransport.finiteSectionsDerived`, `finiteNormalized`,
  `fixedEquation`, `strictTower`, `integralNormalized`, `integralModel`.
- `Sheaf.Paper.PointReductionUnitNormalization`:
  `pointReductionUnitNormalization`.
- `Sheaf.Paper.PointReductionUnits`:
  `pointUnitIntegralModuleUnit`, `pointUnitIntegralDerivedRestriction`,
  `pointUnitIntegralDerivedSectionsRestrictionIso`.
- `Sheaf.Paper.IntegralPullbackComposition`:
  `integralPullbackReductionIso`, `integralPullbackComposition`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralFinitePullbackModel`, `integralFiniteCanonicalPullbackComposition`.
- `Sheaf.Paper.IntegralOperationsWellDefined`:
  `integralOperationsGoodComplex`, the strict quotient and full Roos machinery.
- Mathlib: `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryCompIso`,
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryFactors`,
  `Functor.rightUnitor`, `DerivedCategory.Q` and ordinary categorical composition.

The old recorded `def-trf-frobenius-operators` module
`WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` was read: its
`AlgebraicGeometry.Etale.frobeniusOperator` concerns the etale Hom-of-unit
presentation. The precise pro-etale finite fixed-point map and completed
realization needed here already belong to the landed local-normalization node;
those existing declarations are reused, and that node is added to `stmt_deps`.
No duplicate operator definition or replacement dependency record is delivered.
The other four added statement dependencies are also already landed nodes:
`lem-trf-point-reduction-unit-normalization`,
`lem-pod-integral-pullback-composition`, `def-trf-point-reduction-units`, and
`lem-weil-pbc-proetale-derived-pullback-composition`. None has a path back to
this item in the statement/proof dependency graph. Every recorded proof-dependency
module available on the base is explicitly imported; the proof-only
`lem-trf-fixed-stalk-identification-reduction` has no recorded module to import.

Edge cases checked before finalizing:

- n=0 in Lean denotes A_1; successors cover exactly all positive quotient
  exponents of the source. No nonexistent positive-exponent case is dropped.
- a=b is allowed in quotient coherence; the strict tower arrow is the identity.
- m=1 and every larger period are admitted without a minimal-period hypothesis.
- The zero complex and zero morphisms are admitted, with no nonzero/cohomology
  assumptions. All morphisms are allowed, not just isomorphisms or Weil structures.
- The empty scheme admits no rational point y; its pointed assertion has the same
  empty range as the source. No nonemptiness assumption on X is added.
- l=p is excluded exactly by the source. Residue-field invertibility is derived.
- No quotient flatness, independent universe equality, finite Tor bound beyond
  the source, or chosen arbitrary transition map is assumed.

Searches performed with the prescribed launcher and read-only trees:

- `msearch.py Q76 <item> leanfinder` query
  `Completed geometric stalk Frobenius transport commutes with derived reduction
  modulo powers of a uniformizer`: eight results, concerning pretilt/BdeRham,
  Witt vectors and related topics; no matching completed-stalk assertion.
- `msearch.py ... loogle "SheafOfModules.pullbackComp"`: five ordinary
  pullback-composition/associativity declarations; none states this theorem.
- `msearch.py ... grep "stalk.*reduc|reduc.*stalk|frobenius.*stalk"`:
  fifteen ordinary stalk/function-field results; no matching derived-complete
  pro-etale theorem.
- `rg` of the upstream WeilConjectures tree for Frobenius/stalk notions located
  the WeilSheaf stalk Frobenius API, whose statement is different. The exact node
  id has no upstream hit.
- `rg` of `lean/Sheaf` found the published local-normalization module and
  completed-stalk reparametrization-coherence module. Neither states this
  reduction theorem; the former supplies the exact canonical maps reused here.
- `rg` for `CompletedStalkFrobenius|completedStalkFrobeniusReduction` in
  `dag/lean_names_upstream.json`, upstream WeilConjectures, Mathlib and shared
  `lean/Sheaf` returned no declarations with these new names.

No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by Q76

The dispatcher explicitly prohibits starting other agents and assigns the
maintainer the independent delivery review. Accordingly this section records
Q76's own second pass, not a claimed independent worker review.

I reopened the node, source clause (4), and the final Lean file. I checked the
finite-field data, prime exclusion, extension, finite-type separated scheme,
derived-complete integral object, all finite-Tor reductions, positive iterate,
rational point and induced fixed geometric point against the binders above.
I then checked the canonical alpha factors, iota-then-kappa finite transport,
whole strict-tower integral transport, reduction square, both quotient diagrams,
and naturality for arbitrary integral maps against the three conjuncts of
`ReductionStatement`.

The first draft mixed small and standard derived localizations of point modules.
It was repaired by the explicit identity-induced size functor and its normalized
sections isomorphisms; the site and coefficients remain those of the dependencies.
The finite and integral target maps now both use composite-pullback coordinates,
with the published finite compositor included explicitly. The transition equation
was checked via the normalized adjunction, so it asserts the full successive
quotient square rather than an equality after merely forgetting scalars.
All helper data are constructed; the sole postponed proof is the main theorem.

Validation: the prescribed `scompile.py Q76
lem-trf-completed-stalk-frobenius-reduction <module>` completed successfully for
both the sandbox check and the final library-path check, with no compiler errors
or warnings. All universes and variables are explicitly bound; `autoImplicit`
is disabled. No global build or direct Git command was run.
