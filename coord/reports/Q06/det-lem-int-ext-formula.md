## Worker report

The module `Sheaf.Paper.IntegralStratumHomFormula` states both clauses of
`det-lem-int-ext-formula`. Its two theorems have `sorry` proofs; the four auxiliary
names are actual constructions from existing functors, with no postponed data.
The resolved stage-1 repair note has been read: the refined proof plan, including
the fibre-degree-one and surjective-closed-reflection steps, is retained.
No statement correction or dependency-record repair is made.

Hypothesis and conclusion correspondence:

* Prime l: `(l : ℕ) [Fact l.Prime]`. A finite extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The valuation ring and the
  chosen uniformizer are the existing coefficient-extension constructions, used by
  `integralCoefficientRing` through `DerivedNakayama.integerRing`; no alternative
  valuation, uniformizer, topology or condensed realization is chosen here.
* Positive characteristic unequal to l: `(k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`. For a field, positive
  characteristic is prime, so this is the standing setting. The base scheme data are
  `[X.Over (Spec (.of k))]`, `[LocallyOfFiniteType (X ↘ Spec (.of k))]`,
  `[QuasiCompact (X ↘ Spec (.of k))]` and `[IsSeparated (X ↘ Spec (.of k))]`.
  Locally finite type plus quasi-compact means finite type. There is no Noetherian,
  reduced, smooth, dimension-bound or algebraically closed extra hypothesis.
* Each site is `Scheme.ProEt.topology X`. The actual pulled-back coefficient is
  `condensedRingObj (integralCoefficientRing l E) X`, as encoded in
  `pulledBackModuleObjects` and `integralDerived`. This is the ambient ordinary
  unbounded derived category, not a derived-complete subcategory. Object/site sizes
  are u+1/u, coefficient sheaves have sections in u+1, and filtered index categories
  range over `Type (u + 1)` with `SmallCategory`; no site universes are equated.
* The constructible input in clause (1) is `C : integralDerived l E X` with
  `hC : constantModelBoundedConstructible ... X C`, the exact finite constant scalar
  model definition of the recorded constructibility dependency.
* A common finite stratification is the existential
  `S : X.FiniteLocallyClosedStratification`. This recorded structure includes finite
  disjoint locally closed subsets covering X, their scheme realizations and immersions.
  The filtration length m is independent of the number of strata, so different
  cohomological degrees can contribute pieces on the same stratum.
* The filtration itself is `F : Fin (m + 1) → integralDerived l E X`,
  `IsZero (F 0)`, `Nonempty (F (Fin.last m) ≅ C)`, and one distinguished triangle
  `T r` for every `r : Fin m`. Its first and second vertices are exactly
  `F r.castSucc` and `F r.succ`. Thus this is actual finite successive extension
  data, not merely membership in an abstract triangulated closure.
* Every graded piece existentially specifies `a : Fin S.n`, an intermediate Z,
  `v : S.domain a ⟶ Z`, `i : Z ⟶ X`, open/closed immersion instances and
  `v ≫ i = S.immersion a`. These are precisely u, i and a = i ∘ u in the source.
* Its L is a module sheaf on that stratum, with
  `IsConstantModelConstructible ... L` and `HasFiniteConstantLocalModel ... L`.
  The latter is the existing pro-etale-cover condition with finite scalar
  presentations on the point. Over the valuation DVR, finitely generated modules
  are finitely presented; their scalar matrices allow torsion, not only free modules.
* The third vertex is isomorphic to the shift by `n : ℤ` of the degree-zero image
  of `(lowerStar ... i).obj ((openImmersionLowerShriek ... v).obj L)`.
  This is exactly `a_! = i_* u_!`, using ordinary exact closed direct image.
  The implication `homologyConcentratedIn 0 0 C → n = 0` forces all pieces into
  degree zero whenever C is a sheaf (including any isomorphic degree-zero image).
* Clause (2) quantifies over every closed i and open v, and their local-model sheaf L.
  Such a locally closed image can be completed to a finite stratification by its
  complementary open and closed pieces; no particular adapted stratification is
  needed in the formula. Z and S inherit the standing geometry over k from these
  immersions. The auxiliary open j with `Set.range j = (Set.range i)ᶜ` explicitly
  presents the complement needed by the recorded support functor. Every closed
  immersion has such an open complement; this does not restrict the stratum.
* `integralStratumSections` is the existing `preadditiveCoyoneda` at
  `Mod.regular (condensedRingObj ... X)`, so it is precisely Hom(O,-), in the
  internal-module presentation. `integralStratumDerivedSections` right derives that
  functor using canonical K-injective replacement. These are the module-object
  specialization of the definition of RΓ in the recorded hypercohomology node.
* `integralStratumDual` applies the existing `derivedHom` to the degree-zero image
  of L and the unit of the ordinary derived tensor category. Thus it is
  R-Hom(L,O), including torsion and its positive-degree dual contribution.
* `integralStratumDualTensor` is a canonical alias for left tensor by that dual,
  directly delegating to `derivedTensor`; it chooses no monoidal structure.
* The first conclusion of `integral_stratum_hom_formula` is `Nonempty (F ≅ G)`
  for two functors on the whole ambient derived category of X. The left functor is
  `derivedHom` out of the degree-zero `i_*u_!L`, followed by RΓ_X. The right functor
  is the right derived `closedModuleSectionsWithSupport`, the exact derived inverse
  image along v, tensor on the left by `integralStratumDual`, then RΓ_S. This is the
  asserted natural isomorphism for every unbounded K, with all its morphisms. The
  existential additive structure only exposes the structure asserted by the
  support dependency; it is not an added assumption or an arbitrary support functor.
* `DerivedCategory.torAmplitudeIn _ 0 1 (integralStratumDual ... L)` is precisely
  Tor amplitude contained in [0,1], tested against every module in degree zero.
* Filtered colimit compatibility is stated on a K-flat complex P representing that
  dual: `Q.obj P.obj ≅ integralStratumDual ... L`, a natural comparison identifying
  its tensor-complex functor with the existing derived tensor, and
  `PreservesColimitsOfShape I` for every small filtered I. The complex tensor is the
  existing monoidal tensor of complexes, i.e. the signed direct-sum total relative
  tensor. Its colimits are degreewise module colimits. This renders the source's
  explicit complex-model interpretation, avoiding an assertion that degreewise
  filtered colimits are categorical colimits of the homotopy category D.
* Countable inverse limits retain an entire strict diagram
  `B : ℕᵒᵖ ⥤ CochainComplex (...) ℤ` and its transition chain maps. For every Roos
  triangle `IsDerivedLimitTriangle ... A p δ`, the tensored object has the Roos
  triangle for the tensored transitions. Its first arrow is the canonical
  `Pi.lift` of the images of `p ≫ Pi.π ... n`, retaining every projection map.
  Existence of the two countable products is expressed by `HasProduct` instances;
  these exist in the setting and are the data used to type the recorded Roos
  definition, not an exact-products assumption. The strict-tower dependency
  identifies these triangles with total derived inverse limits of strict systems.

Dependencies used (module → declarations):

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  → the standing separated finite-type-over-field setting in
  `CondensedRing.compactificationOverField`; no compactification is needed here.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` → the valuation-ring,
  uniformizer and finite-quotient constructions of `Padic`, imported unchanged.
* `Sheaf.Paper.IntegralDerivedCoefficientData` → `integralCoefficientRing`,
  `integralDerived`. This already landed definition node is added to stmt_deps
  because these canonical aliases are directly used in the statement.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` → `coefficientRing`,
  `condensedRingObj`; `Mathlib.AlgebraicGeometry.Sites.Proetale` →
  `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.Paper.CondensedConstantConstructibility` →
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`; its Tor notion is the existing
  `DerivedCategory.torAmplitudeIn` from the upstream TorAmplitude module.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` →
  `CondensedRing.derivedHom`, and its Tensor import → `CondensedRing.derivedTensor`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` →
  `lowerStar`, `upperStar`; the LowerShriek.Defs module →
  `openImmersionLowerShriek`. These are the actual recorded module functors.
* `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses` →
  `ringedSiteZerothHypercohomologyOfUniverses`, whose RΓ construction is specialized
  to internal modules by the two section helper aliases above.
* `Mathlib.CategoryTheory.Triangulated.Pretriangulated` → `Triangle`,
  `Pretriangulated.distinguishedTriangles`; the Triangulated interface supplies
  the octahedral proof step.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` →
  `Scheme.FiniteLocallyClosedStratification`; Mathlib OpenImmersion and
  Morphisms.ClosedImmersion → `IsOpenImmersion`, `IsClosedImmersion`.
* `Sheaf.Paper.FormalClosedSupportDerived` → `formal_closed_support_derived`,
  and its sheaf module → `closedModuleSectionsWithSupport`.
* `Mathlib.CategoryTheory.Limits.HasLimits` → colimits/IsColimit,
  the existing complex tensor and `PreservesColimitsOfShape` express the
  canonical filtered colimit comparison, with `CategoryTheory.IsFiltered`.
* `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
  → `ringedStrictTowerHomotopyLimitIndependentCoefficients`;
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit` →
  `IsDerivedLimitTriangle`. These preserve the strict-tower interpretation.
* `def-weil-size-convention` has its recorded convention-only binding; u/u+1
  explicitly implement it here, without introducing a second site or arbitrary
  universe-equality assumption.

All available recorded proof-dependency modules are imported without `public`;
statement construction modules are public. The integral heart and its dualizability
lemma have no recorded statements yet and therefore have no proof import to add.
The Mathlib-leaf proof dependencies are reached through their actual modules,
including the dual tensor adjunction, unique right adjoint, finite-type Noetherian
and immersion base-change interfaces.

Edge cases checked: zero C admits m=0 and the zero filtration; on the empty scheme
S.n=0 and m=0 are allowed. The finite filtration may revisit a stratum, as required
for several cohomological degrees. Zero L, free L and torsion L=O_E/pi are all admitted
by the local-model hypothesis. For torsion L the derived dual has its nonzero
contribution in degree 1, which explains the interval [0,1] and excludes replacing
R-Hom by ordinary Hom. The formula allows unbounded K. Constant, zero and arbitrary
strict towers retain their transitions; no Mittag-Leffler or exact-products
hypothesis is imposed. Filtered indices include all small filtered categories,
not merely sequential diagrams. Schemes need not be reduced or smooth.

Searches for an existing statement/helper:

* msearch LeanFinder: `constructible integral pro etale sheaf finite filtration
  extension by zero global derived Hom formula` returned eight unrelated sheaf
  cohomology/condensed/finite-presentation declarations; no matching theorem.
* msearch LeanSearch: `constructible integral module finite filtration extension
  by zero derived Hom` returned eight generic module-filtration declarations;
  no matching theorem.
* msearch Loogle: `CategoryTheory.Triangulated.Filtration,
  PreservesFilteredColimits` returned unknown Filtration/no hits.
* msearch grep: `filtration|Filtration` in `CategoryTheory/Triangulated` returned
  no hits. `constructible.*(filtration|Hom)|filtration.*constructible` returned
  only five unrelated constructible-subset/RingHom hits.
* rg in the upstream project, side framework and Sheaf sources found related
  IntegralTensorShriek generation (abstract extension closure, not a finite
  triangle filtration), IntegralExtensionByZero (functor preservation),
  FormalClosedSupportDerived (closed support only), and IntegralExtHomContinuity
  (a consumer of this formula), not this statement. Searching the item id in
  upstream found no declaration. The side framework is absent in the older
  slopmaster2 checkout, so its exact sources were read under the authorized
  shared `lean/WeilConjectures` path.
* rg for `preadditiveCoyoneda` with `Mod.regular` and for derived/global section
  definitions found ring-sheaf or fixed-coefficient sections interfaces. None
  gives the internal-module specialization used here; the helper specializes
  the existing Mathlib Hom functor rather than copying a sheaf construction.
* `tools/blueprint_refs.py search finite filtration` and DAG grep found existing
  filtered abelian-object and filtered-complex notions, not a distinct reusable
  finite triangle-filtration interface. The theorem writes its triangle data
  directly; no new definition node is needed.
* New fully qualified declaration names were searched in upstream, Mathlib
  and side sources and had no collisions. The source and docstrings of every
  recorded statement dependency were read; the metatheoretic size convention
  has no declaration to open. The coefficient alias source was also confirmed
  with `scompile.py --source Sheaf.Paper.IntegralDerivedCoefficientData`.

Validation: single-file compilation and required delivery preflight are run
through scompile.py and deliver2.py; final results are recorded below.

Final validation: deliver2.py --no-push reported OK for commit 051b507963:
all single-file compilation checks passed without warnings, and the server
preflight passed. The only two postponed proofs are
`integral_stratum_filtration` and `integral_stratum_hom_formula`.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
