## Worker report

The module `Sheaf.Paper.PointExactDerivedModel` states the exact point-model lemma.
There are five postponed named theorems, all with whole-proof `sorry` and the node's
proof in their docstrings: `exactness`, `composition`, `preserves_constructible`,
`evaluation_restriction`, and `descent`. Every other declaration is actual data,
an abbreviation of an existing construction, or selection from an existence-and-uniqueness
characterization. No definition, dependency record, or mathematical statement was changed.
All names below are in `WeilConjectures.PointExactDerivedModel` unless qualified.

Hypotheses and objects:

- `D : FiniteFieldDatum.{u}` supplies the prime p, positive a, q = p^a, finite k0 of
  cardinality q, and its fixed algebraic closure k, with its original structural map.
- `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` is the distinct coefficient prime. `E : Type u`,
  `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` is the recorded finite extension.
  `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` is the chosen
  coefficient algebraic closure, and `(_ι : E →ₐ[ℚ_[l]] Ω)` is the specified embedding
  of E into it. An algebra homomorphism from the field E is injective, so this is exactly
  E as a finite extension inside that closure, retaining E's existing coefficient-ring
  presentation. The independent universe v puts no extra size constraint on the closure.
  No new coefficient field or valuation is chosen here.
- `(n : ℕ) (hn : 1 ≤ n)` is exactly the positive level; each occurrence of A is
  `Padic.coefficientExtensionRing l E n`, using the dependency's valuation ring and
  uniformizer, with exponent n (not n+1).
- `frobenius D` is `Spec.map` of the recorded geometric Frobenius algebra automorphism
  of `D.k` over `D.k₀`. Its arithmetic inverse raises to cardinality k0 = q.
  `power D` is the usual scheme-composition power, recursively exposing the positive
  cases: power 1 = h, power (m+2) = h ≫ power (m+1).
- `modules D A` is `proEtaleRingModules (Spec (.of D.k)) (proEtaleConstantRing _ A)`.
  It transparently uses `ringedSiteModules`/`SheafOfModules` over the constant sheaf.
  Its derived category is the standard ambient unbounded `DerivedCategory`, localized
  by `DerivedCategory.Q`; no constructible or bounded termwise condition is imposed.
- The original site has object universe u+1 and morphism universe u. The already recorded
  `ULift.{u+1,u} A` coefficient convention is preserved on both module sheaves and the
  target `ModuleCat.{u+1}`. No equality of site universes is introduced.
- `pullback D A r` is `proEtaleConstantRingPullback A (power D r)`, the explicit inverse
  image followed by sheaf tensor scalar change using the actual canonical
  `proEtaleCoefficientInverseImageMap`, packaged as `proEtaleConstantRingComparison`.
  `derivedPullback` is `proEtaleConstantRingDerivedPullback` of the same map, as in the
  recorded general derived-composition interface. Thus the Q used by the composition
  equation is exactly the Q used by its specified K-flat-normalized compositor.
- `evaluation D A` is `(pointFiniteSections D.k A).mapDerivedCategory`. The ordinary
  `pointFiniteSections` evaluates at `ProEt.mk (𝟙 (Spec (.of D.k)))` and restricts scalars
  along `pointConstantSectionMap`; it does not choose a section-ring isomorphism.
- Lean functor composition `F ⋙ G` means G after F. Consequently H_1 H_m is written
  `pullback ... m ⋙ pullback ... 1`, and V Q_r is `derivedPullback ... r ⋙ evaluation ...`.

Clauses:

1. `exactness` asserts finite-limit and finite-colimit preservation for both H_r and Γ,
   and preservation of quasi-isomorphisms by their actual `mapHomologicalComplex (.up ℤ)`
   functors. Positive r is written `r+1`, which ranges over every positive integer.
   Additivity is inherited from the actual functors; together these give exactness.
2. `pullbackFactors` and `evaluationFactors` are the actual
   `Functor.mapDerivedCategoryFactors` natural isomorphisms, not arbitrary existential
   choices. Their signatures identify `DerivedCategory.Q ⋙ Q_r` and
   `DerivedCategory.Q ⋙ V_amb` with termwise pullback/sections followed by localization.
   They apply to every complex without K-flatness. The exact-functor/derived-functor
   dependency identifies these with the total derived functors.
3. `ordinaryComposition D A m` is T_(m+1). It is the inverse of the comparison of
   `proEtaleConstantRingModulePullbackComposition (frobenius D) (power D (m+1)) A`.
   Although that existence theorem does not spell `∃!`, its property uniquely fixes
   the direct-image isomorphism on every section by fibre-product pasting. The conjugate
   isomorphism bijection then fixes the ordinary pullback comparison. Thus choosing
   that witness is determined data, not a choice of an unspecified isomorphism.
4. `derivedComposition D A m` is exactly the published
   `proEtaleConstantRingPullbackComposition h h^(m+1) A`. Its definition is the inverse
   of `proEtaleCanonicalPullbackComposition`, followed by transport along
   `proEtaleConstantRingCompositeCoefficients_eq`. This retains the prescribed K-flat
   characterization and the specified constant-section maps for the composite.
5. `composition` states the requested equation on every complex K. With e_r the forward
   factorization, it reads
   `t_(Q K) ≫ e_(m+2,K) = Q_1(e_(m+1,K)) ≫ e_(1,C(H_(m+1))K) ≫ Q(C(T_(m+1))_K)`.
   This is exactly the stated equality after the iterated comparison isomorphisms;
   m : ℕ represents every original m≥1 by m+1. There is no K-flatness, flat-term,
   boundedness, or constructibility hypothesis on K.
6. `preserves_constructible` asserts that Q_(r+1) carries
   `intrinsicFiniteTorsionConstructible l E n hn s` to itself on every ambient object.
   This is the recorded full D^b_c(s,A), not a replacement notion.
7. `evaluation_restriction` identifies `pointFiniteFibre D l hl E n hn` followed by the
   finite-cohomology full-subcategory inclusion with the source inclusion followed by
   `evaluation D A`. This gives precisely V_amb restricted to D^b_c = V, with its
   recorded bounded finite target viewed in D(A). The equality holds by the actual
   construction as a full-subcategory lift; no arbitrary natural identification is used.
8. `descent` quantifies over every `α : Γ ⟶ H_r ⋙ Γ`. No `[IsIso α]` or invertibility
   hypothesis on any component occurs. `α.mapHomologicalComplex (.up ℤ)` is the existing
   degreewise chain map, whose component in degree i is α at K.X i. The theorem asserts
   `∃! αD : V_amb ⟶ Q_r ⋙ V_amb` with the formula
   `αD_(Q K) ≫ V_amb(e_(r,K)) ≫ v_(C(H_r)K) = v_K ≫ Q_A(C(α)_K)`.
   This is the node's formula with both factorization maps explicitly displayed.
9. Since αD is an actual natural transformation on the entire derived category, its
   naturality is for all derived morphisms, including inverse quasi-isomorphisms.
   `descendedTransformation` selects that uniquely characterized transformation.
   Equalities of chain maps, including composites of the given transformations and
   ordinary T, remain equalities under the actual functor `DerivedCategory.Q.map`:
   functoriality preserves their compositions and identities. `composition` and `descent`
   identify these localized factors with the specified t and αD, so substituting the
   displayed formulas and cancelling the intermediate isomorphisms gives precisely the
   claimed equality preservation. This clause requires no additional independently
   chosen map or axiom.
10. `restrictedTransformation` is actual `Functor.whiskerLeft` by the full D^b_c
    inclusion. It retains all components and naturality equations. Together with
    `preserves_constructible` and `evaluation_restriction`, this restricts all the above
    assertions, including compositor equations and localized equalities, to D^b_c.

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (all fields and
  inherited instances); `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, its imported `coefficientExtensionRing`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: geometric field/scheme Frobenius
  conventions; `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`:
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`.
- Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology and final
  identity object; `CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`; `Sheaf.Paper.FiniteCoefficientPoint`:
  `WeilConjectures.pointFiniteFibre`, `pointFibreFiniteLimits`,
  `pointFibreFiniteColimits`, `pointFibre_sections_mem`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory.standard`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`, its reexported
  `Scheme.proEtaleCanonicalPullbackComposition`, and the actual constant-ring
  derived comparison of `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleConstantRing`, `proEtaleCoefficientInverseImageMap`; tensor data remain the
  recorded `SheafOfModules` construction from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the finite exact ordinary-derived pullback
  convention, no constructibility restriction built into the ambient operation.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso`, constant-section normalization;
  `Sheaf.Paper.PointProEtaleSectionsExact`: `ProEtale.pointModuleSections`,
  `point_proEtale_sections_exact`; the scalar-valued version is the existing
  `WeilConjectures.pointFiniteSections` in `CompletedIntegralCoefficientGerm`.
- Mathlib `Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`; Mathlib
  `Algebra.Homology.Additive`: `NatTrans.mapHomologicalComplex`.
- `Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition`:
  `Scheme.proEtaleConstantRingModulePullbackComposition`, with the full sectionwise
  direct-image and adjunction-conjugate characterization read.
- The remaining recorded proof dependencies are imported without `public`:
  `ProEtaleConstantExact` (finite exact inverse image), `ExactFunctorDerivedFunctor`
  (exact total-derived identification), `ProEtaleConstantRingComposition` (actual
  coefficient map composition), `KFlatResolutionIndependentCoefficients` (unbounded
  flat-term K-flat resolution), `IsomorphismDerivedPullback` (finite-level preservation),
  `PointSectionsFiniteness` (finite point target). Their theorem signatures and docstrings
  were read. The localization dependency is its Mathlib match in
  `CategoryTheory.Localization.Predicate`: `liftNatTrans`, `liftNatTrans_app`,
  `natTrans_ext`, `fullyFaithfulWhiskeringLeft`.

Source checks: read Stacks `sites-cohomology.tex` lemma-derived-pullback-composition
(Tag 0D6D), `derived.tex` lemma-right-derived-exact-functor (015F), and
`categories.tex` lemma-properties-left-localization (04VG). Read the main-20261015
point-fibre definition and the ancestor compact-Frobenius-description proof paragraph
starting “That action transports the pair”. The nine-step node proof is represented
in the theorem docstrings. There is no source correction or statement dispute.

Edge cases: m=1 and r=1 are m=0 and r=0 in the offset positive indices; n=1 and all
n>1 are included without replacing n by n+1. K may be zero, acyclic, unbounded, nonflat,
or an arbitrary representative of a constructible object; no termwise bounds are used.
The transformation α can be zero or have noninvertible components. No hypothesis
that all pro-etale sheaves on a point are constant is made. The empty full subcategory,
zero ring/module, or zero complex is not excluded by any artificial nonzero condition.
The fixed s itself is Spec of a field, so is of course nonempty. Universes retain the
small pro-etale site and its original module coefficient size.

Searches (all actual searches, before writing):

- `msearch.py ... leanfinder` query “Exact pullback on a pro-etale algebraically closed
  point identifies the derived composition isomorphism with the ordinary compositor
  on every complex and natural transformations descend uniquely”: 8 hits, including
  ordinary scheme module pullbackComp and its associativity, no exact point theorem.
- `msearch.py ... loogle` query
  `CategoryTheory.Functor.mapDerivedCategoryFactors, CategoryTheory.Localization.liftNatTrans`:
  0 hits for this combined query. Both individual APIs were found and read by source search.
- `msearch.py ... grep` query
  `mapDerivedCategoryFactors|liftNatTrans|derived.*[Cc]omposition`, subdirectory
  `CategoryTheory`: 25 hits, including the generic localization lifting and composition
  API. These do not state the prescribed point compositor identity.
- `msearch.py ... leansearch` query “Exact functors on sheaf modules induce derived
  functors on all complexes and natural transformations descend uniquely through
  localization”: 8 hits, generic left/right derived functor constructions and comparisons,
  no theorem combining the point normalization and constructible restriction.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `point.*[Ee]xact.*[Dd]erived|point-exact-derived-model|pullbackComposition` found related
  section-module and derived-realization interfaces but no exact match. Source searches
  also located and reused the actual factorization, scalar sections, ordinary compositor,
  and normalized derived comparison rather than copying any of them.

Validation: every delivery theorem has its proof postponed, each definition has real
construction data, all universes and variables are explicitly bound, and no private
notation or instance is used in any signature. Compile through the prescribed scompile.py;
only the assigned sandbox is edited. No new independent notion or dependency repair is
needed: the helper declarations specialize existing constructions to this node's objects.

## Second reading by Q131

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
