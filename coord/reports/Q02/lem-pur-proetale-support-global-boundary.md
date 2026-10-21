## Worker report

The delivery states lem-pur-proetale-support-global-boundary without changing its
natural-language statement, dependencies, proof, or other node fields. There are no
new nodes or dependency modules. All new theorem bodies are `sorry`; every definition
has actual data. The module is Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary,
in namespace AlgebraicGeometry.ProEtale.

The statement is distributed across three main declarations:
`supportGlobalTriangleComparison`, `supportGlobalBoundaryNormalization`, and
`supportGlobalComparisonNatural`. The remaining declarations name the canonical
section formulas, row of complexes, inverse derived-unit comparison, and the proof
obligations required for these constructions. All are listed in `lean.declarations`.

Hypotheses and clauses, checked against the node:

* The finite commutative ring is `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`.
  The schemes are `Scheme.{u}`. This is the published finite-coefficient module-sheaf
  size convention; the site still has object universe u+1 and arrow universe u.
* The closed immersion is `i : Z ⟶ X` with `[IsClosedImmersion i]`. The open immersion
  is `j : U ⟶ X` with `[IsOpenImmersion j]` and `[QuasiCompact j]`. The hypothesis
  `hPair : IsCompl (Set.range i) (Set.range j)` asserts precisely that these are
  complementary. The final boundary theorem explicitly retains these hypotheses
  with `include`, even though its kernel-of-restriction conclusion does not use i.
* Ordinary constant-A modules are the existing
  `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)` presentation used by the
  published support and localization interfaces. There is no constructibility,
  completion, torsion-subcategory, or extra coefficient identification hypothesis.
* The node's sheaf supported kernel, i^!_0, and S=Ri^!_0 are the existing
  `finiteSupportedSections`, `finiteClosedUpperShriek`, and
  `(finiteClosedUpperShriek A i j).rightDerivedFunctorPlus`. The sheaf model is
  `supportedSectionsComplex A i j hPair I.obj`, exactly i_*i^!_0 I. The first map is
  `(supportModelSequence A i j hPair I.obj).f`, defined in the dependency using the
  inverse of the canonical closed-unit comparison followed by the actual kernel
  inclusion. It is not an existential rescaling of that inclusion.
* `I : CochainComplex.Plus (...)` and `[∀ n : ℤ, Injective (I.obj.X n)]` give an
  arbitrary bounded-below injective representative. In the boundary normalization,
  `K : DerivedCategory.Plus (...)` and `e : DerivedCategory.Plus.Q.obj I ≅ K` give
  every derived coefficient and every specified resolution identification. For the
  triangle, `supportFirstModelComparison` and `supportThirdModelComparison` in the
  localization dependency identify the displayed model with i_*SK and Rj_*j^*K;
  its first and second arrows are the support counit and the open unit by that
  dependency's `supportLocalizationTriangle`.
* The entire triangle, including beta and its shift, is the existing
  `supportModelTriangle A i j hPair I.obj hq`. Its boundary inverts the specified
  `supportConeQuotient` and then uses the cone's negative shifted projection.
  The theorem gives an isomorphism `e` from its image under the actual triangulated
  `rightDerivedFunctor` of terminal evaluation to
  `supportSequenceTriangle (supportGlobalRow A j I) hqR`. A triangle isomorphism
  includes all three arrow squares, including the shifted first-component map.
* The global row is `supportGlobalRow A j I`. It uses the existing
  `Functor.injectiveBoundaryRow`, `Sheaf.supportedSectionsFunctor`,
  `Sheaf.supportedSectionsInclusion`, and the restriction natural transformation
  `(sheafSections ...).map (supportGlobalRestriction j).op`. Thus its terms are
  exactly Γ_Z(X,I), I(X), and I(U), with their induced differentials. `hR` asserts
  that it is short exact, hence degreewise short exact by the Mathlib equivalence.
* The chain isomorphism `a` identifies sections of i_*i^!_0 I with Γ_Z(X,I), with
  the normalization `a.hom ≫ row.f = Γ(modelSequence.f)`. Because row.f is the
  actual monic kernel inclusion, this determines a uniquely. The isomorphism b
  identifies sections of j_*j^*I with I(U), normalized by
  `Γ(modelSequence.g) ≫ b.hom = row.g`. Restriction on injective section complexes
  is epic; this also determines b uniquely and fixes the direct-image/sections
  identification. Thus neither comparison is an arbitrarily chosen isomorphism.
* `supportGlobalOpenObjectIso`, `supportGlobalOpenSectionIso`, and the natural
  isomorphism `supportGlobalOpenEvaluationIso` give the literal canonical formula
  `(j^*M)(U) ≅ M(U)`, using the recorded upper-star/open-restriction comparison.
  The site-object isomorphism is induced by the identity of U, not a chosen map.
  `supportGlobalOpenDerivedIso` derives this same isomorphism using the published
  unit-compatible composition isomorphism and the exact-functor comparison.
  Consequently the row's third term computes RΓ(U,j^*K). Exact upper star computes
  j^*K termwise, and its injectivity on terms is the published
  `injective_upperStar_obj_of_weaklyEtale`. No injectivity of underlying abelian
  sheaves is asserted.
* `supportGlobalModels_kInjective` supplies K-injectivity for I, i_*i^!_0 I, and
  j_*j^*I. `supportGlobalUnitIso` is exactly the published
  `rightDerivedFunctorObjQIso` after installing the indicated proof. The three
  components of the triangle isomorphism are required to equal those units,
  followed by Q(a) and Q(b) where appropriate. They are not mere existence claims
  about the three derived objects.
* The last clause of `supportGlobalTriangleComparison` states that
  `DerivedCategory.HomologySequence.δ` of the section quotient triangle is
  `hR.δ q (q + 1) rfl`, conjugated by the explicit
  `DerivedCategory.homologyFunctorFactors` comparisons. Together with the full
  triangle isomorphism this is H^q(RΓ(X,beta)), including its shift convention.
* `supportGlobalBoundaryNormalization` produces precisely the existing
  `Sheaf.SupportSequenceBoundary ... ⊤` interface for arbitrary finite A, together
  with `Sheaf.SupportSequenceExact`. It equates the boundary on every I,K,e,q,
  conjugated by the existing `Sheaf.supportSequenceModelIso` comparisons, with the
  same `hR.δ`. This states the normalized supported-cohomology boundary ∂, without
  limiting A to the A_{E,n} specialization of the recorded long-exact theorem.
  The recorded theorem has an existential boundary, not a separately named chosen
  map; its existing general boundary interface and injective normalization are
  therefore reused directly.
* For every `q : ℤ`, cocycle c with `d c = 0`, and every b with `row.g.f q b = c`,
  the final clause supplies a supported cocycle a with `row.f.f (q+1) a = d b`.
  It equates `hR.δ` applied to `homologyπ (cyclesMk c ...)` with
  `homologyπ (cyclesMk a ...)`. This is literally [c] ↦ [db] under the kernel
  inclusion, with no minus sign. No positivity restriction on q is present.
* `supportGlobalComparisonNatural` states the naturality squares for a and b for
  every chain map between any two bounded-below injective representatives, and
  every pair of normalized comparisons. The derived units and derived open
  comparison are natural isomorphisms, and δ is a natural transformation on the
  entire bounded-below derived category. The imported K-injective Hom bijection
  identifies all derived morphisms with these chain maps modulo homotopy; thus
  these squares express naturality in K, including changing resolutions. The
  docstring gives the descent and independence argument explicitly.

Dependency interfaces read and used:

* Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact: QuasiCompact.
* Sheaf.AlgebraicGeometry.ProEtaleFiniteModules: FiniteCoefficientModules and its
  finite-coefficient realization/equivalence with ordinary ModuleCat-valued sheaves.
  The consumer uses the same ModuleCat presentation as the recorded support nodes.
* WeilConjectures.AlgebraicGeometry.DerivedCategories and
  Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  DerivedCategory.Plus, HasDerivedCategory and homologyFunctor.
* Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations: identified constant-ring
  operations; the support nodes use the corresponding published upperStar,
  lowerStar, and upperStarLowerStarAdjunction from the finite-coefficient framework.
* Sheaf.AlgebraicGeometry.ProEtalePairFlasque: finiteSupportedClosedComparison,
  finiteSupportedClosedComparison_isIso, finiteSupportedSections_sections,
  and IsFlasqueForOpen, together with the imported finiteClosedUpperShriek.
* Sheaf.AlgebraicGeometry.SupportTriangleConstruction: supportModelSequence,
  supportModelTriangle, supportConeQuotient, supportSequenceTriangle.
* Sheaf.AlgebraicGeometry.SupportLocalizationTriangle: supportLocalizationTriangle,
  supportFirstModelComparison, supportThirdModelComparison,
  supportModelKInjective, supportOpenModelKInjective, and the derived-unit model API.
* Sheaf.AlgebraicGeometry.SupportCohomology: Sheaf.supportedSectionsFunctor;
  Sheaf.AlgebraicGeometry.SupportLongExact: supportedSectionsInclusion,
  supportSequenceModelIso, SupportSequenceBoundary and SupportSequenceExact.
* Sheaf.CategoryTheory.DerivedInjectiveBoundary: Functor.injectiveBoundaryRow and
  its injective-model boundary normalization; no duplicate generic row is introduced.
* The proof imports retain the recorded ringed-site mono-restriction theorem,
  pro-etale ringed open/closed localization, adjoint preservation of injectives,
  cone quotient quasi-isomorphism, right-derived-plus injective computation,
  long exact sequence naturality, bounded-below injective representatives, and
  K-injective Hom comparison. The proof dependency
  lem-pur-proetale-injective-support-global-model has no Lean record yet; there is
  no module to import. The statement itself needs no object from this unstated
  proof dependency. Its future use in the node's proof is retained unchanged.

Edge cases checked before and after writing:

* Z=X, U empty: restriction has zero target, support is all sections, and boundary
  has zero source. Z empty, U=X: the support kernel is zero and the boundary target
  vanishes. No nonemptiness is imposed on either site object or scheme.
* The zero ring is permitted: no Nontrivial assumption occurs. The zero coefficient
  object and zero complexes are permitted, and all comparison maps specialize.
* Every integer q is included, including zero and negative degrees, with no chosen
  lower bound. A different representative or lower bound changes none of the terms.
* The sign computation is d(b,-a)=(db-u(a),da)=0 and -pr(b,-a)=a. Changing the
  cone's third map to positive projection would yield -[db]; that is excluded by
  supportModelTriangle and the explicit equality with hR.δ.
* No hypothesis equates the site's object and morphism universes. The source's
  u+1 module-value convention is maintained throughout.

Searches for an existing statement (msearch.py Q02, this item):

* LeanFinder: "Derived global sections of pro-etale support localization triangle
  boundary equals differential of a lift without sign". Eight hits, including
  CochainComplex.mappingCone.δ_liftCochain and d_fst_v'; the others concern
  cotangent complexes or differentials. None states this support/site comparison.
* Loogle: "CochainComplex.mappingCone.homologySequenceδ_triangleh,
  DerivedCategory.triangleOfSESδ". Zero hits for this query.
* Mathlib grep: "support.*boundary|boundary.*support|support.*connecting".
  Zero hits through msearch.
* LeanSearch: "Cohomology of derived global sections of support triangle has
  boundary equal to differential of cocycle lift". Eight hits, including cone
  cocycle lifting and HomComplex cohomology classes. None includes this pro-etale
  sectionwise comparison.
* rg in WeilConjectures and Sheaf for supported boundary, direct-image sections,
  and the item's id found the etale supportedLocalizationBoundary, Kummer-class
  consumers, generic SupportLongExact and DerivedInjectiveBoundary, and ringed-space
  sections comparison modules. These use a different topology/category or supply
  tools, rather than this normalization theorem. The exact item id has no upstream
  Lean hit. A name search in Mathlib, WeilConjectures, Sheaf and the upstream-name
  index found no existing declarations with the new full names.

Sources read: local Stacks etale-cohomology.tex, section-cohomology-support (09XP),
including the injective restriction row and support triangle; derived.tex,
section-canonical-delta-functor (014Z), including the explicit -p composed with q⁻¹
and its functoriality. The cone convention agrees with the node. No statement
correction or STATEMENT-DISPUTED flag is required.

Validation: scompile.py compiled the final single module cleanly in both its sandbox
and library-path checks (27.2 s and 9.2 s), with no error or warning. The prescribed
deliver2.py --no-push dry run passed: commit 9f25f899970 passed the server
preflight and compile. The packet changes only the item lean record, its module,
and this report; six theorem bodies are postponed and all fourteen declarations
are recorded.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
