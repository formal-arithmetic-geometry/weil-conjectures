## Worker report

The module `Sheaf.Algebra.Homology.BimoduleChainCurryingDescent` states
`ModuleCat.BimoduleChainCurrying.bimodule_chain_currying_descent` with one `sorry`.
All fourteen helpers have real data and merely name the existing complexes, restriction,
coinduction presentation, total-tensor inclusions, evaluations, and derived triples.
There are no new DAG nodes, dependency repairs, or statement corrections.

Hypotheses and clauses, read against the unchanged DAG statement:

- The commutative rings are `{S B : Type u} [CommRing S] [CommRing B]` and the
  homomorphism is `(φ : S →+* B)`. `U φ` is Mathlib restriction applied termwise.
  `Complex R` abbreviates `CochainComplex (ModuleCat.{u} R) ℤ`. All complexes are
  arbitrary, and there are no flatness, finiteness or boundedness assumptions.
- The chosen derived morphism universes are independent `wS` and `wB`, with
  `HasDerivedCategory.{wS} (ModuleCat.{u} S)` and its B analogue. These are exactly
  the size choices in def-weil-abstract-derived-category, not equalities of universes.
  All variables and universes are explicit, and `autoImplicit` is disabled.
- Product total Hom is the recorded `CochainComplex.moduleHomComplex`. Its degree-n
  carrier is `HomComplex.Cochain`, the product over `Triplet n`, with differential
  `HomComplex.δ_hom`. `total A T` is the recorded `CochainComplex.mapBifunctor`
  specialized to the ordinary module tensor. Its source is a direct sum over p+q.
- `J φ T N` uses the concrete equivalent presentation
  `moduleHomComplex T ((coinductionComplexFunctor φ).obj N)`. This is not a second
  unspecified B-action on S-Hom. The theorem supplies `eJ T N : U J ≅ Hom_S(UT,N)`;
  its first clause pins every coordinate to `valueJ`, namely evaluation at one
  using the existing `coinductionEvaluation`. The second clause states
  `valueJ (b • z) t = valueJ z (b • t)`. Thus this presentation is exactly J in
  the node, with its prescribed precomposition action, not ordinary Hom_B(T,N)
  or an assumption that N has a B-action. Evaluation at one has the unique inverse
  h ↦ (t ↦ (b ↦ h(bt))), so the B-object is fully determined by the formulas.
- The witnesses `θ A T N : left φ A T N ≅ right φ A T N` are isomorphisms of entire
  S-module complexes. The third and fourth clauses pin the hom and inverse to
  `valueRight (θ.hom z) a t = valueLeft z a t` and
  `valueLeft (θ.inv z) a t = valueRight z a t`, in every n,p,q,r with p+q+n=r.
  `pure` uses the canonical total-tensor inclusion. Consequently the formulas
  respect the tensor balancing relations by their types and the precomposition
  B-action; they are not bijections on only cycles or degree-zero cohomology.
  Products have no support condition; only the total tensor uses direct sums.
- The fifth clause evaluates `d (θ.hom z)` on a pure tensor. The sixth evaluates
  `d z` on the left (equivalently θ(dz) by the forward clause). Both give exactly
  `N.d (...) (valueLeft z a t) - (p+n).negOnePow • valueLeft z a (T.d ... t)
  - n.negOnePow • valueLeft z (A.d ... a) t`. Integer `negOnePow` gives (-1)^n
  for all integers, including negative ones. The inner Hom degree is p+n.
- In the seventh clause, arbitrary chain maps α:A'→A, β:T'→T, γ:N→N' give
  maps `l` and `r`. Their all-coordinate formulas are respectively
  γ(f(α a')(β t')) and γ(g(α a' tensor β t')). These determine the two maps
  uniquely: eJ is an isomorphism, cochains are products, and pure tensors generate
  every direct-sum summand. The equation `l ≫ θ'.hom = θ.hom ≫ r` is the stated
  square, with no change of variance. Specifying formulas rather than selecting
  arbitrary maps is essential here.
- Still in that clause, `kFlat T → kFlat T' → N.IsKInjective → N'.IsKInjective →
  QuasiIso α → QuasiIso β → QuasiIso γ → QuasiIso l ∧ QuasiIso r` is exactly
  the conditional quasi-isomorphism assertion. Neither A nor A' is assumed
  K-flat, and K-injectivity is imposed only over S. The `kFlat` helper is exactly
  the recorded `MorphismProperty.kFlat` specialized to module-complex quasi-isos.
- The derived domain `DerivedTriple S B` is `(D(B)ᵒᵖ × D(B)ᵒᵖ) × D(S)`.
  The witnesses `F,G` are descents of the *specified chain-model functors*:
  `eL` and `eR` compare their values with Q(left) and Q(right) on EVERY A,
  EVERY K-flat T and EVERY S-K-injective N. Their two map equations in the
  seventh clause hold for EVERY chain map between such triples. Thus the
  witnesses are not unconstrained functors with selected object values.
  These are the localization model identifications: the right is the model
  of RHom_S(U(A tensor^L T),N); the left is U RHom_B(A,J), since J is
  B-K-injective on these models. The theorem's docstring gives these identifications
  in steps 7 and 11, following the node's proof.
- `η : F ≅ G` is a natural isomorphism on the full derived product category;
  its type includes the commuting square for EVERY derived morphism. The eighth
  clause pins its components by `eL.hom ≫ η.hom = Q.map θ.hom ≫ eR.hom`.
  The final clause states that it is the unique natural isomorphism with this
  normalization. This is the localization universal-property formulation of
  independence of resolved representatives. Map compatibility holds for arbitrary
  chain maps, not merely quasi-isomorphisms. For quasi-isomorphisms the seventh
  clause makes both vertical maps invertible after Q; the natural square then
  also commutes for their inverses. Functoriality gives all localized composites.
  Changing the representative of any of the three derived objects is covered by
  these same comparisons and the naturality of η.
- There is no assertion or hypothesis that restriction preserves K-injectives.
  All objects and maps in the main chain assertion remain S-module complexes.

Dependency declarations read and used:

- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` (localization at
  `HomologicalComplex.quasiIso`).
- def-sc-module-total-hom-complex:
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex`, using Mathlib `HomComplex.Cochain` and `δ_hom`.
- def-pc-tensor-complex-sheaves: `Mathlib.Algebra.Homology.BifunctorShift`,
  `CochainComplex.mapBifunctor`, `CochainComplex.ιMapBifunctor`, with
  `CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat B)`. This is the node's
  ordinary-module specialization, with sign (-1)^p on the second differential.
- def-pc-module-kflat-complex:
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`,
  `CategoryTheory.MorphismProperty.kFlat`; the public import of
  `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` also gives its
  cochain specialization `CochainComplex.kFlat_iff_preservesQuasiIso`.
- def-pur-kinjective-complex: its existing Mathlib match
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
  `CochainComplex.IsKInjective` (every map from an acyclic complex is null-homotopic).
- Gained existing statement dependency def-trf-derived-coinduction: its recorded
  module `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction` and helpers
  `ModuleCat.coinductionComplexFunctor` and `ModuleCat.coinductionEvaluation`.
  The helpers construct ordinary coinduction and evaluation at one directly from
  the ordinary restriction/coextension adjunction. They do not use the theorem
  `derivedCoinductionAdjunction_spec`. No downstream bimodule tensor-Hom theorem
  is imported, used as an assumption, or chosen to construct a map.

Every available proof-dependency module is also imported plainly: KFlatTensorQuasiIso,
QuasiIsoHomComplexMap, HomComplexGlobalHomotopyOfUniverses, the upstream homotopy
monoidal module, EquivariantHomResolutionCalculus, SiteDerivedTensorDescentIndependentCoefficients,
Mathlib DerivedCategory.KInjective, RingedSiteKInjectiveResolutionsOfUniverses,
KFlatResolutionIndependentCoefficients, Mathlib Localization.Predicate, and
OrdinaryModuleDerivedInternalHom. The eleven-step proof docstring records their
roles, including the one-object-site specializations, signed flip, homotopy formulas,
resolving categories, universal-property descent, and canonical model identification.

Edge cases checked before finalizing:

- S=B and φ=id recovers the ordinary unbounded tensor-Hom currying formula.
- Zero ring and zero A,T,N give zero objects on both sides, with no nonzero or
  nontriviality assumptions. Zero comparison maps are allowed when not q-isos.
- A,T unbounded in both directions: the coordinates are products over every
  integer pair; no tensor/product interchange or finite cochain support is used.
- p=0,n=0 gives d_N f(a)(t)-f(a)(d_Tt)-f(d_Aa)(t). Negative p,n are handled by
  integer signs. The exponent on the inner differential is p+n, not q+n.
- Nonflat S→B, for example Z→Z/2, is allowed: only T,T' are required K-flat
  over B in the conditional comparison clause. N,N' are S-K-injective there.
- Identity comparison maps, arbitrary noninvertible maps, quasi-isomorphisms and
  their inverses are covered; no invertibility of α,β,γ is required for the
  original chain square or for model-comparison naturality.
- Different chosen localization morphism universes wS,wB remain independent.

Existing-declaration searches (2026-10-24):

- msearch.py leanfinder, query `Mixed ring total complexes tensor Hom currying
  natural chain isomorphism`: eight hits, including `HomologicalComplex₂.totalFlipIsoX`,
  `HomologicalComplex.mapBifunctorFlipIso` and `HomologicalComplex.HasGoodTensor₁₂`.
  These concern flip/reindexing and tensor associativity, not mixed-ring currying.
- msearch.py loogle, query `ModuleCat.monoidalClosedHomEquiv`: one exact name hit.
  Read `Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean`: this is the
  ordinary, one-ring module tensor-Hom equivalence, not the requested chain and
  resolving-descent statement. An earlier comma-separated names query returned
  no hits (`unknown identifier HomComplex.Cochain`); the valid query above replaces it.
- msearch.py grep, query `tensorHom|currying|curry`, subdirectory `Algebra/Homology`:
  five hits in Monoidal.lean. Its tensorHom tensors chain maps; it does not curry Hom.
- Direct rg of `bimodule`, `mixed.*Hom`, `currying`, `moduleHomComplex` in the
  upstream and Sheaf homology directories found HomTensorTotal (one-ring sheaf
  version), AlgebraicShriekDerivedHomAdjunction (coinduction evaluation comparison),
  DerivedBimoduleTensorHom (the parent derived statement), and KFlatRHomCurrying
  (one-ring ringed-site version). Read their relevant signatures and normalization
  docstrings. None gives this entire mixed-ring chain isomorphism, signed formulas,
  all-map comparison squares and descent package. The parent does not supply a
  chain currying isomorphism as a declaration, and is not imported as a shortcut.
- Direct rg for `lem-trf-bimodule-chain-currying-descent` in both Lean roots and
  for `BimoduleChainCurrying`/`bimoduleChainCurrying` found no existing declaration.
  Mathlib's underlying HomComplex and ModuleCat closed signatures were read.

Source check: read the full differential-graded clause and omitted-proof hint of
Stacks dga.tex, lemma-tensor-hom-adjunction (09LN), and the current
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`
local-term-locality statement and unit. This delivery preserves the node and unit
statements and the accepted proof split. No STATEMENT-DISPUTED finding remains.

Validation: scompile.py compiles both the isolated sandbox module and its library
module name cleanly (3.4s and 2.9s). There is one postponed theorem, with its full
source and eleven-step proof in the docstring. There are no other postponed proofs.

## Second reading by Q19

This is the dispatcher's single-worker second pass; the independent review is
performed by the maintainer as specified in the assignment. I reopened the node and
the final module and matched the clauses above. In particular I checked that J is
normalized by evaluation at one and its B-action, θ is an S-complex isomorphism,
θ.inv has its own formula, both signs use p+n and n, all integer pairs are allowed,
A is not required K-flat, the q-iso conclusion requires both K-flat T's and only
S-K-injectivity, model comparisons apply to arbitrary chain maps, and η is on the
full derived product category. The only draft correction was parenthesizing the
isomorphism types after the proof-valued arrows in eL/eR. No mathematical statement
changed. All helpers are public and have the owning node's source/blueprint docstring.
