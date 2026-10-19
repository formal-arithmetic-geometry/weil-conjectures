## Worker report

The module `Sheaf.Paper.IsomorphismDerivedPullback` states the finite and integral cases of
`lem-weil-isomorphism-derived-pullback`. Its main statements are
`WeilConjectures.isomorphismFiniteDerivedPullback_termwise` and
`WeilConjectures.isomorphismIntegralDerivedPullback_termwise`. Every theorem proof is `sorry`.
The auxiliary definitions supply the coefficient-normalized termwise inverse image needed to
state the comparison. They belong to the inverse-image notion already named in this node;
there is no new independent mathematical notion, dependency repair, or statement correction.

Clause-by-clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`, a module variable explicitly bound in every declaration
  that uses it. The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The ring of integers, chosen uniformizer, and positive quotients
  are exactly `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. No replacement coefficient datum is introduced.
- The isomorphism of schemes is `{X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]`. Invertibility of ell
  is expressed on both schemes by `[∀ x : X, Invertible (l : X.residueField x)]` and the analogous
  binder for Y. This is the same scheme-theoretic invertibility condition used by the recorded
  constructible integral operations. No nonempty, finite-type, base-field, or properness
  restriction is added.
- The two allowed coefficient cases are separate universal statements. The finite theorem's
  `(n : ℕ)` represents exponent `n + 1`, and includes every exponent at least one. Its coefficient
  sheaf is `proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))`; the integral
  theorem uses `completedIntegralCommRingSheafUnrestricted l E Y`, whose underlying ring sheaf
  is the existing limit `completedIntegralCoefficientSheafUnrestricted l E Y`. The same formulas
  are used on X. In particular integral coefficients are the completed sheaf, not a constant
  sheaf with discrete O_E values.
- Finite c_Lambda is `proEtaleIsoConstantRingComparison`, whose hom is exactly
  `proEtaleCoefficientInverseImageMap`. Integral c_Lambda is
  `isomorphismCompletedCoefficientComparison`. Its existence-and-uniqueness statement requires
  for every n the equality `c.hom ≫ π_n,X = g⁻¹(π_n,Y) ≫ c_A_n`. These equations uniquely
  determine the isomorphism, and characterize precisely the source's composite of the canonical
  limit comparison and the limit of the constant-ring comparisons. Choosing this unique datum
  does not choose an arbitrary comparison from a mere existence assertion.
- The termwise inverse image uses the existing `proEtaleModuleInverseImage`, followed by
  `SheafOfModules.restrictScalars` along the forgotten ring map `c.inv`. Thus the scalar action
  is transported along the actual specified coefficient identification. The helper
  `isomorphismTermwiseModuleInverseImage_exact` supplies additive and exact structure; the
  instance definitions extract its proof fields. They have no postponed data.
- For an arbitrary complex K, its class is `DerivedCategory.Q.obj K`. The named finite and
  integral termwise functors use `Functor.mapDerivedCategory` of the above module functor.
  Mathlib's `mapDerivedCategoryFactors` identifies their values on Q(K), naturally, with
  `Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)`. Therefore the right side is exactly the
  termwise inverse image, including differentials and chain maps, and no representative or
  K-flatness restriction is imposed on K.
- Membership in D^b_c(Y,A) is exactly `intrinsicFiniteTorsionConstructible`, and membership in
  D^b_c(Y,O_E) is exactly `sfIntegralConstructible`. The preservation witnesses `h` in the two
  main theorems quantify over every ambient object satisfying these predicates; at finite level
  h records both pullback and termwise membership, as required to type the isomorphism in the
  full target category. Integral membership retains derived completeness and the one common
  cohomological interval for all reductions. No boundedness condition is substituted.
- `Lg*` is the existing `finiteDerivedPullback l E n g` or
  `constructibleIntegralPullback l E g`, respectively, from the recorded derived-operations
  module. The latter is the constructible restriction of `integralDerivedPullback`, which is
  the normalized descent of the specified strict finite-reduction Roos construction.
- The natural lambda is a `Nonempty (F ≅ G)` between functors on the full source constructible
  subcategory, with both functors landing in the full target constructible subcategory via
  `ObjectProperty.lift`. Thus naturality covers all derived morphisms, not just chain maps or
  an objectwise list of unrelated isomorphisms. No lambda is defined by arbitrary choice.
- The last conjunct in each theorem is the asserted degree-zero specialization, using the
  existing `finiteConstantCoefficientObject` and `integralConstantCoefficientObject`. These
  are the regular coefficient module sheaves placed in degree zero by `singleFunctor _ 0`.
  Their node `lem-weil-constant-coefficient-objects-constructible`, previously a proof dependency,
  is added to stmt_deps because those existing objects now occur explicitly in the signature.

Recorded dependencies read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  reexporting the coefficient constructions of `CoefficientExtension` unchanged.
- `def-weil-scheme-morphism-properties` is a convention-only record. `Scheme`, `Scheme.residueField`
  and `IsIso` are the corresponding Mathlib declarations; there is no module to recreate.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm`: `integralConstantToCompletion`, reexporting
  `CompletedIntegralCoefficients` and its actual completed ring sheaf and finite projections.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `Scheme.sfIntrinsicConstantModuleAdjunction`, reexporting the original arbitrary-ring inverse
  image and the intrinsic finite operation. The scalar transport uses the reexported
  `Scheme.proEtaleModuleInverseImage` rather than a private copy of its site construction.
- `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`:
  `Scheme.proEtaleIsoInverseImage_equivalence`, `proEtaleIso_constantComparison`,
  `proEtaleIso_inverseLimitComparison`, and `proEtaleIsoConstantRingComparison`. Their full
  signatures and docstrings were read, including the module-equivalence clauses.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, reexporting `integralDerivedPullback` from
  `IntegralDerivedOperations`. All three finite/integral definitions were read.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible`: the finite and integral coefficient
  objects and their membership statements. The irrelevant finite-field datum on its integral
  membership theorem is not added as a hypothesis here; the node's proof explains how to
  instantiate it with an independently chosen characteristic different from ell.

The proof dependencies are available through the public dependency closure and the explicit
private imports of K-flat resolutions, reduction-tower well-definedness, and finite-free completed
scalar comparison. The module docstrings give the finite proof steps and all integral steps:
projection compatibility, flat/K-flat transport, tower transitions, strict cone differential,
canonical eta for L=E, normalized descent, completeness, uniform amplitude and degree zero.
The generic exact-functor facts are Mathlib `Functor.homologyFunctorIso` and
`Functor.mapDerivedCategory`, whose defining signatures were inspected. No proof-only definition
was added to the statement.

Edge cases checked: the empty scheme is permitted; the zero complex has the same membership and
maps; finite index n=0 means the required smallest exponent one and never the zero coefficient
quotient at exponent zero; identity isomorphisms and arbitrary automorphisms are retained;
arbitrary cohomological shifts and representatives are permitted. The integral termwise functor
is defined on the ambient category but the completed-pullback comparison is only asserted on
D^b_c, so no false ambient idempotent-completion identification is asserted. The actual site
has object universe u+1 and morphism universe u throughout; module values are in u+1.

Existing-declaration searches:

- `msearch.py ... leansearch "Derived pullback along an isomorphism is naturally isomorphic to
  termwise inverse image on finite and completed integral constructible proetale sheaves"`:
  eight hits, headed by `ChosenPullbacksAlong.iso`, `.isoInv`, generic pushforward congruences,
  and identity module pullback isomorphisms. None states this result.
- `msearch.py ... leanfinder "Derived pullback along an isomorphism agrees with exact termwise
  inverse image"`: eight hits including `Functor.mapDerivedCategorySingleFunctor`, localization
  factorizations, and quasi-isomorphism inversion. These are generic tools, not a full match.
- `msearch.py ... loogle '"mapDerivedCategory"'`: twelve hits, including the exact derived
  functor, its identity/composition comparisons and its single-functor comparison. Those generic
  APIs are reused; none includes completed coefficients or constructibility transport.
- `msearch.py ... grep 'mapDerivedCategory|sheafCongr' Algebra/Homology/DerivedCategory` and direct
  rg in Mathlib's exact-derived-functor file: generic exact descent, no complete match.
- Direct `rg` in project `lean/Sheaf` and upstream `WeilConjectures` for isomorphism/derived,
  termwise/inverse-image and the new names; node-id search upstream returned no matching
  declaration. The nearby `IsomorphismDerivedPullbackEquivalence` concerns finite-level ambient
  equivalences, without integral coefficients, the termwise comparison or constructibility.
  `ProEtaleConstantExact.finiteCoefficientModulePullback` is a finite RingCat specialization;
  its existing construction was read. The shared helper here composes the existing commutative
  inverse-image module functor with scalar restriction for the completed comparison as well.
  No existing declaration gave that completed comparison or the entire node's conclusion.
- New full declaration names were also checked against `dag/lean_names_upstream.json` and both
  source trees; no collision was found.

Validation: `scompile.py Q115 lem-weil-isomorphism-derived-pullback <module>` passed for both the
sandbox name and actual library module name with no errors or warnings. All variables and
universes are explicit and `autoImplicit` is disabled. No statement is disputed.

## Second reading by Q115

I read the node copy, its source place in `def-weil-ordinary-compact-cohomology.md` (order 1510,
coefficient-object paragraph), and every recorded statement dependency.  The source paragraph
introduces the finite constant coefficient object and the completed integral coefficient object;
the node supplies the derived-to-termwise pullback comparison needed by the next canonical Weil
structure.  Its objects, hypotheses, and conclusion match the Lean as follows.

- The prime, finite extension, valuation ring, uniformizer, and positive quotient rings are
  `(l : ℕ) [Fact l.Prime]`, `E`, and `Padic.coefficientExtensionRing l E (n + 1)` in
  `isomorphismFiniteDerivedPullback_termwise`; the `n + 1` indexing covers exactly every
  `A_{E,m}` with `m ≥ 1`.  The integral theorem uses the recorded inverse-limit ring
  `completedIntegralCommRingSheafUnrestricted l E`.
- The schemes and isomorphism are `{X Y : Scheme.{u}}`, `(g : X ⟶ Y) [IsIso g]`.  Invertibility
  of `l` on both schemes is exactly the two instance binders
  `[∀ x : X, Invertible (l : X.residueField x)]` and the corresponding binder for `Y`.
  No finite-type, separatedness, properness, base-field, or nonemptiness hypothesis is added.
- The finite coefficient sheaves are `proEtaleConstantRing` and the structure map is the existing
  `proEtaleIsoConstantRingComparison`, whose hom is the canonical `c^g_A`.  The integral map is
  `isomorphismCompletedCoefficientComparison`; its projection equations are precisely
  `c.hom ≫ π_{n+1,X} = g⁻¹(π_{n+1,Y}) ≫ c^g_{A_{E,n+1}}`, so it is the stated inverse-limit
  composite rather than an arbitrary isomorphism.
- `isomorphismTermwiseModuleInverseImage` applies the recorded pro-etale inverse image to every
  term and transports the scalar action through the inverse of this structure map.  Its derived
  functors are `isomorphismFiniteTermwiseInverseImage` and
  `isomorphismIntegralTermwiseInverseImage`.
- For every ambient complex satisfying the source constructibility predicate, the finite theorem
  provides membership of both the recorded `finiteDerivedPullback` and the termwise inverse image
  in the target `intrinsicFiniteTorsionConstructible` property.  The integral theorem gives the
  same for `sfIntegralConstructible`, including derived completeness and one common interval for
  all positive reductions.
- The `Nonempty` isomorphisms between the lifted full subcategory functors are exactly natural
  isomorphisms in `K`; the final `Nonempty` conjuncts specialize them to the finite and completed
  coefficient objects in degree zero.  Thus they render the node's `λ_K : Lg^*K ≅ g⁻¹K` and
  `λ_{Λ_Y}` clauses without choosing a noncanonical map.

Edge cases checked: `n = 0` denotes exponent one and never a zero quotient; identity and arbitrary
scheme automorphisms retain the same canonical comparison; empty schemes and zero complexes are
allowed by the object-property predicates; arbitrary cohomological shifts remain in the ambient
derived category; no characteristic or universe equality is imposed (site values are in `u+1` and
site morphisms in `u`).

For an independent existing-declaration check I reran `msearch.py` with LeanFinder for
“derived pullback inverse image isomorphism constructible sheaf”, and inspected the hits for
`SheafOfModules.pullbackIso`, `Functor.mapDerivedCategory`, and the project’s
`finiteTorsionDerivedPullback`.  I also searched `lean/Sheaf`, the upstream source tree, and
`dag/lean_names_upstream.json` for `isomorphismDerivedPullback`, `termwiseInverseImage`, and the
node id.  These are generic pullback/equivalence declarations or the finite ambient equivalence;
none states the completed-coefficient comparison, the constructibility transport, and the
degree-zero specializations together.  The worker module therefore remains the single declaration
for this node.

No mismatch was found, so no Lean statement or dependency record was changed in this second
reading.  The module was compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q115 lem-weil-isomorphism-derived-pullback
lean/Sheaf/Paper/IsomorphismDerivedPullback.lean`; it completed without errors or warnings.
