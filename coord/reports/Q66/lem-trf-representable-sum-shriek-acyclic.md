## Worker report

The delivery states `lem-trf-representable-sum-shriek-acyclic` in
`Sheaf.CategoryTheory.DerivedCategory.RepresentableSumShriekAcyclic`.
Every theorem has proof `sorry`. The only helper definition,
`CategoryTheory.representableModule_resolutionAugmentation`, constructs the actual
sum augmentation by coproduct descent, functorial images of the supplied maps,
the standard single-complex comparison, and the degree-zero coproduct inclusions.
The three additive instances extract proofs from the named additive theorem;
they introduce no new categorical objects or maps. All thirteen declarations
are listed in `lean.declarations`. No new nodes or dependency repairs are needed.
The item's node changes only in `lean`; its reviewed statement and proof are unchanged.

### Hypotheses and clauses

* Fixed size convention, small E and D, arbitrary commutative R: explicit
  `universe u wE wD wR`, `(E : Type u) [SmallCategory E]`,
  `(D : Type u) [SmallCategory D]`, `(R : Type u) [CommRing R]`.
  The sites, arrows, coefficients and all sum indices are small in one chosen
  bound `u`; the module and presheaf categories themselves have objects in
  `Type (u+1)` and homs in `Type u`. Derived hom universes `wE`, `wD`, `wR`
  are separate, with explicit `HasDerivedCategory` hypotheses. No equality
  between category-object and category-morphism universes is imposed on the
  module/presheaf/derived categories. A larger common bound accommodates the
  original small categories and rings, exactly as the node's size convention does.
* The category A is literally `Eᵒᵖ ⥤ ModuleCat.{u} R`, as in the node.
  Identity coverings generate `⊥ : GrothendieckTopology E`.
  Mathlib's `Presheaf.isSheaf_bot` and `sheafBotEquivalence` supply its automatic
  sheaf condition and its identification with module-valued sheaves on that
  topology. The ringed-site category is the existing `ringedSiteModules`
  (a transparent abbreviation for `SheafOfModules`); there is no second
  presheaf/sheaf definition. The module docstring explains this choice of the
  presheaf presentation. In the constant-ring case, fixed-ring-linear natural
  maps and semilinear module-sheaf maps are exactly the same data.
* `L_U(M)(V) = ⊕_(V → U) M`: the existing
  `evaluationLeftAdjoint (ModuleCat.{u} R) (op U)` has object at `V : Eᵒᵖ`
  equal by definition to `∐ fun _ : op U ⟶ V ↦ M`.
  The opposite-category hom is precisely `V.unop ⟶ U`.
  Categorical coproducts of modules are the finite-support direct sums;
  `ModuleCat.finsuppCocone` and `finsuppCoconeIsColimit` give this concrete
  model for each copower. Nothing is redefined.
* Restriction `(a,m) ↦ (ab,m)` is the first conjunct of
  `representableModule_formulas`: after precomposing with the coprojection
  for `a`, restriction along `b` is the coprojection for `a ≫ b` in Eᵒᵖ.
  On unop arrows this is exactly the node's composite in E.
* The natural Hom bijection is the existing
  `(evaluationAdjunctionRight (ModuleCat R) (op U)).homEquiv M H`.
  It is an adjunction, so its two naturality laws and inverse laws are already
  part of its data, not merely asserted setwise bijectivity. The second and
  third conjuncts of `representableModule_formulas` explicitly assert
  evaluation on the identity summand and the inverse formula
  `f ≫ H.map a` on every summand. These are exactly the two displayed
  formulas in the node.
* Exactness and projectivity of L_U are respectively the first and second
  conjuncts of `representableModule_exact_projective_generators`:
  `PreservesFiniteLimits`, `PreservesFiniteColimits`, and preservation of
  `CategoryTheory.Projective`. Additivity is separately provided by the
  named theorem `representableModule_additive`. In abelian categories this
  is exactly exactness. `Projective` is Mathlib's lifting-across-every-epi
  class, whose full signature was read; no weaker projectivity is used.
* Enough projectives in Mod_R and A are the next two conjuncts of
  `representableModule_exact_projective_generators`, using the existing
  `EnoughProjectives` class.
* For each H the next conjunct asserts projectivity of the precise coproduct
  indexed by `p : Σ U : E, H.obj (op U)`, and `Epi` of its explicit map.
  Its summand is the inverse evaluation-adjunction image of
  `ModuleCat.ofHom (LinearMap.toSpanSingleton R (H.obj (op p.1)) p.2)`.
  This coefficient map sends r to r • x; the inverse adjunction restricts it
  along a, hence gives exactly r • H(a)(x). The specified epimorphism is
  therefore not replaced by an unspecified projective presentation.
* Projectivity of arbitrary small sums in both categories is the last two
  conjuncts of the same theorem, with `I : Type u` and no nonemptiness or
  finiteness assumption. Exactness of small sums in both categories is
  `modulePresheaf_smallSums_exact`: any family of short complexes whose
  component sequences are short exact has short exact coproduct sequence.
  `Discrete I` encodes the arbitrary family; its colimit is its coproduct.
* Any functor u:E→D is `(u : E ⥤ D)` without continuity, faithfulness,
  fullness, injectivity or exactness assumptions. Its left adjoint to
  precomposition is the existing `u.op.lan`; its unit is the actual
  `(u.op.lanAdjunction (ModuleCat R)).unit`.
* C_E and C_D are the existing `colim` functors over Eᵒᵖ and Dᵒᵖ, respectively.
* `representableModule_colim_lan` gives natural isomorphisms of functors
  `L_U ⋙ colim ≅ 𝟭` and `L_U ⋙ u.op.lan ≅ L_(uU)`.
  The first iso sends each generator identically to its coefficient; the
  second is normalized after the actual Kan unit by sending a to u(a) and
  acting identically on its coefficient. They are natural isomorphisms in
  the coefficient module, not pointwise arbitrary isos. The normalization
  uniquely fixes them and also forces compatibility with morphisms of U.
* Total derived functors and their canonical comparisons: each acyclicity
  theorem binds the relevant derived functor and a transformation
  `ε : DerivedCategory.Q ⋙ L ⟶ V.mapHomologicalComplex _ ⋙ DerivedCategory.Q`.
  `hLC` or `hLK` is the existing `Functor.IsLeftDerivedFunctor ε (quasiIso ...)`.
  `hdefined` also retains the Stacks requirement of being defined at EVERY
  homotopy complex: the denominator diagram of all quasi-isomorphisms into X
  is `IsEssentiallyConstantProDiagram` with some value Y. This is the body
  of the recorded `Functor.IsTriangulatedLeftDerivedDefinedAt` and matches
  the already recorded bounded-above computation theorem's interface. It
  is not silently replaced by existence of a Kan-extension counit alone.
* T is the actual coproduct `∐ fun c : I ↦ L_(U c)(M c)` with arbitrary
  `M : I → ModuleCat R`. `representableModule_sum_colim_acyclic` and
  `representableModule_sum_lan_acyclic` assert `IsIso (ε.app (T[0]))` for the
  two canonical comparisons. The latter also provides the coproduct
  identification of u_!T with `∐ c, L_(u(U c))(M c)`, with its generator
  normalization after the Kan unit and the source coproduct inclusion.
* `representableModule_sum_lan_colim_acyclic` asserts
  `IsIso (ε.app ((u.op.lan.obj T)[0]))` for the target colimit functor.
  This keeps the actual Kan image as the object, rather than only an
  isomorphic unspecified sum. Only C_D's relevant derived hypotheses are
  needed in this clause; the other two clauses bind their own hypotheses.
  Together they state the node's assertions under its simultaneous hypotheses.
* Supplied coefficient resolutions are `P : I → CochainComplex (ModuleCat R) ℤ`,
  their actual augmentations are `a c : P c ⟶ (M c)[0]`, and the three
  hypotheses of `representableModule_sum_resolution` are exactly
  `(P c).IsStrictlyLE 0`, projectivity in EVERY integer degree, and
  `QuasiIso (a c)`. No resolution is chosen in the definition.
* The resolution conclusion gives upper bound zero, projectivity in every
  degree, and `QuasiIso` of `representableModule_resolutionAugmentation`.
  Its source is the coproduct in cochain complexes of the degreewise L_U
  images. Pointwise colimits make this literally the sum prescribed in the node.
* The next two conjuncts say the actual colimit and Kan images of this
  augmentation are quasi-isomorphisms. The final two conjuncts give
  generator-normalized target isos to `∐ M` and `∐ c, L_(u(U c))(M c)` and,
  more explicitly, `QuasiIso` of the mapped augmentation followed by the
  standard `singleMapHomologicalComplex` comparison and the degree-zero
  image of those target isos. Thus the maps to the exact two complexes
  in degree zero in the node are stated, not only bare isomorphism existence.

### Dependencies read and used

* `def-weil-size-convention`: its `lean.convention` record has no declaration;
  rendered by the explicit universe binders above.
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, read in full; it is `SheafOfModules`
  on an arbitrary ringed site. This is the identity-topology interpretation
  in the module docstring, not a replacement definition.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, read in full. Its site
  and sheaf imports supply the background identity-covering topology.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` and `Qh`,
  with their full signatures, localization and size convention read.
* `Mathlib.CategoryTheory.Limits.HasLimits`:
  `CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit`, `colimit.desc`,
  and `colim`; these are the chosen colimits, functor and universal maps.
* `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`:
  `Functor.IsTriangulatedLeftDerivedValue` and
  `Functor.IsTriangulatedLeftDerivedDefinedAt`, read with their complete
  triangulated, shift, saturation and denominator-diagram signatures.
  The essentially-constant condition is expanded in exactly the form used
  by the already recorded computation dependency.
* Proof-only `Mathlib.Algebra.DirectSum.Module`: the recorded
  `DirectSum`, module structure, inclusions and finite-support universal maps.
  Read the module and its categorical copower realization in
  `Mathlib.Algebra.Category.ModuleCat.Colimits`.
* Proof-only
  `Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation`:
  `exists_boundedAbove_projective_resolution` and
  `boundedAbove_acyclic_leftDerived_computation`; read their full signatures
  and natural-language proofs. The two statements give exactly bound zero
  resolutions and canonical comparison computation used in proof steps 9--10.

Additional Mathlib constructions used directly: `evaluationLeftAdjoint`,
`evaluationAdjunctionRight` (full source read); `Functor.lan`, `lanAdjunction`
(full source and unit read); `Projective`, `EnoughProjectives` (definitions read);
`ShortComplex.ShortExact`; and `HomologicalComplex.singleMapHomologicalComplex`.
All imports of the node's statement dependencies are public, all proof-only
imports are plain imports. No new dependency has been introduced.

### Searches

All launcher searches were run under group Q66 and this item.

* `msearch.py ... leanfinder "Representable module presheaf with arbitrary coefficients evaluation adjunction exact projective colimit left Kan extension acyclic"`:
  eight hits, including `PresheafOfModules.freeYoneda`, `freeAdjunction`,
  `freeYonedaEquiv`, and projectivity via preadditive coyoneda. These do
  not give the combined arbitrary-coefficient acyclicity statement.
* `msearch.py ... loogle "CategoryTheory.Functor.freeYoneda, CategoryTheory.Projective"`:
  rejected unknown `CategoryTheory.Functor.freeYoneda`, not evidence of absence.
* Qualified retry `msearch.py ... loogle "CategoryTheory.evaluationLeftAdjoint"`:
  seven hits, including the exact existing copower construction and its
  adjunction, object, restriction, coefficient-map and unit formulas.
  The delivery uses those constructions rather than defining L_U again.
* `msearch.py ... grep "freeYoneda|copower|leftKanExtension" CategoryTheory`:
  25 reported hits, chiefly generic derived/Kan extension infrastructure;
  no theorem combines the node's claims.
* `msearch.py ... leansearch "The left adjoint of evaluation on module presheaves is exact and sums of representables with arbitrary coefficients are left Kan extension acyclic"`:
  eight hits, chiefly free-presheaf adjunction and pointwise limit/colimit
  lemmas, not the node's statement.
* Local `rg` in the full read-only `lean/WeilConjectures` and `lean/Sheaf`
  for `representableSum|representable_sum|leftKan.*[Aa]cyclic|inducedPresheaf|representable-sum-shriek-acyclic`:
  no exact match. A further search for
  `evaluationLeftAdjoint|representable.*acyclic|sum.*shriek` found tower
  generator applications and generic bar-complex commentary; these are
  not the arbitrary-small-category, arbitrary-coefficient statement here.
* The upstream blueprint-id search
  `rg -n 'representable-sum-shriek-acyclic' lean/WeilConjectures` found no
  recorded statement. The upstream name index search likewise found none
  of the new names. All searches remained in the prescribed source trees.
* Read Mathlib `CategoryTheory/Adjunction/Evaluation.lean`,
  `CategoryTheory/Generator/Presheaf.lean`,
  `Algebra/Category/ModuleCat/Presheaf/Generator.lean`, and Kan adjunction
  sources. `Presheaf.freeYoneda` is an alternate existing object-level
  copower; the functorial `evaluationLeftAdjoint` is used throughout this
  delivery, so the two interfaces are not confused.

Source verification: read the node's ten proof steps and
`literature/stacks-project/sites-cohomology.tex`, Example
`example-left-derived-colimits` (Tag 08PG), including the simplicial
contraction and the subsequent arbitrary functor example. The node's
reviewed projective-resolution refinement is unchanged. There is no item
repair note in the read clone. The withdrawn CompactObject example was
checked against its current node record and the upstream replacement module;
this delivery follows the required module-mode/public-section conventions.

### Edge cases and validation

Checked before writing and again against the elaborated statement:

* E empty: no U is required globally, the generator index is empty and H
  is the unique zero presheaf. Enough projectives and the resolution clauses
  still make sense; no inhabitant is chosen.
* I empty, including E empty: all sums and the augmentation are the zero
  complex. All three acyclicity statements retain this case.
* R the zero ring, M_c zero, and modules not projective (e.g. Z/2 as a
  Z-module): no nonzero or projectivity assumption on M_c occurs. Only
  the supplied resolution TERMS are assumed projective.
* Repeated U_c, arrows with nontrivial endomorphisms, and nonfaithful u:
  coproduct indices are arrows, never their images or isomorphism classes;
  u may identify arrows and the Kan normalization still uses `u.op.map`.
* E and D terminal and u the identity: L_U and the two ordinary functors
  reduce to the expected coefficient-preserving functors, and the
  resolution assertion reduces to exactness of sums of resolutions.
* Integer degree zero and all positive degrees: bound is explicitly zero;
  projectivity and quasi-isomorphism conditions do not omit degree zero.
* The canonical derived comparisons are the bound natural transformations
  with the derived universal property and every-object essential-constancy
  condition. They are not arbitrary maps with an assumed invertibility.

Every compile used only `scompile.py Q66 lem-trf-representable-sum-shriek-acyclic`.
The final module compiled in sandbox and declared-module modes, with no errors
or warnings apart from the permitted `sorry` notices. A field-notation issue
on a coproduct of cochain complexes was repaired by writing the existing
`CochainComplex.IsStrictlyLE` predicate explicitly; this changes no mathematics.
No test, local build, shared file edit or Git mutation was run in the read clone.
No `STATEMENT-DISPUTED` flag or statement correction is needed.

## Second reading by Q66

I reopened the node and completed a separate clause-by-clause rereading of the
finished file. The dispatcher forbids starting other agents, so this is the
worker's second pass; the maintainer's independent review remains independent.

The source category is Eᵒᵖ throughout. In particular the indices `op U ⟶ V`,
the restriction composite `a ≫ b`, and `u.op.map a` have the correct variance.
The epi really has the node's `(U,x)` indices and scalar-evaluation formula.
Exact sums and projective sums are each stated for modules AND presheaves.
The three acyclicity claims apply to arbitrary modules and use the canonical
counit on the degree-zero complex of the actual relevant object. The third
claim retains `u_!T`, not just its representable-sum model. All three contain
the stronger Stacks defined-at-every-object hypothesis in addition to the
universal counit. No finite, nonempty, exact-u or projective-coefficient
assumption was introduced.

This rereading strengthened the explicitness of the resolution output: I
replaced bare target-iso existence with generator-normalized isomorphisms and
quasi-isomorphisms of the actual mapped augmentation followed by the standard
single-complex comparison to the exact two stated targets. I recompiled the
whole module after that change. The degree bound, projective-term hypothesis,
augmentation formula, empty family and identity cases all agree with the node.
