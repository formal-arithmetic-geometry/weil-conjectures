## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes` states
`AlgebraicGeometry.Scheme.Modules.coherent_property_devissage_integral_subschemes` with
one `sorry`; it defines no new notion and proves nothing. The full nine-step natural-language
proof from the node is carried in the declaration docstring. Only `lean` changes in the node.

Clause correspondence:

- X is a scheme: `(X : Scheme.{u})`. Noetherian means exactly
  `[IsLocallyNoetherian X] [CompactSpace X]`; the latter is quasi-compactness of X.
- A property of coherent O_X-modules is `(P : X.Modules → Prop)`, with every use restricted
  to coherent modules by `RingedSpace.IsCoherent X.toRingedSpace`. Allowing P on all modules
  introduces no condition on its values at incoherent modules.
- (0): `hP_zero : P (0 : X.Modules)` uses the category's zero object.
- (1): `hP_ext` quantifies over `S : ShortComplex X.Modules`, assumes `S.ShortExact` and
  coherence of each of `S.X₁`, `S.X₂`, `S.X₃`, and takes `P S.X₁` and `P S.X₃` to `P S.X₂`.
- (2): `hP_sum` quantifies over F and r, assumes coherence and `1 ≤ r`, and takes
  `P (⨁ (fun _ : Fin r ↦ F))` to `P F`. The local finite-biproduct instance is supplied by
  `HasFiniteBiproducts.of_hasFiniteProducts`; it is a construction, not a new hypothesis.
- (3): `hP_integral` quantifies over every scheme Z, every `i : Z ⟶ X` with
  `[IsClosedImmersion i]`, `[IsIntegral Z]`, and every `ξ : X` with
  `closure ({ξ} : Set X) = Set.range i.base`. This is precisely the stated generic-point
  condition, without requiring an independently chosen generic point of Z.
- G is an existential `G : X.Modules`, with `RingedSpace.IsCoherent X.toRingedSpace G`.
- (3)(a): `{x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base` is exactly
  Supp(G) = i(Z), following the project's inline support convention.
- (3)(b): all `g : X.presheaf.stalk ξ` in `IsLocalRing.maximalIdeal _` annihilate every
  element m of `(RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G`. This is
  m_ξ G_ξ = 0, expressed elementwise, over the ambient local ring O_{X,ξ}.
- (3)(c): `(J : X.Modules)` and `(ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)` with
  `[Mono ι] [J.IsQuasicoherent]` represent an arbitrary quasi-coherent sheaf of ideals
  of O_X. This quantification has no ideal-sheaf choice or affine restriction.
  `Function.Surjective ((RingedSpace.moduleStalkFunctor ...).map ι).hom` says its stalk
  image is the full O_X stalk, hence J_ξ = O_{X,ξ}; the target is the unit module's
  stalk, canonically the same ring. Surjectivity avoids choosing an unnecessary stalk
  identification.
- `G' : Subobject G` is a submodule of G. Coherence is explicitly required.
  The map `h : (G' : X.Modules) ⟶ idealModuleProduct ι G` and equality
  `G'.arrow = h ≫ idealModuleProductι ι G` express G' ⊆ JG. The preexisting
  `Scheme.idealModuleProduct` is the image of the multiplication map J ⊗ G → G,
  built with the recorded tensor product and its left unitor. No product is redefined.
- Surjectivity of the stalk of `G'.arrow` expresses G'_ξ = G_ξ as submodules of G_ξ.
  Since G'.arrow is mono and stalks preserve monomorphisms, equality of its image to
  the full stalk is the stated equality, not an arbitrary abstract isomorphism.
  `P (G' : X.Modules)` gives the final clause (3)(c).
- Conclusion: `∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F`.

Subobject representatives cause no extra invariance assumption: (0) and (1) already force
P to be invariant under isomorphism among coherent modules, as step 3(a) of the node proves.
Therefore choosing a representative for a submodule neither strengthens nor weakens (3)(c).

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, its category and morphisms
  (def-pc-scheme).
- Mathlib.AlgebraicGeometry.Noetherian: `AlgebraicGeometry.IsLocallyNoetherian`;
  `CompactSpace X` is the scheme quasi-compactness convention (pqf-def-locnoeth and
  def-weil-pbc-scheme-conventions). `IsNoetherian` extends exactly these two classes.
- Sheaf.AlgebraicGeometry.Coherent: `AlgebraicGeometry.RingedSpace.IsCoherent`
  (pqf-def-coherent), using the same carrier as X.Modules.
- Mathlib.AlgebraicGeometry.Modules.Sheaf: `Scheme.Modules` and its Abelian, limits,
  and colimits instances (def-weil-sheaf-of-modules-category).
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct: `SheafOfModules.monoidalCategory`
  (def-pur-sheaf-tensor-product), through the ideal-module-product module.
- Sheaf.Algebra.Homology.ModuleStalkFunctor: `RingedSpace.moduleStalkFunctor`, the
  prescribed scheme/ringed-space specialization. Also read the currently recorded
  presheaf-level `PresheafOfModules.moduleStalkFunctor` in
  Sheaf.Topology.PresheafModuleStalkFunctor (def-weil-pbc-module-stalk); both use
  exactly Mathlib's stalk carrier and induced linear maps.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` were read (def-weil-residue-field). Only its maximal
  ideal notion, `IsLocalRing.maximalIdeal (X.presheaf.stalk ξ)`, is needed here.
- Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase was read
  (def-weil-pbc-closed-subset-proper-over-base); its support clause is the standing
  inline stalk locus, so no irrelevant proper-over-base hypothesis is imported.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `AlgebraicGeometry.IsClosedImmersion`
  and Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsIntegral`.
- Existing Sheaf.AlgebraicGeometry.IdealModuleProductStalk: `Scheme.idealModuleProduct`
  and `Scheme.idealModuleProductι`, already introduced by
  lem-weil-pbc-ideal-module-product-stalk, which is in this item's proof dependencies.
- Mathlib.Algebra.Homology.ShortComplex.ShortExact: `ShortComplex.ShortExact`.
  Mathlib.CategoryTheory.Preadditive.Biproducts supplies finite direct sums.

Edge cases checked: no Nonempty X hypothesis excludes the empty scheme; on an empty
scheme (3) has no witnesses and (0) supplies the zero-module case. Integral Z carries
nonemptiness intrinsically. The zero module conclusion is included and hP_zero prevents
the already recorded Stacks counterexample P = nonzero. r = 0 is excluded only in (2),
as the node requires, while r = 1 is included. J = O_X is allowed; J = 0 fails the full
stalk condition at a point. Maximal-ideal annihilation is over O_{X,ξ}, not O_{Z,η}.
The universe u is explicit and shared among all schemes, sheaves, rings and stalks;
no independent smaller testing universe or implicit binders occur.

Searches:

- msearch.py leanfinder: "A property of coherent sheaves on a Noetherian scheme closed
  under extensions and descent from finite nonempty direct sums holds for all coherent
  modules if it holds generically on integral closed subschemes". Eight hits, including
  SheafOfModules.IsFiniteType, IsLocallyNoetherian, IsNoetherian and affine-cover criteria;
  no devissage statement.
- msearch.py loogle: "AlgebraicGeometry.IsLocallyNoetherian, SheafOfModules". Zero hits.
- msearch.py grep: "devissage|coherent_property" in AlgebraicGeometry. Zero hits.
- rg on WeilConjectures: "lem-weil-pbc-coherent-property-devissage-integral-subschemes",
  "coherent_property_devissage", "devissage". Only unrelated prime-factor, étale, and
  curve devissage declarations; no exact statement. No exact upstream blueprint name
  found in dag/lean_names_upstream.json.
- rg on lean/Sheaf: "IsCoherent", "devissage", "property" and ideal/tensor product
  searches. Located Coherent, CoherentFiltrationIntegralSubschemes,
  CoherentGenericPointIdealInclusion, ModuleStalkFunctor and IdealModuleProductStalk;
  no declaration of this statement. Reused the existing product definitions.

Source: local coherent.tex is absent on this machine; read the primary Stacks pages
https://stacks.math.columbia.edu/tag/01YM and https://stacks.math.columbia.edu/tag/01YL.
The existing node intentionally adds (0), with its already documented source error;
this delivery preserves that node exactly. No statement correction or dispute is needed.

Validation: server scompile clean (2.2 seconds); no warnings or errors. Dry-run preflight
is the final check; the second reader will supply the independent reading and deliver.

## Second reading by C1

Independent reading of the node, the delivered Lean, and the Stacks source: downloaded
upstream coherent.tex into scratchpad/coherent.tex and read section-devissage,
lemma-property-higher-rank-cohomological (01YM), and its supporting 01YL argument.
The section assumes Noetherian X throughout, with no separatedness or field assumption.
The node already incorporates the reviewed stage-1 correction P(0), absent in Stacks;
I preserved it. Quasi-coherent subobjects of a coherent module are coherent on this X,
so the node's coherent G' agrees with the source's quasi-coherent G'. No new statement
correction, definition node, or dependency module is required in this delivery.

Object/hypothesis/conclusion checklist (each verdict: exact):

- X, a Noetherian scheme: `X : Scheme.{u}`, `[IsLocallyNoetherian X]`,
  `[CompactSpace X]`. Read Noetherian.lean: IsNoetherian extends precisely these two
  classes; its locally Noetherian class tests Noetherian rings on all affine opens.
- P, a property of coherent O_X-modules: `P : X.Modules → Prop`, with coherence
  restricting every relevant quantifier. Its values on incoherent modules are unused.
  Read Modules/Sheaf.lean: X.Modules is SheafOfModules over X.ringCatSheaf, with the
  same morphisms and abelian structure, not the category of quasi-coherent modules only.
- (0): `hP_zero : P (0 : X.Modules)`. Isomorphism invariance for coherent objects
  follows from (0),(1), so a chosen zero representative introduces no extra assumption.
- (1): `hP_ext`, for every `S : ShortComplex X.Modules` with `S.ShortExact`, coherence
  of all three terms, and `P S.X₁ → P S.X₃ → P S.X₂`. These are exactly the end terms
  and middle term of the node's short exact sequence.
- (2): `hP_sum`, every coherent F and `r : ℕ` with `1 ≤ r`, descends P from the
  biproduct of the constant family on Fin r to F. Universal implication for each r
  equals descent when some positive r has the property. The explicit
  `HasBiproduct.of_hasProduct` constructs the finite biproduct from existing products;
  it imposes no new instance hypothesis on X or P.
- (3): `hP_integral`, every `Z : Scheme.{u}`, `i : Z ⟶ X` with IsClosedImmersion i
  and IsIntegral Z, and every `ξ : X` with `closure {ξ} = Set.range i.base`.
  Read ClosedImmersion.lean (closed embedding and surjective stalk maps) and
  Properties.lean (nonempty and domain sections on nonempty opens). The closed
  embedding carries precisely the generic point of Z to this ξ.
- Existential coherent G: `∃ G : X.Modules, RingedSpace.IsCoherent ... G ∧ ...`.
  Read Coherent.lean: finite type and finite type kernels of all finite free maps
  on all opens; its scheme carrier is definitionally X.Modules.
- (3)(a): `{x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base`, exact
  nonzero-stalk support, matching the inline support convention read in
  ClosedSubsetProperOverBase.lean. No proper-over-base hypothesis is imported.
- (3)(b): all `g : X.presheaf.stalk ξ` in `IsLocalRing.maximalIdeal _` kill all
  `m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G`. The local ring
  is the ambient O_{X,ξ}, as in the node, not O_{Z,η} or its residue field.
- (3)(c), J: all `J : X.Modules`, `ι : J ⟶ SheafOfModules.unit X.ringCatSheaf`
  with `[Mono ι] [J.IsQuasicoherent]`. A submodule of the unit is exactly a sheaf
  of ideals of O_X; Mathlib's quasi-coherence notion is the one cited by Coherent.
  Stalk surjectivity of ι means its image ideal is the full O_{X,ξ}. Read
  RingedSpace.moduleStalkFunctor and PresheafOfModules.moduleStalkFunctor: both use
  the existing abelian stalk carrier and the germ-induced linear maps. The unit's
  stalk is canonically the structure-ring stalk, so surjectivity is intrinsic.
- (3)(c), product: read idealModuleProduct and idealModuleProductι in
  IdealModuleProductStalk.lean. They are image and image inclusion of
  `ι ▷ G ≫ (λ_ G).hom`, using the recorded SheafOfModules.monoidalCategory.
  Read TensorProduct.lean and its upstream Monoidal.lean: tensor is the
  sheafification of the sectionwise tensor. No product or tensor is redefined.
- (3)(c), G': `∃ G' : Subobject G`, coherent underlying module; existence of
  `h : G' ⟶ idealModuleProduct ι G` with `G'.arrow = h ≫ idealModuleProductι ι G`
  says exactly G' ⊆ JG, inside G. The factor map is automatically mono since its
  composite is mono. Surjectivity of the stalk of G'.arrow says its image is all
  G_ξ; stalk injectivity of a subobject gives the stated equality as submodules,
  not an unrelated abstract isomorphism. `P (G' : X.Modules)` is the final clause.
  Chosen subobject representatives do not add invariance assumptions: (0),(1)
  already imply invariance among coherent modules by the node's proof step 3(a).
- Conclusion: `∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F`.
  The existential G precedes the universal J and existential G', as required;
  G can depend on i and ξ, and G' on J.

Edge cases: X may be empty; no Nonempty X or nonzero F assumption is added. The
zero module is included explicitly, including all its isomorphic representatives
via (0),(1). Integral Z is necessarily nonempty by its existing class, exactly as
in the node. r = 0 is excluded only in (2); r = 1 is included. No empty-index-set
hypothesis is imposed elsewhere. J = O_X is permitted; J = 0 cannot have a full
stalk at ξ. Any characteristic is allowed; no field base is imposed. Scheme Z,
X, modules, rings and stalks share universe u, with no smaller independent testing
universe, hidden free variables, or additional finite-generation hypotheses.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: "Noetherian induction coherent sheaves property extensions
  nonempty repeated direct sum integral support generic stalk annihilated maximal ideal".
  Eight hits: IsFiniteType, IsLocallyNoetherian and its affine cover/local stalk facts;
  none states the node.
- Loogle via msearch: `AlgebraicGeometry.Scheme, (Prop → Prop)`: zero hits.
  The earlier `ShortComplex.ShortExact, SheafOfModules` query was an unknown-identifier
  response and was not treated as evidence.
- LeanSearch attempted via msearch with extensions, repeated sums and generic integral
  supports: service unavailable (Internal Server Error), no verdict inferred.
- rg on Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf for
  `d[eé]vissage|higher.rank.cohomological|property.*integral|integral.*property`.
  Found prime-factor/etale/derived devissage and the already landed
  CoherentPropertyIrreducible. Read that declaration: it is the two-out-of-three,
  fixed-support, rank-one-stalk 01YH statement, not 01YM. No exact existing statement.
  Reused the existing ideal product, coherent predicate and stalk constructions.

Mismatch repaired: the worker used
`attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts` for the direct sum.
The standing brief forbids file-local instances in a statement module. Removing it
confirmed the missing HasBiproduct elaboration; I supplied
`HasBiproduct.of_hasProduct (fun _ : Fin r ↦ F)` explicitly to `@biproduct`, removed
the local attribute, wrapped the signature within 100 columns and synchronized
lean.statement verbatim. This is the same finite direct sum, with no mathematical
change. Everything else was preserved, including the nine-step proof docstring.
There is one named theorem with sorry, no added definition, private copy or proof.

Validation: revised module compiles cleanly on the server under the default timeout;
no warnings or errors. The node record equals the file signature. Delivery preflight
and final server compile are run by deliver2.py below.
