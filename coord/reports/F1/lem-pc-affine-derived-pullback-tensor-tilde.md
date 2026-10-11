## Worker report

Module: `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, file
`lean/Sheaf/AlgebraicGeometry/AffineDerivedPullbackTensorTilde.lean`.
The module states all three clauses of `lem-pc-affine-derived-pullback-tensor-tilde`.
There are six named theorems, each proved only by `sorry`; no definition or instance is
created. Four of the statements are natural-isomorphism statements. The two additional
object statements express the affine formulas for every choice of K-flat resolution,
including resolutions of arbitrary, unbounded module complexes.

Hypotheses and clauses, in order:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)` in
  `AlgebraicGeometry.derivedPullback_openRestriction_iso` use the recorded Mathlib scheme
  and morphism. No geometric property of X, Y, or f is assumed.
- Derived categories: `HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings ...))`
  supplies the same localization and carrier as `schemeDerivedCategory`. These are
  implementation parameters of the derived categories, not extra mathematical hypotheses.
  All scheme-module derived categories in each comparison share the hom universe w.
- Clause (1), opens and image containment: `(U : X.Opens) (V : Y.Opens)` and
  `(hUV : U ≤ f ⁻¹ᵁ V)` are exactly U, V, and f(U) contained in V.
  `f.resLE V U hUV` is the induced morphism `U.toScheme ⟶ V.toScheme`.
- Clause (1), pullback restriction: `derivedPullback_openRestriction_iso` states a
  natural isomorphism `derivedPullback f ⋙ R_U ≅ R_V ⋙ derivedPullback (f.resLE V U hUV)`.
  Here R_U and R_V are written out as `SheafOfModules.overFunctor ⋙
  Equivalence.functor (Scheme.Modules.overEquiv ...)`, followed by `mapDerivedCategory`.
  Its component at every E is the requested isomorphism. The explicit Equivalence.functor
  category arguments retain the shared SheafOfModules category instance.
- Clause (1), tensor restriction: `derivedTensor_openRestriction_iso` states the natural
  isomorphism of curried bifunctors between `(K,L) ↦ R_U(K ⊗ L)` and
  `(K,L) ↦ R_U K ⊗ R_U L`. `Functor.whiskeringRight` postcomposes with R_U and
  `Functor.whiskeringLeft` precomposes the second variable with R_U. Thus naturality is
  expressed in both K and L. `⊗` is the globally recorded `schemeDerivedTensorMonoidal`,
  not a new monoidal instance or an underived tensor.
- Clause (2), affine schemes and ring map: `(A B : Type u) [CommRing A] [CommRing B]`
  and `(φ : A →+* B)`, with `Spec.map (CommRingCat.ofHom φ)`, render
  `Spec B → Spec A`. Commutativity is required for these spectra, as throughout the source.
- Clause (2), every complex M: `derivedPullback_tilde_iso` takes an arbitrary
  `M : CochainComplex (ModuleCat.{u} A) ℤ`. For any resolution `(s : P ⟶ M)` with
  `QuasiIso s` and `(HomologicalComplex.quasiIso ...).kFlat P`, its conclusion is
  `Lf*(Q(tilde M)) ≅ Q(tilde (extendScalars φ P))`.
  The resolution binders specify how the derived tensor in the node is evaluated; they
  do not require M itself to be K-flat or the ring map to be flat. Every M admits such
  a resolution. `extendScalars φ` is the B-linear complex `B ⊗_A P`, canonically the
  same base-change representative as the node's `M ⊗^L_A B`.
- Clause (2), canonical comparison: `derivedPullback_tilde_kFlat_natIso` gives the
  natural isomorphism on the full subcategory `CochainComplex.KFlat (ModuleCat A)`.
  The two functors are `tilde ⋙ Q ⋙ derivedPullback (Spec φ)` and
  `extendScalars φ ⋙ tilde ⋙ Q`, both precomposed with `CochainComplex.ιKFlat`.
  This is the natural comparison on resolving models; using Q(tilde s) transports it
  to M. Naturality supplies compatibility with maps of K-flat models and therefore
  resolution comparisons. No arbitrary derived-tensor object is a hypothesis.
- Clause (3), every pair of complexes: `derivedTensor_tilde_iso` takes arbitrary
  `M N : CochainComplex (ModuleCat.{u} A) ℤ` and any K-flat resolution `P ⟶ M`.
  Its conclusion is `Q(tilde M) ⊗ Q(tilde N) ≅ Q(tilde (Tot(P ⊗_A N)))`.
  The concrete module complex is `CochainComplex.mapBifunctor P N
  (curriedTensor (ModuleCat.{u} A))`: precisely the derived tensor computed by P.
  N has no flatness or boundedness hypothesis.
- Clause (3), canonical comparison: `derivedTensor_tilde_kFlat_natIso` gives the
  natural isomorphism in a K-flat first model and an arbitrary second complex.
  The right bifunctor is `curriedTensor (ModuleCat A).map₂CochainComplex`, which is
  the functorial total tensor underlying `mapBifunctor`. Both variables then undergo
  termwise tilde and Q on the left; the total complex undergoes tilde and Q on the right.
  Naturality supplies the comparison used with a resolution of M.
- All appearances of termwise tilde use `tilde.functor (.of A)` and the recorded
  `tilde.map_zero`, with an explicit `@id` type annotation selecting the shared category
  `SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)`. `DerivedCategory.Q` makes
  these complexes objects in exactly D(O_Spec A). No separate tilde functor is defined.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `AlgebraicGeometry.derivedPullback` and
  `exists_derivedPullback` (the latter's K-flat computation explains the comparison).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`. All three signatures and
  docstrings were read; only the ambient category is needed in these formulas.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  `HomologicalComplex.mapBifunctor` totalization, and `curriedTensor`.
  The recorded `SheafOfModules.monoidalCategory` was read in the upstream sheaf tensor
  module; it supplies the underived tensor used by the shared K-flat construction.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`, `IsKFlatResolution`, and
  the shared sheaf tensor zero-preservation statements. Their site-level signatures
  were read; the ordinary-module specialization is the landed node below.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `exists_affineQCohDerivedEquivalence`. Its full signature and proof docstring were
  read; it justifies the induced exact termwise tilde functor used in the proof text.
  The statement does not choose an arbitrary equivalence in place of termwise tilde,
  and does not import this module merely to cite a proof dependency.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.toOpen`,
  `tilde.toOpen_res`, `tilde.functor`, `tilde.map_zero`. The declaration bodies and
  docstrings were read. Termwise tilde uses the actual functor, not an abstract sheaf
  with unspecified action.
- Added already-landed statement dependency `def-pc-scheme-derived-tensor-structure`:
  `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `schemeDerivedTensorMonoidal`.
  The node and full definition were read and reused, as required by the current convention.
- Added already-landed statement dependency `def-pc-module-kflat-complex`:
  upstream `CategoryTheory.MorphismProperty.kFlat` and `CochainComplex.ιKFlat`, in
  `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` (generic predicate from
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`). The recorded criterion is
  tensoring on either side preserving quasi-isomorphisms, equivalent to the acyclic
  total-tensor criterion by cones and signed symmetry over commutative rings.
- For restriction, the shared `moduleOverFunctor_*` instances from
  `Sheaf.Paper.DerivedHomMayerVietoris` are reused through the derived-category import.
  The existing Mathlib declarations `Functor.additive_of_preserves_binary_products`,
  `comp_preservesFiniteLimits`, and `comp_preservesFiniteColimits` are enabled with
  `attribute [local instance]`, as explicitly permitted by STATE's LOCAL ATTRIBUTE
  INSTANCES ruling. No new local instance is declared. Downstream readers enable
  these same existing declarations when elaborating the restriction expressions.
- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` supplies the shared
  instance `ModuleCat.extendScalars_additive`; importing it resolves the missing
  zero-preservation instance for the termwise scalar-extension functor.

Edge cases checked before writing: zero complexes; zero rings (empty spectra);
U or V empty; U and V whole schemes; identity f and identity ring map; arbitrary
unbounded complexes (infinite totalization coproducts); nonflat ring maps. No assumption
excludes any of these. The opens are arbitrary, not required to be affine or quasi-compact.
All universes are explicitly declared, with no automatic implicit variable.

Searches for the statement and its notions:

- `msearch.py ... leanfinder "derived pullback and derived tensor of associated sheaves
  of module complexes on affine schemes"`: 8 hits, all underived pullback/tensor APIs
  (`Scheme.Modules.pullback`, `pullbackPushforwardAdjunction`, `SheafOfModules.pullbackIso`,
  `pullbackComp`, and related maps); no exact derived affine/restriction statement.
- `msearch.py ... loogle "AlgebraicGeometry.tilde, DerivedCategory"`: OK, 0 hits.
- `msearch.py ... grep "derived.*(tilde|tensor)|tilde.*(derived|tensor)"
  AlgebraicGeometry`: OK, 0 Mathlib hits.
- `msearch.py ... leansearch "derived pullback associated sheaf complex affine derived
  tensor"`: UNAVAILABLE, Internal Server Error. No mathematical verdict is drawn from it.
- `rg` for the item id and `derived.*tilde|tilde.*derived` in the upstream
  `WeilConjectures/`: no match.
- `rg` for those patterns in `lean/Sheaf`: existing related statements cite this item
  in proof docstrings, including DerivedPullbackTensorQCoh and TorAmplitudeQCohTest;
  no existing declaration states all, or any exact affine/restriction clause of this node.
- `rg` across the source, Mathlib, project modules and `dag/lean_names_upstream.json`
  for all six proposed declaration names: no name collision.
- Source and Mathlib searches found the existing generic module K-flat category,
  `ModuleCat.extendScalars`, tilde, mapBifunctor, map₂CochainComplex, and the shared
  extension-of-scalars additivity instance; all are reused, none duplicated.

Sources opened: https://stacks.math.columbia.edu/tag/08DW (including the restriction
sentence in its proof), https://stacks.math.columbia.edu/tag/08DX, and
https://stacks.math.columbia.edu/tag/08DV. The literature .tex checkout is not present
on this machine, so these exact primary-source pages were read instead.

Node fault in proof step 3: it mentions preservation of only finite direct sums,
although the complexes are unbounded and totalization can use infinite direct sums.
This does not invalidate the statement: tilde is a left adjoint and preserves all
coproducts. The Lean theorem docstrings give that complete corrected justification.
The node's statement is unchanged; no statement correction or new/dependency module
is necessary. The two added stmt_deps are existing, landed nodes, permitted by
brief-stage2 §5 / STATE "STMT_DEPS MAY GAIN LANDED NODES".

Validation: server single-file compile succeeded with exit code 0 and no warnings
(241 lines before the module's main-statements index, 23.8 seconds).
`deliver2.py F1 lem-pc-affine-derived-pullback-tensor-tilde --no-push` printed OK:
the module compiles and passes preflight except for the independent second reading,
which is deliberately left to the second reader. Nothing was pushed.

## Second reading by F1

Independent reading of the sandbox node and all six statements, against the source
and the recorded dependencies. Verdict: all three clauses are rendered correctly;
no Lean statement, node statement, or definition needed repair. This reading adds
the review record only, leaving the Worker report in place.

Source checked independently: Stacks `perfect.tex`, section
`section-derived-quasi-coherent` (its introductory conventions), and labels
`lemma-affine-K-flat`, `lemma-quasi-coherence-pullback`, and
`lemma-quasi-coherence-tensor-product`. The literature checkout is absent here;
I retrieved the primary tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex
into the item's scratchpad and read the relevant text. I also opened
https://stacks.math.columbia.edu/tag/08DV,
https://stacks.math.columbia.edu/tag/08DW, and
https://stacks.math.columbia.edu/tag/08DX. There is no standing Noetherian,
separatedness, characteristic, boundedness, or flatness assumption in this section.
The source reverses the letters X,Y in 08DW relative to the node; the Lean follows
the node's direction, correctly giving a functor from Y to X.

Object/hypothesis/conclusion checklist (the node's statement in order):

1. Objects X,Y and a scheme morphism f:X -> Y: `{X Y : Scheme.{u}}`
   and `(f : X ⟶ Y)` in `derivedPullback_openRestriction_iso`. Read
   Mathlib's `Scheme`, `Scheme.Hom`, and `Scheme.Opens`; these are schemes,
   locally ringed-space morphisms, and arbitrary opens. PASS.
2. D(O_Z) and Lf*: `schemeDerivedCategory Z` and `derivedPullback f`.
   Read `DerivedCategory.lean`, including its QCoh full-subcategory definitions,
   and `DerivedPullback.lean`, including `exists_derivedPullback` and its counit
   on K-flat models. This uses the shared SheafOfModules category, with the
   left derived functor of the recorded tensor pullback, not Mathlib's other
   module pullback. The `HasDerivedCategory.{w}` binders select localizations;
   they are the dependency's implementation parameters, not geometric
   hypotheses. No QCoh condition is imposed on E,K,L in clause (1). PASS.
3. Derived tensor on any scheme Z: `curriedTensor (schemeDerivedCategory Z)`
   and `⊗` use the global `schemeDerivedTensorMonoidal`. Read its definition:
   it is the K-flat derived monoidal localization of the sheaf tensor, not
   an arbitrary tensor instance. Read the sheaf `IsKFlat` and resolution
   definitions and Mathlib's total `mapBifunctor`. PASS.
4. Opens U,V and f(U) contained in V: `(U : X.Opens) (V : Y.Opens)`
   with `(hUV : U ≤ f ⁻¹ᵁ V)`. `f.resLE V U hUV` is the morphism from
   U.toScheme to V.toScheme. No affine/quasi-compact condition on either open.
   PASS.
5. Clause (1), every E: `derivedPullback_openRestriction_iso` is a
   natural isomorphism of the two composite functors; its component at E
   gives exactly `(Lf*E)|U ≅ L(f|U)*(E|V)`. Read `overEquiv` and the shared
   restriction exactness instances in `DerivedHomMayerVietoris.lean`.
   `overFunctor ⋙ overEquiv.functor`, followed by `mapDerivedCategory`,
   restricts O-module complexes to the actual open subscheme. PASS.
6. Clause (1), every K,L: `derivedTensor_openRestriction_iso` compares
   curried tensor followed by restriction to restriction in both variables
   followed by curried tensor. The `whiskeringRight` on the left restricts
   the value; `whiskeringLeft` on the right restricts the second input.
   Thus components give precisely `(K ⊗^L L)|U ≅ K|U ⊗^L L|U`, naturally
   in both factors. Natural isomorphisms express the node's canonical
   comparisons; no unrelated extra conclusion is included. PASS.
7. Clause (2), affines and ring map: `(A B : Type u) [CommRing A]
   [CommRing B] (φ : A →+* B)` and `Spec.map (CommRingCat.ofHom φ)`
   are Spec B -> Spec A. Commutative rings are the rings used for Spec
   throughout the source; neither ring is assumed a domain or a field. PASS.
8. Clause (2), every complex M: `(M P : CochainComplex (ModuleCat.{u} A) ℤ)`
   with `(s : P ⟶ M) (hs : QuasiIso s)` and the recorded module K-flat
   predicate on P in `derivedPullback_tilde_iso`. P,s,hs,hP describe any
   representative of the module derived tensor, not a restriction on M.
   The right side is tilde of termwise `ModuleCat.extendScalars φ P`,
   the B-module complex B tensor_A P, canonically M tensor-derived_A B.
   The left side is Lf* applied to Q of termwise tilde M. PASS.
9. Clause (2), functorial comparison: `derivedPullback_tilde_kFlat_natIso`
   uses the full inclusion `CochainComplex.ιKFlat` and compares exactly
   the two resolving-model functors. Its components give the affine formula
   for P; exact tilde transports Q(s) to an isomorphism, yielding the
   object formula for arbitrary M. Naturality supplies compatibility with
   resolution maps, rather than assuming an arbitrary derived-tensor object.
   Read the generic `MorphismProperty.kFlat`, the module specialization
   `kFlat_iff_preservesQuasiIso`, and `ιKFlat`. PASS.
10. Clause (3), every pair M,N: `(M N P : CochainComplex (ModuleCat.{u} A) ℤ)`
    with any K-flat quasi-isomorphism P -> M in `derivedTensor_tilde_iso`.
    N remains arbitrary. The conclusion is Q(tilde M) tensor-derived
    Q(tilde N) isomorphic to Q(tilde (mapBifunctor P N (curriedTensor _))).
    The latter is the direct-sum total module tensor representing
    M tensor-derived_A N, including the signed second differential. PASS.
11. Clause (3), naturality: `derivedTensor_tilde_kFlat_natIso` compares
    the same functors in a K-flat first model and arbitrary second complex.
    `map₂CochainComplex` is the functorial total tensor used by
    `mapBifunctor`; postcomposition on the right applies tilde and Q to
    the resulting total complex. Maps in both variables are included.
    Exact tilde and a resolution of M give the general comparison. PASS.
12. Associated sheaf in (2),(3): read Mathlib's `tilde`, `toOpen`,
    `toOpen_res`, `tilde.functor`, and `tilde.map_zero`; these are precisely
    the dependency's associated sheaf with localization sections, applied
    termwise by `mapHomologicalComplex`. The explicit `@id` annotation
    chooses the shared SheafOfModules category instance. The affine QCoh
    equivalence dependency's signature identifies this very functor after Q;
    no arbitrarily chosen equivalence or private tilde is substituted. PASS.

Edge cases: empty schemes and opens (including zero-ring spectra) are allowed;
no `Nonempty` hypothesis on points or opens occurs. Zero complexes, degree zero,
and arbitrary positive and negative degrees are covered by cochain complexes
indexed by all ℤ. The complexes may be unbounded, and `mapBifunctor` uses all
diagonal coproducts, not a finite truncation. Identity morphisms, whole opens,
arbitrary characteristic, and nonflat ring maps are covered. The source has no
index-family binder; empty sums are handled by the shared total construction.
Universe u is arbitrary, and w selects the common derived-category hom universe;
objects can be placed in a common universe, so no mathematical ring or scheme
size case is excluded. There are no automatically introduced variables or
unbound universes (confirmed by the explicit binders and server compile).

Independent H4 searches, with queries different from the first worker's:

- LeanFinder: "restriction open subscheme commutes derived base change
  associated module sheaf tensor total complex": 8 hits, all underived
  tilde-section restriction or Scheme.Modules restriction APIs; no match.
- Loogle: `AlgebraicGeometry.tilde, CochainComplex`: OK, 0 hits.
  An earlier `AlgebraicGeometry.tilde.functor, CategoryTheory.NatIso` query
  reported unknown identifier NatIso; I replaced it with the valid query above.
- Mathlib grep service: `tilde.*(derived|KFlat)|derived.*tilde` in
  AlgebraicGeometry: OK, 0 hits.
- LeanSearch: "derived restriction to open subschemes commutes with tensor
  product of complexes of structure sheaf modules": unavailable, Internal
  Server Error; no verdict inferred from the unavailable service.
- Direct rg over Mathlib, upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json for those derived-tilde patterns and all six
  declaration names: no duplicate statement/name. Related project hits are
  proof-docstring citations and the affine derived equivalence; they do not
  state these comparisons. Broader tensor/pullback searches find underived
  `exists_tensorPullback_tilde_iso` and `affine_tilde_tensor`, and upstream
  étale derived tensor formulas with different coefficient sheaf categories.
  Those are not the O_X-module statements here.

No new node or dependency module occurs in this delivery. The two added
statement dependencies are already recorded, landed nodes, and are reused.
All the dependency records were opened, as were their relevant declarations;
none requires replacement. The module introduces no definitions or instances.
All six named theorem proofs are only `sorry`. Every declaration has its source,
blueprint tag, and relevant proof steps in its docstring. Imports supply the
shared tensor, K-flat inclusion, tilde, derived pullback and scalar-extension
additivity; the existing local attribute instances are allowed by STATE.

Mismatch audit: no mismatch in the Lean signatures. The node proof's finite-sum
justification in step 3 is insufficient for unbounded complexes, as the Worker
report already says; both relevant Lean docstrings already correctly use
arbitrary coproducts preserved by tilde as a left adjoint. No statement correction
is necessary and the node's proof fields are left unchanged. No disputed flag
remains. The recorded `lean.statement` is the first theorem's exact signature;
the `declarations` list records all six clauses/comparisons in the module.

Validation: independent server single-file compile succeeded, 250 lines,
23.7 seconds, exit code 0, with no warning. The first compile invocation used
a relative path absent from the read-only repository; rerunning with the
sandbox's absolute module path succeeded. No source file was changed for that.
