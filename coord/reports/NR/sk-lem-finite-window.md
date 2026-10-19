## Worker report

The module `Sheaf.Paper.FiniteWindow` states `AlgebraicGeometry.ProEtale.finiteWindow`
and `AlgebraicGeometry.ProEtale.finiteWindow_padicAlgCl`. Both proofs are `sorry`.
The transparent helper definition `AlgebraicGeometry.ProEtale.FiniteWindowAssertions`
packages exactly the conclusion: a family of additive equivalences, its canonical-map
equation, and its naturality equation. This belongs to the owning node, as permitted for
helpers, and is listed in lean.declarations. It constructs no coefficient object or
map, chooses no data, and introduces no replacement for any existing notion.
There are no new nodes, dependency repairs, or changes to the natural statement.
Each theorem has the source and the complete four-step DAG proof in its docstring.

Clause-by-clause translation:

- The arbitrary scheme is `(X : Scheme.{u})`, with no finiteness, nonemptiness,
  characteristic, dimension, separation, or base-field hypotheses.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The standard fixed algebraic closure is
  `PadicAlgCl ℓ`. Finite extensions inside it are exactly
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`; its field structure and topology are
  the restricted ones. This is the fixed standard algebraic-closure model already
  used by the dependency `finiteWindow_unbounded`.
- The two coefficient choices are handled by the two theorems, respectively
  `Profinite.continuousMapRingObj E` and `Profinite.padicAlgClRingObj ℓ`.
  The latter is the finite-subextension-valued condensed ring, not all continuous
  functions into the topological algebraic closure.
- `pulledBackModuleObjects Λ X` is the ambient category of modules over
  `coefficientRing X (Mon.mk Λ)`, whose underlying ring object is `condensedRingObj Λ X`,
  namely the prescribed `p_X^* Λ`. No constant discrete coefficient sheaf is substituted.
- The source sheaf is `(C : pulledBackModuleObjects Λ X)` and
  `(hC : IsConstantModelConstructible Λ X C)`. This is the recorded finite constant-model
  constructibility on a finite constructible locally closed stratification for qcqs X,
  and on affine opens for arbitrary X. Its degree-zero placement is
  `(DerivedCategory.singleFunctor _ 0).obj C` everywhere in the conclusion.
- The nonnegative bound is `(d_C : ℕ)`. The meaning of 'as in
  sk-lem-uniform-constructible-ext' is the hypothesis `hExt`: for every constructible N
  and every natural r strictly above d_C, `Subsingleton (@Abelian.Ext _ _ _
  (HasExt.standard _) C N r)`. A degree strictly above a nonnegative bound is necessarily
  positive, so this covers every integer degree in the node. Mathlib's `Ext.homAddEquiv`
  identifies these groups with the ambient derived morphisms. We assume the bound
  rather than import the geometric hypotheses used by another theorem to produce it.
- `IndCons` is expanded without a copied definition as
  `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)`; its definition is a
  small filtered colimit presentation in the ambient module category. The index-size
  convention agrees with the published lower-tail lemma and sibling ind-heart statements.
- `Dic` is exactly the indexing subtype
  `{K : DerivedCategory (pulledBackModuleObjects Λ X) // ∀ q : ℤ,
  ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
  ((DerivedCategory.homologyFunctor _ q).obj K)}`. This is only an inline expression of
  the node's full object class, not a new category or predicate. Naturality quantifies
  over every ambient morphism `f : K.val ⟶ L.val`, so it is naturality on the full
  subcategory Dic. No lower or upper bound on K is present.
- `(m : ℤ)` is arbitrary. Mathlib shifts `⟦m⟧` have the stated cohomological convention
  `H^q(K[m]) = H^(q+m)(K)`. The window uses exactly
  `(DerivedCategory.TStructure.t.truncGE (m - (d_C : ℤ))).obj
  ((DerivedCategory.TStructure.t.truncLE m).obj K.val)`.
- `FiniteWindowAssertions C P d_C m` is the exact conclusion packaged over a general
  abelian category, instantiated with the ambient coefficient module category and
  `P K := ∀ q, ObjectProperty.ind ... ((DerivedCategory.homologyFunctor _ q).obj K)`.
  The isomorphisms of Hom groups in this transparent helper are an existential family
  `e` of additive equivalences
  `Hom(C,K[m]) ≃+ Hom(C,(tau_ge(m-d_C) tau_le(m) K)[m])` for all Dic objects K.
  The first conjunct is `e K (f ≫ (truncLEι m).app K.val shifted) =
  f ≫ (truncGEπ (m-d_C)).app (tau_le(m) K.val) shifted`. Thus it identifies the
  equivalence with the actual truncation zigzag: `e a_K = b_K`.
  The canonical upper-truncation map a_K is bijective by standard t-orthogonality,
  independently of any extra hypothesis; this equation characterizes exactly
  `b_K composed with inverse a_K` and cannot select an arbitrary unrelated equivalence.
- The second conjunct explicitly asserts naturality: for all K,L in Dic, all ambient
  `f : K.val ⟶ L.val`, and all `g : C[0] ⟶ K.val[m]`,
  `e L (g ≫ f[m]) = e K g ≫ ((truncLE m ⋙ truncGE (m-d_C)).map f)[m]`.
  This is the node's naturality in K for fixed C,d_C,m. The finite range
  m-d_C,...,m is the cohomological support of this exact canonical window.

Dependencies read and used:

- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and the full subcategory
  `ConstantModelConstructible`. The predicate form is definitionally membership in Cons.
- sk-lem-uniform-constructible-ext: `Sheaf.Paper.UniformConstructibleExt`,
  `AlgebraicGeometry.ProEtale.uniformConstructibleExt`, imported for the bound's provenance.
  The conditional theorem here takes exactly the asserted Ext bound; it does not assert
  its existence on arbitrary schemes or add the producer theorem's geometric assumptions.
- def-weil-derived-cohomology-sheaves: its exact general `mathlib_match`,
  `DerivedCategory.homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. The primary recorded module
  `Sheaf.Paper.PbcQbarStandardCohomology` additionally supplies common-finite-stage Qbar
  cohomology, an interface not needed here. Its note preserves the general ambient
  cohomology declarations; we use the already recorded exact ambient Mathlib match.
- def-kun-truncations: `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, whose
  documented/reexported canonical derived truncations are
  `DerivedCategory.TStructure.t.truncLE`, `truncGE`, `truncLEι`, and `truncGEπ`.
  These have their implementations in Mathlib's TStructure TruncLEGT and TruncLTGE.
- sk-def-sfb-condensed-ring: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing` and its public continuous-coefficient constructors;
  the concrete coefficients use the already published `continuousMapRingObj`.
- sk-def-sfb-qlbar-condensed: published upstream
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and its underlying `padicAlgClRingObj`.
- sk-def-sfb-pulled-back-coefficients: published upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`, through the
  existing `pulledBackModuleObjects` abbreviation in `Sheaf.Paper.ModuleObjects`.
- Proof dependencies: Mathlib `TStructure.triangleLEGE_distinguished`,
  `DerivedCategory.TStructure.t`, `Triangulated.TStructure`,
  `Pretriangulated.Triangle.coyoneda_exact₂` (and rotations), and
  `Sheaf.Paper.FiniteWindowUnbounded` declarations `finiteWindow_unbounded` and
  `finiteWindow_unbounded_padicAlgCl`. Every stated proof-dependency module is imported.

Edge cases were checked before writing: X empty; C=0; K=0; d_C=0 giving the
single degree m; m positive, zero, or negative; unbounded K in either direction;
zero cohomology and the constant filtered zero diagram; E equal to the base field;
both finite and algebraic-closure coefficients. All occur in the displayed signatures.
All variables and universes u,v,w,t are explicit (`set_option autoImplicit false`).
The assertion-packaging helper has fully general, independent category-object,
category-morphism, and derived-category universes; the two actual coefficient cases use
the existing standard derived-category instances without a new equality of universes.
No local notation, private construction, chosen arbitrary map, or hidden boundedness
assumption is used. No disputed statement or node fault was found.

Searches for an existing declaration:

- `msearch.py leanfinder`: "Maps from a constructible sheaf into an unbounded derived
  object depend only on a finite window of canonical truncations". Eight results:
  `DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE`,
  `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`, `DerivedCategory.IsGE`,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`,
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`,
  `DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE`,
  `DerivedCategory.instIsLEObjSingleFunctor`,
  `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`. None states this
  constructible finite-window isomorphism or its canonical naturality.
- `msearch.py loogle`: `"trunc", "homEquiv"`. Three results, all
  `SSet.OneTruncation₂.nerveHomEquiv` and its identity/application lemmas; unrelated.
- `msearch.py grep`: `finite.?[Ww]indow|hom.*trunc|trunc.*hom`, restricted to
  `CategoryTheory/Triangulated/TStructure`. Twenty results in truncation and spectral-object
  files; none supplies the required constructible finite-window statement.
- Direct `rg` of Mathlib, upstream WeilConjectures, and `dag/lean_names_upstream.json`
  for `finiteWindow|finiteWindow_padicAlgCl`: no existing declarations.
- Direct upstream/project search for
  `finiteWindow|finite_window|finite.window|sk-lem-finite-window`: the side project has
  the already used lower-tail module, proper-direct-image windows, and an unrelated
  tensor window; no duplicate of this node's Hom equivalence. The upstream node-id
  search has no match. The relevant canonical truncation and coefficient signatures
  were opened in full rather than inferred from search-result names.

Validation: the initial fully expanded conclusion elaborated in the sandbox in 11.7 s,
but timed out at compiled-module export, also confirmed on the server. Factoring the
identical conclusion into the transparent generic FiniteWindowAssertions helper avoids
repetition of the large coefficient-category expression. Three long docstring/signature
lines in that first attempt were also shortened. All compilation uses scompile.py with
the unchanged 60-second per-file limit. Final results are recorded below.

The refactored module passed scompile.py: sandbox 50.1 s and library 16.0 s,
with no errors or warnings. The final documentation-only wrap changes keep all
lines within 100 characters. The delivery dry run recompiles the exact final file.

Additional LeanSearch check: msearch.py leansearch, query "Hom from a constructible
sheaf to an unbounded complex depends only on a finite interval of canonical cohomology
truncations". Eight hits: HomologicalComplex.ιTruncLE,
CochainComplex.instIsIsoIntιTruncLEOfIsStrictlyLE, CochainComplex.ιTruncLE,
HomologicalComplex.instIsIsoπTruncGEOfIsStrictlySupported, HomologicalComplex.πTruncGE,
CategoryTheory.HasExt.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQuasiIsoOfIsGEOfIsLEOfNat,
HomologicalComplex.stupidTruncMap, ComplexShape.Embedding.truncLEFunctor.
These construct truncations or bound Hom sizes; none gives the required constructible
finite-window equivalence or duplicates FiniteWindowAssertions. The exact helper name
was also searched in Mathlib, upstream, the side library, and lean_names_upstream.json:
no prior declaration.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
