## Worker report

The module `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` states
`AlgebraicGeometry.exists_closed_subset_of_galois_invariant` with its proof left as
`sorry`. No definitions or additional nodes are introduced. The declaration docstring
carries all ten steps of the node's proof, including the affine chart identification,
finite Galois reduction, extension of automorphisms, norm polynomial, radical ideal
calculation, surjectivity and gluing.

The local literature checkout has no `literature/stacks-project/varieties.tex`.
I therefore opened the primary source https://stacks.math.columbia.edu/tag/038B
(Lemma 33.7.10, label `lemma-closed-fixed-by-Galois`). Its hypotheses and conclusion
agree with the node, including possibly infinite Galois extensions. The specified action
is realized by the existing source declarations described below. No statement correction
or disputed statement is needed.

Hypothesis and clause correspondence:

- A field `k` is `(k : Type u) [Field k]`; the extension field is
  `(K : Type u) [Field K] [Algebra k K]`. The embedding is `algebraMap k K`.
- Galois means `[IsGalois k K]`: the full signature and docstring of Mathlib's class
  were read. Its two fields supply `Algebra.IsSeparable k K` and `Normal k K`.
  `Algebra.IsSeparable` says every minimal polynomial is separable and implies
  algebraicity; `Normal` requires every mapped minimal polynomial to split in `K`.
  There is no `FiniteDimensional` assumption and no algebraic-closure assumption.
- A scheme over `k` is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`;
  its structure map is `X ↘ Spec (.of k)`.
- `X_K` is `pullback (X ↘ Spec (.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. `Tbar` is a set of its underlying
  points (the explicit coercion `↥` ensures that `pullback` is a scheme, rather than
  allowing inference of a pullback in the category of types).
- The automorphism group is `K ≃ₐ[k] K`, exactly the `k`-algebra automorphisms.
  `specAlgEquivOver σ` is `Spec σ` as an endomorphism of the object
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
  `baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)` is precisely `σ_X`:
  its definition is `pullback.map` with identity on `X`, `Spec σ` on `Spec K`,
  and identity on `Spec k`. It is an automorphism since `σ.symm` induces its inverse.
  `Spec.map_comp` reverses ring-map composition, while `baseChangeMap_comp`
  preserves scheme-map composition, giving the reversed-composition clause in the node.
  These are specifications of the existing action, not extra hypotheses or a separately
  postulated arbitrary action.
- Closedness is `(hclosed : IsClosed Tbar)`.
- Invariance is `(hinvariant : ∀ σ : K ≃ₐ[k] K,
  (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Tbar = Tbar)`.
  This uses image equality, exactly as the node, with the actual induced action.
- The projection `p` is `pullback.fst` for the same two morphisms.
- The conclusion `∃ T : Set X, IsClosed T ∧ (pullback.fst ... ) ⁻¹' T = Tbar`
  gives both required clauses: a closed subset of `X` and precisely the prescribed
  inverse-image equality. No uniqueness or stronger subscheme descent is asserted.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs,
  used through `[Algebra k K]` and `algebraMap k K`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable; supplied by `IsGalois.to_isSeparable`.
  Also read `Normal`, Mathlib.FieldTheory.Normal.Defs and `IsGalois`,
  Mathlib.FieldTheory.Galois.Basic to verify the exact Galois hypothesis.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`,
  Mathlib.AlgebraicGeometry.Over, with its structure map `↘`.
- `def-pc-base-change`: imported Sheaf.AlgebraicGeometry.BaseChangeConventions and
  read its complete file and recorded note. The note explicitly directs scheme base
  change to `Limits.pullback` and the induced morphism to `baseChangeMap`.
  `Scheme.Modules.moduleBaseChange` itself is not relevant to subsets and is not used.
  Read `AlgebraicGeometry.baseChangeMap` and `baseChangeMap_comp` in
  WeilConjectures.AlgebraicGeometry.PicardFunctor; the former is the induced morphism used.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, including the functoriality signature;
  also read the recorded `Spec.homEquiv` in Mathlib.AlgebraicGeometry.GammaSpecAdjunction.
- Additional existing action constructor `AlgebraicGeometry.specAlgEquivOver`,
  WeilConjectures.AlgebraicGeometry.Picard.Jacobian, lines 997--1010: full signature,
  definition and docstring read. It takes any commutative algebra and an algebra
  automorphism, so is available without smoothness, properness, or any Picard hypothesis.
  This avoids introducing a second definition of the Galois action.

Edge cases checked before writing: empty `X` and empty/full `Tbar` satisfy the stated
form with empty/full `T`; no nonemptiness assumptions exclude them. The trivial extension
is included. Extensions of infinite degree are included. No characteristic is restricted;
nonperfect base fields are included as long as the stated extension is separable and normal.
Arbitrary nonaffine and non-quasi-compact schemes are included, with no finiteness or
separation assumptions. A shared arbitrary universe `u` is the project's scheme convention;
fields and schemes of different initial universe sizes can be lifted into their common
universe. There is no quantification over test objects in a smaller independent universe.
Every variable and universe is explicitly bound.

Searches made (recorded by msearch.py in `searches.jsonl`):

- LeanFinder: "A closed subset of a scheme after a possibly infinite Galois field extension
  invariant under all Galois automorphisms descends to a closed subset of the original scheme".
  Eight hits: fixing-subgroup closedness, Galois correspondence, integral-ring invariance,
  and unrelated geometric closedness lemmas; none states closed-subset descent.
- LeanSearch: "Galois invariant closed subset of scheme base change descends".
  Service unavailable (Internal Server Error), recorded as unavailable.
- Loogle: `IsGalois, IsClosed`. One hit, `InfiniteGalois.fixingSubgroup_isClosed`;
  it concerns a subgroup of the Galois group, not a subset of a scheme.
- Mathlib grep: `galois.*closed|closed.*galois|galois.*descend`.
  Twenty-one hits, principally order-theoretic Galois connections and field-theoretic
  closed subgroups. No matching scheme theorem.
- `rg` on WeilConjectures for Galois/closed/descent combinations and the exact node id:
  no existing realization. Searching `baseChangeMap` and `Spec`/algebra automorphisms
  located the reusable `specAlgEquivOver` action constructor above.
- `rg` on `lean/Sheaf` for the same concept found other fpqc-descent and Galois-category
  modules, but no declaration stating this theorem. The chosen theorem name has no
  existing occurrence in these libraries.

Validation: server single-file compilation and the delivery dry run are run as required;
only the expected `sorry` is left. The independent second reading is for the next worker.

## Second reading by H1

I independently opened the delivered node and Lean file, all five statement dependency
nodes, and the declarations below. The node agrees with Stacks Tag 038B. Since the local
Stacks checkout lacks varieties.tex, I read the primary TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
chapter Notation, the discussion preceding equation-galois-action-base-change-kbar,
and lemma-closed-fixed-by-Galois with its complete proof (current lines 765–849).
I also checked https://stacks.math.columbia.edu/tag/038B. The chapter only fixes the
letter k for the ground field; this lemma imposes no variety, finite type,
Noetherian, quasi-compactness, separatedness, or algebraic-closure hypothesis.
The reversed order of the two fibre-product factors in the source is the canonical
symmetry of the same base change and does not change the statement.

Object/hypothesis/conclusion checklist, written from the node before comparing:

1. Ground field k: `(k : Type u) [Field k]`. Exact.
2. Extension field K and its specified embedding of k:
   `(K : Type u) [Field K] [Algebra k K]`, with `algebraMap k K`. Exact.
   I read `Algebra` in Mathlib/Algebra/Algebra/Defs.lean:95; this is precisely the
   dependency def-pc-field-extension, not a chosen subfield or a finite extension.
3. Separable algebraic and normal, allowing infinite degree: `[IsGalois k K]`.
   I read IsGalois in FieldTheory/Galois/Basic.lean:57, Normal in
   FieldTheory/Normal/Defs.lean:34, and IsSeparable/Algebra.IsSeparable in
   FieldTheory/Separable.lean:539–570. The two IsGalois fields supply exactly
   separability of every minimal polynomial and algebraicity plus splitting of
   every minimal polynomial. Thus the separable-algebraic dependency is used
   through the class projection. No finite-dimensional hypothesis. Exact.
4. Automorphism group Aut(K/k): `K ≃ₐ[k] K`. Exact algebra automorphisms.
5. Scheme X over k and its structure morphism:
   `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and `X ↘ Spec (.of k)`.
   I read Scheme.Over in Mathlib/AlgebraicGeometry/Over.lean:36: it is the
   structure-map data, with no property of the map imposed. Exact.
6. Base change X_K: the scheme `pullback (X ↘ Spec (.of k))
   (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. Exact.
   I read the entire recorded BaseChangeConventions module and its node's note.
   It explicitly assigns scheme base change to Limits.pullback, and g_X to
   baseChangeMap; its primary moduleBaseChange declaration is for module sheaves,
   not a replacement for scheme base change. The existing conventions are used.
7. Induced automorphism σ_X = id_X × Spec(σ), its inverse, and reversed composition:
   `baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)`.
   I opened specAlgEquivOver in Picard/Jacobian.lean:997–1010: it is literally
   Over.homMk of Spec.map of σ.toAlgHom.toRingHom, with σ.commutes proving the
   compatibility. Its signature assumes only commutative rings and an algebra.
   I opened baseChangeMap, baseChangeMap_id, baseChangeMap_comp in
   PicardFunctor.lean:295–307: the map is pullback.map with identity on X,
   that exact Spec morphism, and identity on Spec k. Applying it to σ.symm
   gives the inverse; Spec.map_comp reverses the ring composition, so the
   specified opposite-group law holds. These are properties of the reused
   constructor, not additional hypotheses or an arbitrary postulated action.
   I also read Spec, Spec.map, Spec.map_comp in Scheme.lean:470–488 and
   Spec.homEquiv in GammaSpecAdjunction.lean:579. Exact.
8. Projection p: `pullback.fst` of precisely the same two maps. Exact.
9. Subset Tbar of the underlying points of X_K:
   `Tbar : Set ↥(pullback ...)`. The explicit scheme coercion excludes a
   set-theoretic pullback interpretation. Exact.
10. Tbar closed: `hclosed : IsClosed Tbar`. Exact.
11. Image invariance for every automorphism:
    `hinvariant : ∀ σ : K ≃ₐ[k] K, (baseChangeMap ... (specAlgEquivOver σ))
    '' Tbar = Tbar`. Same universal quantifier, action, and image equality. Exact.
12. There exists a closed T in X with precisely p⁻¹(T) = Tbar:
    `∃ T : Set X, IsClosed T ∧ (pullback.fst ...) ⁻¹' T = Tbar`.
    Both clauses and quantifier order are exact; no uniqueness, subscheme structure,
    or extra finiteness conclusion is inserted.

Edge cases: empty X and empty/full Tbar are admitted; the corresponding empty/full
T has the stated preimage. The trivial field extension and infinite Galois extensions
are admitted. Every characteristic and imperfect ground fields are admitted.
Nonaffine, non-quasi-compact, non-Noetherian schemes are admitted. A zero-ring affine
chart gives an empty scheme and is not excluded; the ground and extension fields
are nonzero as the source requires. No index set or n occurs, so empty indices and
n = 0 do not create an omitted case. The universe u is arbitrary and explicit,
with k, K, X in the same scheme-category universe. Different initial universe levels
can be raised to their common maximum; there is no small-test-object quantification
that could become vacuous. All variables and universes are bound by eye.

Independent searches (different wording from the worker; recorded by msearch.py):

- LeanFinder: `invariant Zariski closed sets descend along normal separable field
  extensions`. Eight results concern separable-closure operators, normal closures,
  and Krull topology; none is scheme closed-subset descent.
- Loogle: `IsGalois, Set.preimage`. Zero results.
- Mathlib grep: `closed.*invariant|invariant.*closed|closed.*descen`.
  Twenty-three results concern dynamics, invariant submodules, or descent of the
  universally-closed property; none supplies this subset-descent statement.
- Independently ran rg with the same concept alternatives and the full theorem
  name against WeilConjectures/, lean/Sheaf/, and dag/lean_names_upstream.json.
  The closest modules concern closed-subscheme descent, fpqc descent of morphism
  properties, and invariant Lie subspaces. None says this statement; the theorem
  name is absent. The worker's LeanSearch service failure remains recorded in
  its report; the independent LeanFinder and Loogle calls both succeeded.

No new definition nodes or dependency modules are delivered, so H12/H13 introduce
no additional review items. No statement_change exists or is needed. There is no
private definition, hollow data, additional instance, or proved theorem. The sole
proof is sorry. Both docstrings identify the source and blueprint; the statement's
ten proof steps match the node in order, including the finite subextension,
automorphism extension, fixed coefficients, radical calculation, surjectivity,
and local gluing. Imports supply IsGalois, the dependency conventions, and the
existing action constructor. Namespace, file topic, and all line lengths conform.
The JSON lean.statement equals the file's theorem signature verbatim.

Mismatches and repairs: none found. The Lean file and node are retained unchanged;
this independent review is appended to the worker report. Server compilation and
delivery preflight results are recorded below after running them.

Validation results: scompile.py passed with exit code 0, compiled in 2.1 seconds,
with no errors or warnings. deliver2.py --no-push printed OK: the delivery passed
preflight and compiled. The initial compile invocation used the repository working
directory and could not find the sandbox-relative file; rerunning from the sandbox
resolved that invocation error without changing code or tools.
