## Worker report

The module `Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember` states
`AlgebraicGeometry.Scheme.sr_matching_object_one_member`. Its only theorem proof is
`sorry`; it defines no new notion. The source proof is carried step by step in the
declaration docstring. The item's statement is unchanged. Its `stmt_deps` gains the
already-landed `lem-weil-pbc-matching-object-proper-faces`, whose diagram is used
literally; this addition is permitted by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).

Hypotheses and clauses, in order:

- Scheme X: `(X : Scheme.{u})`, with arbitrary universe `u` and no compactness or
  separation restriction.
- The augmented simplicial X-scheme with every U_n → X étale:
  `(U : SimplicialObject X.Etale)`. Each object has its own scheme and étale
  structure morphism to X. Each simplicial operator is an X-morphism; functoriality
  gives all simplicial identities and compatibility with augmentation. Conversely
  any augmented simplicial X-scheme in the node lifts to this category because
  `Etale.forget X` is fully faithful. Thus this encoding adds no hypothesis.
- Simplicial operators U(φ): `U.map φ.op`, with terms `U _⦋n⦌`.
- Matching schemes: `∃ M : ℕ → X.Etale` and projections `π n` to the existing
  `U.properFaceDiagram n`. `properFaceProperty n` requires source length < n
  and injectivity, and the full subcategory of `Over ⦋n⦌` supplies the commuting
  triangles. This is exactly the node's proper injective face diagram.
- M_0(U) = X: `M 0 = Etale.mk (𝟙 X)`. Its diagram is empty. In every degree the
  cone is asserted limiting by
  `Nonempty (IsLimit ((Etale.forget X).mapCone (Cone.mk (M n) (π n))))`.
  This is a limit in `Over X`, tested on ALL schemes over X, not just étale
  test schemes. Bundling `M n : X.Etale` asserts simultaneously that each
  matching scheme's structure morphism is étale, exactly clause (1).
- Matching map: `μ : ∀ n, U _⦋n⦌ ⟶ M n`, with
  `μ n ≫ (π n).app (op a) = U.map a.obj.hom.op` for every proper face a.
  Limit universality makes this the uniquely specified matching map. In degree
  zero μ is the augmentation, since its target is id_X and it is an X-morphism.
- K_n = {U_n}, K(φ) = (id, U(φ)): the literal functor
  `U ⋙ FormalCoproduct.incl.{w} X.Etale`. Mathlib's `incl` uses a PUnit index
  and maps a morphism to the unique singleton index map and that component.
- Clause (2): for each n the existential `ψ` is an isomorphism from the
  recorded `semiRepresentableMatchingObject` of K to `incl.obj (M n)`;
  `semiRepresentableMatchingMap ... n ≫ ψ.hom = incl.map (μ n)` is exactly
  the matching-map correspondence requested by the node.
- Clause (3): in every degree,
  `IsSemiRepresentableCovering (semiRepresentableMatchingMap ... n) ↔
  Surjective (μ n).left`.
- Consequence: the final conjunct is
  `IsSemiRepresentableHypercover K ↔ ∀ n, Etale (μ n).left ∧ Surjective (μ n).left`.
  Thus it includes the étale-covering condition and degree zero expressly.
  Existentially choosing the whole family of limiting vertices and maps is the
  usual simultaneous choice of the node's M_n(U); it adds no extra restriction,
  since limiting cones and their matching maps are unique up to comparison.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Scheme.smallEtaleTopology`, `Scheme.ofArrows_mem_smallEtaleTopology_iff`;
  with `Scheme.Etale`, `Etale.forget`, and `Etale.mk` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Used through the SR module.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, its `δ` and `σ`. SimplicialObject is
  exactly the functor category `SimplexCategoryᵒᵖ ⥤ C`.
- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`:
  `Scheme.semiRepresentableMatchingObject`, `semiRepresentableMatchingMap`,
  `IsSemiRepresentableCovering`, `IsSemiRepresentableHypercover`, and the
  finite-limit instance. All are imported and used without private copies.
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`:
  `SimplicialObject.properFaceProperty`, `ProperFaceCategory`,
  `properFaceDiagram`; the degree-one and higher comparison statements and
  docstrings were read in full. This already-landed node is added to stmt_deps.
- `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`: `FormalCoproduct.incl`.
- The recorded `Sheaf.Paper.FiniteSplitEtaleHypercover.FiniteSplitEtaleHypercover`
  dependency was read in full, including its matching_universal and
  matchingMap_projection fields. It describes the additionally split, finite,
  covering case over a qcqs X. The present node assumes none of those properties,
  so that specialized structure is not a binder or an unused import. Its general
  underlying simplicial object is the very same Mathlib `SimplicialObject X.Etale`
  used here. Its scheme-matching universal property is rendered by the existing
  proper-face cone and `IsLimit`, without defining another hypercover or matching
  notion. No dependency replacement module is needed.

Edge cases checked before writing:

- n = 0: the proper-face category is empty (no natural source length is < 0);
  the limit is id_X, the matching map is augmentation. A terminal cone does not
  omit the clause for arbitrary non-étale test schemes.
- n = 1: exactly two vertices, hence the fibre product over X, with no face-pair
  constraint. n ≥ 2: the proper-face diagram includes all injective lower faces.
- Empty X and empty terms: permitted as schemes étale over X; surjectivity onto
  an empty matching scheme is correctly allowed, while an empty source cannot
  cover a nonempty matching scheme.
- No qcqs, finite-presentation, splitting, or prior hypercover condition is
  assumed. No characteristic or nonempty-scheme restriction is present.
- Both scheme universe u and the arbitrary formal-family index universe w are
  explicit. The proper-face shape is finite; no universe bound omits a scheme.

Searches (performed for this item, recorded by msearch.py in searches.jsonl):

- LeanFinder: `matching objects of simplicial etale schemes agree with matching
  objects of singleton formal coproduct families`: 8 hits, on sigma open covers
  and GlueData.oneHypercover; none states this result.
- Loogle: `CategoryTheory.Limits.FormalCoproduct.incl,
  CategoryTheory.Limits.PreservesLimit`: 0 hits.
- LeanSearch: `simplicial matching objects formal coproduct singleton etale
  schemes`: unavailable (Internal Server Error), recorded as unavailable.
- Mathlib grep: `matching|Matching|preserves|PreservesLimit` in
  CategoryTheory/Limits/FormalCoproducts: 5 hits including the TODO on preservation
  of limits by incl and unrelated preservation by eval; no matching theorem.
- rg in WeilConjectures for `matching|Matching|FormalCoproduct`: unrelated
  matching prose and CechComparison formal coproducts; no theorem of this form.
  Search for the item id there gives no hit.
- rg in lean/Sheaf for `matching.*[Oo]ne|[Oo]ne.*matching`: general degree-one
  matching statements and proper-face comparisons; no singleton étale theorem.
- Name search for `sr_matching_object_one_member` in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no existing declaration.

The local literature checkout contains lists only. The actual source places were
opened and read on the Stacks website: [01G2](https://stacks.math.columbia.edu/tag/01G2),
[01G3](https://stacks.math.columbia.edu/tag/01G3),
[01G5](https://stacks.math.columbia.edu/tag/01G5), and
[0186](https://stacks.math.columbia.edu/tag/0186). The memberwise finite-limit formulas,
covering definition, hypercover definition, and compatible-face argument agree with
the node. No statement fault or disputed clause was found.

Validation: lcompile.py compiled the single module cleanly (exit code 0, no warnings).

## Second reading by K1

I reread the node statement, its Stacks source places (01G2, 01G3, 01G5, and 0186),
the dependency declarations, and the Lean theorem independently. The theorem's binders and
clauses render the node as follows, in order:

- The arbitrary base scheme is `(X : Scheme.{u})`; no compactness, separation, characteristic,
  or nonemptiness assumption is added.
- The augmented simplicial etale X-scheme is `U : SimplicialObject X.Etale`. Its objects are
  etale X-schemes and its morphisms are X-morphisms; the augmentation is each object's bundled
  structure map to X. The independent family universe `w` occurs only in
  `FormalCoproduct.{w}` and does not restrict `X`.
- The matching family and projections are
  `M : ℕ → X.Etale` and
  `π : ∀ n, (Functor.const _).obj (M n) ⟶ U.properFaceDiagram n`.
  `properFaceDiagram` is indexed by injective proper faces, exactly the nonidentity
  order-preserving maps from `[k]` to `[n]` with `k < n`.
- The matching maps are `μ : ∀ n, U _⦋n⦌ ⟶ M n`, and
  `μ n ≫ (π n).app (op a) = U.map a.obj.hom.op` for every proper face `a`.
- `M 0 = Etale.mk (𝟙 X)` gives the degree-zero matching object and the augmentation case.
  For every degree, `Nonempty (IsLimit ((Etale.forget X).mapCone
  (Cone.mk (M n) (π n))))` states the limit in schemes over X after forgetting etaleness,
  so the universal property is tested on all X-schemes as in the source.
- For each degree, the existential isomorphism
  `semiRepresentableMatchingObject (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≅
  (FormalCoproduct.incl.{w} X.Etale).obj (M n)` and its commuting equation identify the
  semi-representable matching map with the singleton family map induced by `μ n`.
- The covering equivalence is exactly
  `IsSemiRepresentableCovering (...) ↔ Surjective (μ n).left`; etaleness of the component
  follows from its being an X-morphism between etale X-schemes, as in the source.
- The final clause is exactly
  `IsSemiRepresentableHypercover (...) ↔ ∀ n, Etale (μ n).left ∧ Surjective (μ n).left`,
  i.e. every matching map is a surjective etale morphism, including degree zero.

No mismatch was found, and no Lean text was changed. In particular, the theorem does not add
qcqs, finite, split, covering, or hypercover hypotheses inherited from the specialized
`FiniteSplitEtaleHypercover` dependency. The added `lem-weil-pbc-matching-object-proper-faces`
statement dependency is used literally by `U.properFaceDiagram` and is already landed.

Edge cases checked: degree zero has the empty proper-face diagram and identity matching object;
degree one has the two vertex faces; higher degrees include all injective proper faces. Empty
schemes and empty terms remain allowed, with surjectivity having its usual behavior. No
characteristic or nonempty-scheme condition is present, and all universes are explicit.

Searches found no existing declaration in Mathlib, `WeilConjectures`, or `lean/Sheaf`; LeanFinder,
Loogle, LeanSearch, and repository grep searches are recorded in `searches.jsonl`. The only
related Mathlib result is the documented TODO about preservation of limits by
`FormalCoproduct.incl`; no theorem states this matching result. `lcompile.py` compiles the
module with only its intentional `sorry` proof.
