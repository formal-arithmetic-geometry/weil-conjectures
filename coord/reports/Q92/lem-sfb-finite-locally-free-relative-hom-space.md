## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeRelativeHomSpace` states
`AlgebraicGeometry.AlgebraicSpace.exists_finiteLocallyFree_relativeHomSpace`.
It has one postponed theorem, with the full ten-step proof plan from Stacks
criteria.tex, Tag 05Y7. No statement correction is needed.

Clause-by-clause correspondence:

- `S : Scheme.{u}` fixes the base and the size convention. The existing algebraic-space
  interface uses sheaves of `Type u` on `Over S`; schemes have object universe `u+1`
  and morphism universe `u`. All tests and witnesses use this same existing bound.
- `Z T : Over S` and `p : Z ⟶ T` are exactly the source, target, and morphism of
  S-schemes. `[p.left.IsFiniteLocallyFree]` is the recorded finite, flat, locally
  finitely presented predicate. It imposes no degree or constant-rank condition.
- `X : AlgebraicSpace S` and `f : X ⟶ schemeSpace T` give the arbitrary target and
  its specified morphism to T. There is no additional condition on this morphism.
- `relativeSpaceHomPairs p f U` is the dependent sum over `a : U ⟶ T` of sections
  `b` of X on `Limits.pullback a p`, satisfying
  `f.hom.hom.app ... b = Limits.pullback.fst a p ≫ a`.
  Yoneda identifies those sections with actual maps from the scheme fibre product
  to X. The equation is precisely `f ∘ b = a ∘ pr_U`, with Lean's diagram order.
- `relativeSpaceHomBaseChange p v a' a q` is `pullback.map` on `(v,id_Z,id_T)`.
  Its equality argument `q : a' = v ≫ a` allows the two dependent fibres to be
  compared without introducing an implicit cast. Its data are the canonical
  pullback map, not an arbitrary chosen map.
- `∃ H h e` gives an algebraic space H over S, its structural map to T, and
  equivalences on every S-scheme U with the stated pair type. Thus H is over T.
- The first conjunct identifies the first pair component with evaluation of h.
- The second conjunct says that restriction along v changes a to `v ≫ a` and
  changes b by X's restriction along the canonical `V ×_T Z → U ×_T Z`.
  These are exactly the naturality equations for the pointwise equivalences e,
  so the conclusion is a natural isomorphism, not just unrelated bijections.
  The witness q is proof irrelevant; the base-change map is fixed by pullback.map.
  Identity and composition are those of pullbacks and the existing presheaf X.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (finite, flat, lfp).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and its full-subcategory sheaf morphisms.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace`, retaining the actual Yoneda sheaf.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `pullback.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; imported publicly through EnlargedEtaleRingedSite.
  Scheme pullbacks in Over S are used for the scheme source; no new space
  fibre-product construction is introduced.
- `def-weil-size-convention` is metatheoretic and has no declaration, as its record says.

Recorded proof dependencies with published modules are imported without `public`:
AlgebraicSpaceFpqcSheaf, FiniteLocallyFreeDegreeLocallyConstant,
FiniteLocallyFreePrincipalBasisCover, AffineFiniteFreeHom, AlgebraicSpaceCoproduct,
AlgebraicSpaceOpenGluing, AlgebraicSpaceAffineEtaleCover. Mathlib permanence and
covering dependencies are provided by the stated Mathlib imports and FiberDegree.
The proof-only nodes lem-sfb-etale-sections-finite-locally-free,
lem-sfb-finite-etale-cover-local-sections, lem-sfb-fppf-space-atlas-bootstrap, and
lem-sfb-fppf-local-algebraic-space currently have neither Lean modules nor Mathlib
matches; their proof imports cannot yet be added. They are not needed to type the
statement. They remain explicitly named in the proof docstring.

Edge cases checked before writing: if p has rank zero, all its test pullbacks are
empty and there is a unique b, hence H is T. Empty U gives the unique pair. If X is
empty and p has variable rank, the pair functor is supported on the rank-zero locus;
no nonemptiness assumption is introduced. For p the identity, the functor is X with
its given structural map. Nonseparated, non-quasi-compact and non-finitely-presented
X are allowed without change. The test category includes every S-scheme in the
chosen bound, not just affine or étale tests.

Searches for an existing statement (2026-10-24):

- msearch leanfinder: "The relative Hom functor from a finite locally free scheme to
  an arbitrary algebraic space is an algebraic space". Eight hits, finite-morphism
  pullback stability and affine-space results; none states the result.
- msearch loogle: `"AlgebraicSpace", "Hom"`: zero hits.
- msearch leansearch: "The presheaf of pairs of a map to T and a map from its fibre
  product with a finite locally free scheme to an algebraic space is an algebraic
  space": eight hits, general presheaf/sheaf and scheme-pullback declarations;
  no relative Hom algebraicity.
- msearch grep, Mathlib AlgebraicGeometry:
  `WeilRestrict|weilRestrict|relativeHom|relativeSpaceHom`: zero hits.
- rg in project Sheaf and WeilConjectures for relative Hom and Hom functors found
  `RelativeMorphismsPresheaf` and `AffineFiniteFreeHom`. These require a scheme
  target; they do not provide this arbitrary algebraic-space statement. The affine
  theorem is retained as a proof import. ConstantWeilRestrictionUnitMap concerns a
  sheaf-theoretic Weil structure, not the geometric relative Hom functor.
- grep/rg for this blueprint id, the new declaration names, and relevant patterns
  in WeilConjectures, Sheaf, and dag/lean_names_upstream.json found no duplicate.

The helpers are constructions explicitly belonging to the item's own functor,
listed in lean.declarations, not independent missing notions. Both have real data.
The theorem's proof is `sorry` as required in stage 2. No node fault or disputed
statement was found. The cited local Stacks source was read at equation-hom-functor
and proposition-hom-functor-algebraic-space.

## Second reading by Q92

Independent second reading by the maintainer's stage-2 reviewer (the delivered section
was a self-review by the author and is replaced here, delivery-errors H11). Read the
item node, its source (Stacks criteria.tex Tags 05Y2 and 05Y7), the seven stmt_dep
records, the delivered module, and the declarations it uses in the live tree.

Node clauses and their Lean rendering:

1. Scheme S in the universes of the size convention: `{S : Scheme.{u}}`; tests are
   `Over S` (objects in `u+1`, morphisms in `u`) and algebraic spaces are
   `AlgebraicSpace S` = full subcategory of `Sheaf (Scheme.fppfTopology.over S) (Type u)`
   satisfying `IsAlgebraicSpace` (record of def-trf-algebraic-space). No extra
   universe equation. Correct.
2. Finite locally free `p : Z → T` of S-schemes, variable rank and rank zero allowed:
   `(Z T : Over S) (p : Z ⟶ T) [p.left.IsFiniteLocallyFree]`; the class (FiberDegree.lean,
   def-pc-finite-locally-free record) extends `IsFinite`, `Flat`,
   `LocallyOfFinitePresentation` and carries no degree. Correct, not stronger.
3. Schemes as algebraic spaces: `schemeSpace T` = the actual Yoneda sheaf
   `(fppfTopology.over S).yoneda.obj T` (def-trf-scheme-algebraic-space record). Correct.
4. Arbitrary X with `f : X → T`: `(X : AlgebraicSpace S) (f : X ⟶ schemeSpace T)`, no
   condition on f or X (no separation, qc, flatness, fp). Correct.
5. `H_{Z,X/T}(U)`: `relativeSpaceHomPairs p f U` = Σ `a : U ⟶ T`, sections `b` of X on
   `pullback a p` (= U ×_{a,T} Z in Over S, i.e. the scheme fibre product with its
   S-structure, def-pc-fibre-product) with `f(b) = pullback.fst a p ≫ a`, which is
   `f ∘ b = a ∘ pr_U` read through Yoneda. Exact.
6. Restriction along `v : V → U`: `(a ∘ v, b ∘ (v ×_T id_Z))`. `relativeSpaceHomBaseChange`
   is `pullback.map … v (𝟙 Z) (𝟙 T)`, the canonical map, with an equality argument
   `a' = v ≫ a` to avoid casts. Real data, not arbitrary.
7. Conclusion: `∃ H : AlgebraicSpace S, h : H ⟶ schemeSpace T` (H over T),
   `e U : H(U) ≃ H_{Z,X/T}(U)` for every S-scheme U; clause 1 `(e U c).1 = h(c)` is the
   structural map sending (a,b) to a; clause 2 is naturality: the first component of
   the restricted pair is `v ≫ a` and its second component is X's restriction of b
   along the canonical base-change map. Together with clause 1 these determine the
   Σ-equality, so `e` is a natural isomorphism of functors of points. Neither weaker
   nor stronger than the node.

Edge cases: rank zero (pullbacks empty, unique b, H = T), U empty (unique pair),
X empty with variable rank (functor supported on the rank-zero locus; no nonemptiness
assumed), p = id (H = X), non-affine and non-qc tests (all of Over S). All covered.

One definition per notion: `relativeMorphismsPresheaf` (def-sfb-relative-morphisms-
presheaf) and `exists_affine_finite_free_hom` (lem-sfb-affine-finite-free-hom) require
a scheme target X over S; they cannot render an arbitrary algebraic-space target over T.
The two helpers belong to the item's own functor and are listed in lean.declarations.
No existing relative-Hom space statement found in Mathlib or Sheaf/WeilConjectures.

Gates: helpers have real data; the theorem is `by sorry`; module and declaration
docstrings carry the source place and `(blueprint: …)`; the theorem docstring carries
the ten proof steps; `lean.statement` is verbatim in the file; the node record
differs from live only in its `lean` field; all imported modules exist in the live
tree. No changes to the Lean or the node were needed; only this section was rewritten.
