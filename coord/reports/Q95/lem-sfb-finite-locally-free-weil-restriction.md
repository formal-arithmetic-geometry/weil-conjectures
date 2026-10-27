## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeWeilRestriction` states
`AlgebraicGeometry.AlgebraicSpace.exists_finiteLocallyFree_weilRestriction`, with
one postponed theorem proof and no new definitions. The source read was
`literature/stacks-project/criteria.tex`, proposition-restriction-of-scalars-algebraic-space
(Tag 05YF) and lemma-fibre-diagram (Tag 05YE), including their proofs. The theorem
specializes the source's intermediate algebraic spaces Z and B to the schemes Z and T,
exactly as the assigned node requires. No statement correction is needed.

Hypothesis and clause correspondence:

- The base scheme S is `{S : Scheme.{u}}`; `universe u` and `autoImplicit false`
  make the size convention explicit. Scheme objects have universe u+1 and morphisms
  universe u; the existing algebraic-space interface uses `Type u`-valued presheaves.
- Z and T are S-schemes, written `(Z T : Over S)`. The S-morphism is `(p : Z ⟶ T)`.
- Finite locally freeness is `[Scheme.Hom.IsFiniteLocallyFree p.left]`, the recorded
  upstream class extending finite, flat, and locally of finite presentation. There is
  no degree parameter, constant-rank hypothesis, positivity hypothesis, or surjectivity
  assumption on p.
- `(E : AlgebraicSpace S)` uses the existing full subcategory of big fppf sheaves
  with representable diagonal and an etale surjective scheme atlas.
- The given map E to Z is `(q : E.obj.obj ⟶ yoneda.obj Z)`. Morphisms of algebraic
  spaces are natural transformations; this is the same map to the actual scheme
  representable underlying `schemeSpace Z`, without choosing a different model.
- The conclusion `∃ (R : AlgebraicSpace S) (r : R.obj.obj ⟶ yoneda.obj T)` is an
  algebraic space with its structure map to T. This is an algebraic space over T
  expressed in the slice of algebraic spaces over S.
- For each S-scheme U and S-map `a : U ⟶ T`, the left side of the equivalence `e U a`
  is `{x : R.obj.obj.obj (op U) // r.app (op U) x = a}`, precisely the points over a.
- The right side is the subtype of natural transformations
  `b : yoneda.obj (Limits.pullback p a) ⟶ E.obj.obj` satisfying
  `b ≫ q = yoneda.map (pullback.fst p a)`. This is precisely
  `Hom_Z(Z ×_T U, E)`. Pullbacks in `Over S` are the scheme fibre products with
  their induced S-structure. Yoneda identifies the indicated natural transformations
  with scheme-test maps to E.
- The final universal equality, for `v : V ⟶ U`, identifies restriction of a point
  with precomposition of its corresponding b by the canonical base-change map.
  `pullback.map p (v ≫ a) p a (𝟙 Z) v (𝟙 T) ...` is exactly
  `Z ×_T V → Z ×_T U`, with projections the identity on Z and v on the test scheme.
  The points x and y are quantified in the respective fibres; the premise
  `R.obj.obj.map v.op x.val = y.val` specifies the restriction. Such a y always
  exists by naturality of r. Thus the equality expresses full naturality, not an
  extra condition on the input, and the fibrewise equivalences form the required
  natural isomorphism on S-schemes over T.
- There are no separation, quasi-compactness, flatness, or finite-presentation
  assumptions on E to Z. E and q are completely arbitrary of their indicated types.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  their full structure signatures and documentation were read in the pinned source.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, lines 890--900, and the adjacent
  `IsFiniteLocallyFreeOfDegree` for comparison (the degree class is not imposed).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, and `IsRepresentableWith`, with their sheaf,
  diagonal, atlas and natural-transformation definitions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `Limits.pullback`, `pullback.fst`, and `pullback.map`, with full signatures and
  universal-property documentation. These are used in `Over S`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and the two other recorded clauses
  were read; this statement dependency is publicly imported and its closure result
  is step 3 of the postponed proof.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicSpace.schemeSpace` and `schemeSheaf_isAlgebraicSpace`; their actual
  representable-sheaf construction was read and the module is a plain proof import.
- `def-weil-size-convention` has a convention record rather than a definition;
  its requested universe bookkeeping is implemented by the explicit universe.
- The proof dependency `lem-sfb-finite-locally-free-relative-hom-space` currently
  has no lean record. Its full mathematical statement was read and is cited in
  the proof docstring; no unstated declaration is imported. It is a proof input,
  not a notion required to elaborate this statement. A server-source query for
  `Sheaf.AlgebraicGeometry.FiniteLocallyFreeRelativeHomSpace` also reported source
  unavailable. Its future module import is left to the maintainer when it lands,
  as required by stages/2-statements.md rule 7.

Edge cases checked before writing:

- If p has rank zero (Z empty), every base change is empty; its unique map to E
  satisfies the equation over Z, and the restriction is terminal over T.
- Rank may change between open-and-closed pieces of T; no fixed rank is encoded.
- T or S may be empty; all quantification is over their actual scheme slices,
  with no nonemptiness assumptions.
- For p the identity, the functor is the original space E over T, up to the
  canonical pullback identity comparison. For an identity test morphism, the
  naturality equation is ordinary identity restriction.
- An empty E is permitted; over positive-rank tests the fibre can be empty, while
  over rank-zero tests it is a singleton. No point existence is assumed.
- The test category and morphism universes are the existing interface universes;
  an independently smaller test universe is not introduced.

Searches actually made (all msearch invocations used group Q95 and this item):

- leanfinder: `Weil restriction of algebraic spaces along a finite locally free
  morphism is an algebraic space`: eight results, about scheme finiteness,
  finite-presentation and stability under base change; none is Weil restriction.
- loogle: `AlgebraicGeometry.WeilRestriction, AlgebraicGeometry.AlgebraicSpace`:
  zero hits; unknown identifier `AlgebraicGeometry.WeilRestriction`.
- grep: `WeilRestriction|weilRestriction|RestrictionOfScalars`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- leansearch: `Weil restriction of an algebraic space along a finite locally free
  morphism is an algebraic space`: eight unrelated scheme restriction and finite
  morphism results, none states the assigned proposition.
- rg over both `lean/WeilConjectures` and `lean/Sheaf`:
  `WeilRestriction|weilRestriction|finiteLocallyFreeRelativeHom|relativeHomSpace|` plus
  the item id: only unrelated constant Weil-structure restriction-unit and
  Weil-kernel inertia declarations; no geometric Weil restriction or duplicate
  theorem. A broader search for restriction-of-scalars terminology found module
  scalar restriction, not the geometric functor here.

Validation: the first compiler run found the namespace collision between
`AlgebraicSpace.pullback` (module pullback) and categorical `Limits.pullback`.
The categorical object is now explicitly qualified. The corrected module passed
both sandbox and final-module scompile checks with no errors or warnings.
No node faults or statement disputes were found. The node copy changes only `lean`.


## Second reading by Q95

Clause-by-clause reading of the node, the source and the module
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeWeilRestriction` (written at maintainer review,
replacing the worker's self-check, which was not an independent reading).

Source read: `criteria.tex` lines 1674-1712, Tag 05YE (lemma-fibre-diagram) and Tag 05YF
(proposition-restriction-of-scalars-algebraic-space): for `X → Z → B` morphisms of algebraic
spaces over `S` with `Z → B` finite locally free, `Res_{Z/B}(X)` is an algebraic space. No other
hypothesis; the node specializes `Z, B` to schemes `Z, T`.

1. Scheme `S`, size convention: `{S : Scheme.{u}}`, `universe u`; the test category `Over S`
   has objects in `Type (u+1)`, Homs in `Type u`, matching the `AlgebraicSpace S` interface
   (`(Over S)ᵒᵖ ⥤ Type u` fppf sheaves). Correct; no extra universe.
2. `p : Z → T` finite locally free S-map, rank arbitrary or zero: `(Z T : Over S) (p : Z ⟶ T)
   [Scheme.Hom.IsFiniteLocallyFree p.left]`; this is the recorded lean of def-pc-finite-locally-free
   (`IsFinite ∧ Flat ∧ LocallyOfFinitePresentation`, FiberDegree.lean l.899), not the degree
   class. Correct, no stronger.
3. `E` an algebraic space over `S` with `E → Z`: `(E : AlgebraicSpace S)
   (q : E.obj.obj ⟶ yoneda.obj Z)`; morphisms of algebraic spaces are natural transformations
   (def-trf-algebraic-space), and `yoneda.obj Z` is the presheaf `h_Z`. No property of `q`.
   Correct.
4. Functor `R(U → T) = Hom_Z(Z ×_T U, E)`: the subtype
   `{b : yoneda.obj (pullback p a) ⟶ E.obj.obj // b ≫ q = yoneda.map (pullback.fst p a)}`;
   pullbacks in `Over S` are scheme fibre products with induced S-structure; by Yoneda `b` is a
   point of `E` on `Z ×_T U`, and the equation says it lies over `Z` via `pr_Z`. Correct
   (`Z`-first order as in the node).
5. Restriction by precomposition with base change: the final clause, for `v : V ⟶ U`, says that
   if `y` is the restriction of `x`, then `e(y) = yoneda.map (pullback.map p (v ≫ a) p a (𝟙 Z) v
   (𝟙 T) _ _) ≫ e(x)`; `pullback.map … : Z ×_T V ⟶ Z ×_T U` is `𝟙_Z × v`. Together with the
   fibrewise equivalences this is exactly a natural isomorphism of functors on S-schemes over T.
   Correct.
6. Conclusion "algebraic space `R` over `T`": `∃ (R : AlgebraicSpace S) (r : R.obj.obj ⟶
   yoneda.obj T)`, with points over `a` the fibres `{x // r.app _ x = a}`. An algebraic space over
   `T` is an algebraic space over `S` with a map to `h_T`; correct.
7. "No separation, quasi-compactness, flatness or finite-presentation on `E → Z`": none imposed.

Edge cases: `Z = ∅` (rank 0): every fibre of the functor is a singleton, `R = T`, allowed;
variable rank: no degree encoded; `S`, `T`, `E` empty: no nonemptiness assumption;
`p = 𝟙`: functor is `E`; `v = 𝟙`: naturality reduces to the identity restriction.

One definition per notion: no `WeilRestriction`/`Res`/relative-Hom space declaration in Mathlib,
`lean/Sheaf` or `lean/WeilConjectures` (rg `eilRestriction|relativeHomSpace|RestrictionOfScalarsSpace`:
only unrelated constant-Weil-structure hits); live node `lean` is null; the proof dependency
lem-sfb-finite-locally-free-relative-hom-space has no lean record and is correctly not imported.

Hygiene: module docstring and theorem docstring carry Tags 05YF/05YE and
`(blueprint: lem-sfb-finite-locally-free-weil-restriction)`; the theorem docstring carries the
node's three proof steps; proof is `sorry`; no new definitions; `lean.statement` is verbatim the
file signature. No change to the Lean or node record.
