## Worker report

States `CategoryTheory.fppf_stack_algebraicity_bootstrap` in
`Sheaf.AlgebraicGeometry.FppfStackAlgebraicityBootstrap`. Its only theorem has
`by sorry`; no definition or proof is added. The seven-step proof docstring follows
all seven DAG proof steps, including the diagonal bootstrap rather than a diagonal
assumption. Source checked directly: `literature/stacks-project/criteria.tex`,
Tag 06DC (`theorem-bootstrap`), lines 2829 onward, and Tag 05XW.

Clause-by-clause correspondence:

- Base scheme and size convention: `{S : Scheme.{u}}`; the scheme universe is `u`.
  `Y : BasedCategory.{v, w} (Over S)` permits independent hom and object universes
  for the total groupoid. All three levels are explicitly bound; `autoImplicit` is false.
- A stack in groupoids on the big fppf site: `hstack : IsFppfModuliStack Y`.
  This existing predicate includes `IsFibredInGroupoids`, then effective descent and
  unique arrow gluing for each sieve covering in `Scheme.fppfTopology.over S`.
  It is the total-category version of the pseudofunctor stack condition used by
  `lem-sfb-groupoid-stackification-local-description`, not a new notion of stack.
- Algebraic-space source: `A : AlgebraicSpace S`; it already includes an fppf sheaf,
  representable diagonal, and a surjective representable etale scheme atlas.
- Morphism of fibred groupoids: `f : BasedFunctor (discreteModuli A.obj.obj) Y`.
  `discreteModuli` retains each section of A and gives discrete fibres; `BasedFunctor`
  is the existing functor over the base. Maps between groupoid fibrations preserve
  cartesian arrows, since all arrows are cartesian.
- Every scheme T and object y of Y(T): the universal binders `T : Over S` and
  `y : BasedFunctor (discreteModuli (yoneda.obj T)) Y`. The fibred Yoneda description
  identifies such a map with an object over T, without discarding automorphisms.
- Representability of `A ×_Y T`: `∃ (Z : AlgebraicSpace S)
  (p : Z.obj.obj ⟶ yoneda.obj T), HasSpaceBaseChange f T y Z p`.
  The reused predicate specifies an equivalence of the actual 2-fibre product with
  Z over T, including its projection. A space over S together with p is exactly
  a space over T. No arbitrary unconnected projection is substituted.
- Flat and locally finitely presented projections, tested on etale scheme charts:
  for every `U : Over S` and `b : yoneda.obj U ⟶ Z.obj.obj`, `AlgebraicSpace.IsEtale b`
  implies `Flat (yoneda.preimage (b ≫ p)).left ∧
  LocallyOfFinitePresentation (yoneda.preimage (b ≫ p)).left`.
  Yoneda inverse gives the actual composite U → T. The two clauses share precisely
  the same representative and projection as `HasSpaceBaseChange`.
- Surjectivity of each projection: `SpaceMapIsSurjective Z T p`. By its existing
  definition, every point t of T is the image of a point of an etale scheme chart
  of Z. This is equivalent to the stated field-extension lifting: apply it to the
  image point of Spec K → T, choose a chart point above that image, and choose
  a common extension of K and the chart residue field over κ(t). The resulting
  chart-valued L-point maps to the original Spec K point after extension. Conversely
  lift Spec κ(t) → T and take a point of an etale scheme chart above the resulting
  field-valued point of Z. Thus no K-rational lift is required.
- Conclusion: `IsAlgebraicModuliStack Y`. Its existing definition is precisely an
  etale stack, algebraic-space diagonal, and a representable smooth surjective
  scheme atlas. Diagonal representability appears only inside the conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category and Hom.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`;
  slice topology is the existing `GrothendieckTopology.over`.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`; read its complete
  signature and docstring. Its stack predicate uses pseudofunctors; the existing
  total-category predicate below supplies the interface matching the conclusion.
- `Sheaf.CategoryTheory.SiteStackification`: `CategoryTheory.IsFppfModuliStack`.
  Its owning landed node `def-sfb-fppf-stackification` is added to `stmt_deps` under
  the rule permitting existing landed notions. No dependency record is changed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `IsFibredInGroupoids`, `HasSpaceBaseChange`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `ModuliTwoIso`, `SpaceMapIsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` (affine-local
  definition with the documented stalkwise equivalence).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.

All already recorded proof modules are plain imports. Not-yet-stated proof prerequisites
are retained in the DAG and the proof docstring; this statement does not require
constructing them. `Mathlib.AlgebraicGeometry.Limits` provides the recorded coproduct
match, and smooth-local-on-source is supplied through the existing smooth module and
Mathlib's locality API. Size convention is metatheoretic, as its record specifies.

Edge cases checked: empty S, empty A, empty Y, empty T and empty covers; no nonemptiness
assumption is added. An empty A cannot cover a nonempty field fibre, as required.
For empty T surjectivity is vacuous and flatness/lfp on empty charts remain valid.
Nonreduced schemes and nontrivial automorphisms in Y remain allowed. No smoothness
of A or of f is assumed. No quasi-compactness, separatedness, finite type of S,
Noetherianity, characteristic restriction or diagonal representability is assumed.
No independent too-small field-test universe is introduced: surjectivity uses scheme
points and residue fields in the scheme universe. The countable coproduct in the
proof is permitted by the fixed size convention.

Searches for reuse (2026-10-24):

- `msearch.py leanfinder`, query “A stack with representable flat locally finitely
  presented surjective algebraic space cover is algebraic”: eight hits, including
  scheme FlatDescent declarations, LocallyOfFinitePresentation and UniversallyOpen.of_flat;
  none states stack algebraicity.
- `msearch.py loogle`, query `"AlgebraicGeometry", "Stack"`: zero hits.
- `msearch.py grep`, query `algebraicStack|flatGroupoid|quotientStack|bootstrap`:
  eight unrelated Mathlib hits (calculus, Jacobson rings, cofiltered systems,
  integral closure, Hall, matroids); no stack bootstrap.
- `msearch.py leansearch`, query “A stack with a representable fppf cover by an
  algebraic space has a smooth scheme atlas”: service unavailable, recorded by the
  wrapper. Other search kinds and direct source searches were used.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for fppf/algebraic/atlas/bootstrap,
  plus this item's id: no matching theorem. Existing SiteStackification,
  AlgebraicStackSetoidSpace, StackChartwiseSmoothEtaleCalculus,
  EtaleSmoothAtlasFppfDescent and AlgebraicModuliStack interfaces were inspected;
  none states this theorem. Existing notions were reused, with no new node needed.

No statement correction or statement dispute. The requested example
`Sheaf.CategoryTheory.CompactObject` is now withdrawn; its recorded replacement
`WeilConjectures.CategoryTheory.CompactObject` was read for the active module conventions.

## Second reading by NP

Independent second reading (maintainer review, 2026-10-24). It replaces the worker's
own final self-check, which said explicitly that it was not an independent reading.

Node clauses against the Lean, each read through the recorded dependency declarations:

1. Scheme S, size convention: `{S : Scheme.{u}}`; Over S has hom universe u, the
   universe of `discreteModuli` presheaves. Correct.
2. Stack in groupoids on (Sch/S)_fppf: `hstack : IsFppfModuliStack Y`
   (def-sfb-fppf-stackification, Sheaf/CategoryTheory/SiteStackification.lean). It is
   `IsFibredInGroupoids Y` plus colimit descent for every sieve of
   `Scheme.fppfTopology.over S`, so Isom sheaves and effective descent. This is the one
   project notion; the added stmt_dep is its landed owner. Correct.
3. Algebraic space A as a discrete fibred groupoid: `A : AlgebraicSpace S`,
   `discreteModuli A.obj.obj`. Correct (same encoding as def-sfb-stable-pointed-moduli-groupoids).
4. f a morphism of fibred groupoids: `f : BasedFunctor (discreteModuli A.obj.obj) Y`. Correct.
5. Representability: for every `T : Over S` and `y` (an object of Y(T) via the
   discreteModuli Yoneda map) there are `Z, p` with `HasSpaceBaseChange f T y Z p`, i.e.
   an equivalence of `discreteModuli Z` with the 2-fibre product T ×_Y A, compatible with
   the projection to T through `p`. This is the body of `IsRepresentableByAlgebraicSpaces`,
   with p specified. Correct.
6. Flat and locally finitely presented, tested on étale scheme charts: for every étale
   `b : h_U → Z`, `Flat` and `LocallyOfFinitePresentation` of the scheme map
   `yoneda.preimage (b ≫ p)`. This is the pattern of the recorded `SpaceMapIsSmooth`/
   `SpaceMapIsEtale` and of the landed StackReducedLocallyNoetherianFppfDescent
   hypothesis. `AlgebraicSpace.SpaceMapIsFppf` is about maps between spaces in
   `AlgebraicSpace S`, not maps to `yoneda.obj T`, so it is not a duplicate. Correct.
7. Surjective: `SpaceMapIsSurjective Z T p` (every point of T is hit by an étale chart
   point). For a space this is equivalent to lifting field points after a field extension
   (residue fields and a common extension). Correct.
8. Same Z and p in all three clauses (one existential). Since Z is determined up to
   equivalence over T, the existential is no weaker than "the" base change.
9. Conclusion: `IsAlgebraicModuliStack Y` = étale stack ∧ algebraic-space diagonal ∧
   smooth surjective representable scheme atlas (def-sfb-algebraic-moduli-stack).
   No diagonal hypothesis is assumed. Correct.

Source: Stacks criteria.tex Tag 06DC (X representable by an algebraic space; F representable,
surjective, flat, locally of finite presentation ⇒ Y algebraic). The Lean has no extra
hypotheses (no quasi-compactness, separatedness, Noetherianity, smoothness of A, or
universe identification beyond Over S's).

Edge cases: empty S/T/A/Y (an empty A forces empty Y fibres through surjectivity; vacuous
otherwise); nonreduced T; nontrivial automorphisms in Y are kept by BasedCategory.

Records: `lean.statement` is verbatim the file signature (checked by substring); node
changes against live are `stmt_deps` (+def-sfb-fppf-stackification, landed by Q27) and
`lean` only. The theorem body is `by sorry`; there are no definitions. The docstrings carry
the source place and blueprint id; the proof docstring follows the 7 DAG steps. All imported
proof modules exist in the live tree.

Searches: rg `06DC|theorem-bootstrap` in lean/Sheaf and lean/WeilConjectures (no hits);
rg for theorems concluding `IsAlgebraicModuliStack` (none states 06DC); rg for `SpaceMapIs*`
(no flat/lfp space-to-scheme predicate exists).

No mismatch was found.
