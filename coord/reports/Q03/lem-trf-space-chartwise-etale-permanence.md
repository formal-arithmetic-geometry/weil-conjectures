## Worker report

The module `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` states the entire node as the eight conjuncts of `AlgebraicGeometry.AlgebraicSpace.chartwise_etale_permanence`. Its only proof is `sorry`. The original node statement is unchanged. No new notion, new node or private copy is introduced.

Clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; all algebraic spaces are `AlgebraicSpace S`. Universe `u` is the existing big-site universe; family indices have arbitrary explicit universes `w` and `v`, with composite indices `Sigma J` in their maximum.
- The phrase “call chartwise etale” is the existing `IsChartwiseEtale`, whose full definition quantifies over every `T : Over S` and every map `a : yoneda.obj T ⟶ X.obj.obj`, requiring `IsEtale a → IsEtale (a ≫ f.hom.hom)`. Here existing `IsEtale` means representability with etale scheme projections, not the chartwise property. Its `IsRepresentableWith` definition uses actual Yoneda pullback squares.
- Scheme source: the first conjunct quantifies over every scheme over S, `T : Over S`, every target Y and every `f : schemeSpace T ⟶ Y`, and concludes `IsChartwiseEtale f ↔ IsEtale f.hom.hom`. `schemeSpace T` is the canonical fppf Yoneda sheaf of T, rather than an arbitrary surrogate or extra representability assumption.
- Identity: the second conjunct is `∀ X, IsChartwiseEtale (𝟙 X)`.
- Composition: the third conjunct quantifies over every composable pair and assumes exactly its two chartwise-etale hypotheses, concluding chartwise etaleness of `f ≫ g`.
- Arbitrary base change: the fourth conjunct takes any `f : X ⟶ Z` and `g : Y ⟶ Z`, assumes chartwise etaleness only of f, and concludes it for `enlargedFibreProductFst g f`. The first projection from Y ×_Z X is precisely the base change of f.
- Maps over a common base: the fifth conjunct has `g : X ⟶ Z`, `h : Y ⟶ Z`, `f : X ⟶ Y`, hypotheses `IsChartwiseEtale g`, `IsChartwiseEtale h`, and the triangle `f ≫ h = g`, concluding `IsChartwiseEtale f`.
- Etale coverings are always written as the pair `(∀ i, IsChartwiseEtale (f i)) ∧ IsJointlySurjective (fun i ↦ (f i).hom.hom)`. This expands precisely the node's definition; in particular no representable-etale hypothesis is inserted.
- Singleton isomorphisms: the sixth conjunct quantifies over every isomorphism e, asserting chartwise etaleness and joint surjectivity of the constant Unit-indexed family. Its first condition is the memberwise etaleness condition for that singleton.
- Composite coverings: the seventh conjunct uses arbitrary `I`, dependent `J : I → Type v`, spaces `Xᵢ` and `Xᵢⱼ`, the actual maps f and g, the cover of X and every cover of Xᵢ, and concludes the same two conditions for `g a.1 a.2 ≫ f a.1` indexed by `Sigma J`.
- Pullback coverings: the eighth conjunct takes any cover f and arbitrary g into its target, and concludes both covering conditions for the first projections from `enlargedFibreProduct g (f i)`.
- These are actual sheaf fibre products: `enlargedFibreProduct` is `⟨Limits.pullback f.hom g.hom, (fibreProduct_isAlgebraicSpace ...).1⟩`, and its projection is `ObjectProperty.homMk (Limits.pullback.fst ...)`. No arbitrary cone or comparison map is assumed.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, with their locally ringed-space and local-affineness signatures.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsAlgebraicSpace`, and `isEtale_comp`. Spaces are the full subcategory of fppf sheaves with representable diagonal and a surjective etale atlas. Morphisms have underlying presheaf map `f.hom.hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`, expanded on every field-valued section with a lift after a field extension.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`: `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and `etale_fibreProduct_isScheme`. Only the closure result is needed for arbitrary chartwise maps: the older cover lemma assumes representability.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: existing `IsChartwiseEtale`, `schemeSpace`, `enlargedFibreProduct`, `enlargedFibreProductFst`. The full definitions and supporting proof signatures/docstrings were read. Its existing composition lemma and site-object base-change lemma are partial matches, not the full eight-clause result.
- `def-weil-size-convention` is a metatheoretic convention, with no object to import; its explicit universe convention is honored.
- The statement module retains only imports needed to elaborate the stated objects and predicates. Proof-only imports from the earlier attempt (`EtaleDescentThroughSourceCover` and several scheme morphism modules) were removed because the theorem proof is `sorry`; this also avoids pulling an unrelated stale compiled artifact during delivery. `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` is retained for the displayed fibre-product projection.

Edge cases checked before writing: empty spaces; empty I; empty dependent J i (which can cover only an empty point set); identity and isomorphism maps; arbitrary nonrepresentable chartwise-etale morphisms; arbitrary base changes; no separation, finite-type, quasi-compactness or Noetherian assumption; field extensions remain in the site's universe. Scheme-source cancellation is not confused with cancellation of the other arrow. No node fault or mathematical dispute was found.

Sources read: local Stacks `spaces-properties.tex`, definition-etale and the paragraph after it, lemma-composition-etale, lemma-base-change-etale, lemma-etale-permanence (03FR, 03FT, 03FU, 03FV); `spaces-topologies.tex`, definition of covering and lemma-etale (041F), all three clauses. The theorem docstring carries all ten proof steps of the node.

Searches (msearch.py Q03 / this item): LeanFinder query “Etale morphisms of algebraic spaces defined on scheme charts are stable under composition and arbitrary base change” returned eight scheme-only results, principally IsEtale.of_comp and the scheme base-change instance; Loogle query `"AlgebraicSpace", "Etale"` returned zero hits; Mathlib grep `ChartwiseEtale|chartwise.*etale|AlgebraicSpace` under AlgebraicGeometry returned zero hits. LeanSearch query “Chartwise etale algebraic spaces covering families stable under composition and base change” returned eight scheme-site and general-precoverage results, no algebraic-space result. Direct rg of the source project and side Lean for `ChartwiseEtale|chartwise|lem-trf-space-chartwise-etale-permanence` found only the existing enlarged-site predicate and partial permanence results there; no complete match. Mathlib source declarations were then opened to distinguish their scheme-only scope.

Import-cycle note: the enlarged-site node has this item as a proof dependency, but its module currently does not import this module. We reuse its already published definitions instead of making duplicate notions. The maintainer must omit a future proof-only reverse import into EnlargedEtaleRingedSite, by the explicit import-cycle exception in stages/2-statements.md section 3(7). No DAG edge to the downstream enlarged-site node is added, avoiding a DAG cycle. The used definitions themselves are independent of its permanence theorems.

Validation is recorded below after the compile and delivery dry run.

Repair validation (2026-10-18): the initial dry run reproduced the saved packet's artifact error while compiling the proof-only import `EtaleDescentThroughSourceCover`: `cannot import non-module Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint from module`. Because this stage states the theorem with a `sorry` proof, those proof-only imports were unnecessary. After removing them, `scompile.py Q03 lem-trf-space-chartwise-etale-permanence lean/Sheaf/AlgebraicGeometry/ChartwiseEtalePermanence.lean` compiled both sandbox and library checks cleanly (2.0 seconds each, no warnings or errors). The required `deliver2.py ... --no-push` dry run then passed preflight and compilation, producing commit `ac11825cf5`; no statement or dependency field was changed.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
