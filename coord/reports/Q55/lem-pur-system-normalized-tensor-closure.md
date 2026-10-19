## Worker report

The module `Sheaf.Paper.SystemNormalizedTensorClosure` states both closure assertions of
`lem-pur-system-normalized-tensor-closure`. Its two theorem proofs are `sorry`.
`normalized_tensor_closure` states normalization, the actual tensor reduction formula,
and its quotient cocycle. `normalized_inverseImage_closure` states normalization of the
inverse-image system, its actual reduction formula, and its quotient cocycle. The only
helper, `SemilinearDerivedSectionsData.inverseImageGeometry`, is an abbreviation for
`(A.geometric J' uInv uPush adjSet).val`, a projection from the supplied simultaneous
model, with real data and no further choice. It introduces no new mathematical notion.

Hypothesis and clause correspondence:

- The small site is `{C : Type c} [Category.{v} C]` with `J : GrothendieckTopology C`.
  `[EssentiallySmall.{max c v r} C]` is the dependency's coefficient-size convention;
  objects and morphisms have independent universes. It admits every small site.
- The strict inverse sequence is `B : ℕ → Sheaf J CommRingCat.{max c v r}` and
  `τ : ∀ n : ℕ, B (n + 1) ⟶ B n`. Lean level zero denotes the paper's level one;
  this is an index renaming, not an extra coefficient stage. All pairs and triples,
  including equal indices, are quantified with `n ≤ m` and `m ≤ l`.
- `DS J B τ` is the ordinary unbounded derived category of the actual ringed sequence
  site, whose module sheaves are the strict semilinear systems. Its `e` is actual
  derived evaluation. No category of diagrams in derived categories is substituted.
- `Data J B τ` is the simultaneous coefficient/tensor model in the recorded section
  theorem, and `SemilinearDerivedSectionsData J B τ` also supplies its inverse-image
  models. These are presentations of the operations specified in the node. Their
  existence is `semilinearDerivedSections`; they are not extra geometric assumptions.
- `Normalized J B τ A.scalar P` and its analogue for Q are exactly invertibility of
  every actual transition-adjoint. `reduction` is defined by the normalized scalar
  adjunction applied to `derivedTransition`, itself descended from horizontal system
  restrictions. Thus the theorem does not quantify over separately chosen reductions.
- The tensor system T is `A.closed.tensor.obj (P, Q)`. The first conjunct of
  `normalized_tensor_closure` asserts precisely its normalization.
- The second conjunct identifies its actual reduction, followed by
  `(A.tensorEvaluation n).hom.app (P, Q)`, with scalar extension of the level-m
  evaluation, then `(A.scalarTensor h).hom.app (P_m, Q_m)`, then
  `(A.levelClosed n).tensor.map (Prod.mkHom (reduction ... P) (reduction ... Q))`.
  This is the node's displayed two-arrow composite, with the necessary evaluation
  identifications written explicitly on both sides. The first arrow is the canonical
  comparison: `Data.scalarTensorModel` fixes it on K-flat representatives and ordinary
  pure tensors. The statement uses that comparison, not an arbitrary isomorphism.
- The third conjunct is the actual quotient cocycle on T: scalar extension of its
  l-to-m reduction followed by its m-to-n reduction equals
  `(A.scalarComposition h k).hom.app (T_l)` followed by its l-to-n reduction.
- The topos morphism is `uInv`, `uPush`, `adjSet : uInv ⊣ uPush` and
  `[PreservesFiniteLimits uInv]`, on sheaves of sets of the two small sites.
  No site-functor presentation or extra continuity assumption is imposed.
- For the inverse-image assertion, `A.inverseImageGeometry ...` projects the geometry
  supplied by `A.geometric`. Its `coefficients`, `coefficientTransition`, and
  `inverseImage` are precisely C_n = v-inverse-image B_n and the induced transitions:
  `GeometryBase.coefficient_compatibility` fixes those maps on underlying sheaves.
  The inverse-image system is `G.pull.mapDerivedCategory.obj P` for this geometry G.
- The first inverse-image conjunct states normalization using `G.target.scalar`.
  Its second conjunct uses the same actual `reduction`, and identifies it, under
  `G.pullEvaluation`, with `G.coefficientPullback.inv` followed by
  `derivedExact ... .map (reduction ... P)`. This has the orientation in the node:
  S(v-inverse-image P_m) maps to v-inverse-image(T(P_m)), then to v-inverse-image P_n.
  `Geometry.coefficientPullback_transpose` fixes this comparison by the actual
  scalar-adjunction transpose of the identity-on-underlying-sheaves restriction map.
- The last conjunct writes the quotient cocycle on that actual inverse-image system,
  with its target scalar associator. These are equations of constructed derived
  morphisms; no inference that evaluation detects equality is made.
- There is no boundedness or flatness hypothesis in either theorem. `DS` is unbounded;
  the scalar data uses `DerivedChangeOfRingsCochainModel` and its K-flat computations
  for arbitrary maps of coefficient rings. There is no surjectivity assumption:
  the term quotient cocycle denotes the reduction compatibility of the node even
  for its stated arbitrary strict tower.

Recorded dependencies opened and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the dependency's site convention;
  actual sheaves here use its retained Mathlib `GrothendieckTopology`/`Sheaf` interface.
- `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and
  `SemilinearDerivedSectionsData`: the full simultaneous model. Its publicly imported
  `SemilinearSystemModels` supplies `Systems`, `DS`, `e`, `ScalarData`, `reduction`,
  `Normalized`; `SemilinearDerivedCalculus` supplies `Data`, `scalarComposition`,
  `scalarTensor`, `tensorEvaluation` and their representative normalizations.
  `SemilinearGeometryDerived` supplies `Geometry`, `coefficientPullback`,
  `pullEvaluation`; `SemilinearGeometryOps` supplies `PullTransitionFormula`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` and
  `DerivedChangeOfRingsCochainModel`: public through the section model; its `T`,
  normalized counit, and K-flat computation are the scalar-data interface used here.
- Proof dependency imported without `public`:
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its full signature and proof docstring fix the generic comparison by the canonical
  K-flat total-tensor square. No duplicate dependency module is necessary.

Sources read: `sites-cohomology.tex`, the lemmas `lemma-K-flat-resolution` (06YS) and
`lemma-pullback-tensor-product` (07A4), including their proofs; the current blueprint's
`prop-pur-adic-reconstruction-trace-coherence` statement and proof, and the node's four
strict-system proof steps. Each theorem docstring gives its complete natural-language
proof using these dependencies. Neither statement requires a correction or dispute flag.

Edge cases checked before and during writing: zero P or Q; the zero coefficient ring;
constant towers and identity transitions; m = n and l = m = n; towers with non-flat maps,
for example integer coefficients reduced modulo a nonzero nonunit; arbitrary unbounded
complexes; an empty site; and identity as well as general inverse-image functors.
None is excluded by the signatures. In particular no cancellation of ring maps, ordinary
underived tensor computation, positive truncation, or evaluated-K-injective assumption
was introduced.

Searches made with `msearch.py Q55 lem-pur-system-normalized-tensor-closure`:

- LeanFinder: `normalized semilinear systems closed under derived tensor product and
  inverse image`. Eight hits about tensor images, equalizers and finitely generated
  submodules; no matching derived-system closure statement.
- LeanSearch: `normalized systems of modules closed under derived tensor product`.
  Eight hits including ModuleCat monoidal closedness, directed tensor systems,
  AB4-star, and PiTensorProduct; no matching derived-system closure statement.
- Loogle: `CategoryTheory.Functor.map_isIso`. Returned the expected functorial
  preservation of isomorphisms and related categorical lemmas; useful proof tools,
  not a match for the geometric/derived-system statement.
- Mathlib grep: `Normalized.*tensor|tensor.*Normalized|semilinear` in CategoryTheory.
  Zero hits.
- Source/project `rg`: `normalized.*tensor|tensor.*normalized`, then the narrower
  `Normalized.*tensor|tensor.*Normalized|normalized_tensor|normalized_pull`, in
  `WeilConjectures` and `lean/Sheaf` (Paper for the narrower pass). Hits concern Picard
  normalization, tensor models, and other coefficient constructions, not this closure.
- Source `rg` for the exact node id returned no declaration. The new declaration
  names were also searched in Mathlib, upstream Lean, the side library, and
  `dag/lean_names_upstream.json`; no collisions were found.

Validation: every module of this delivery is compiled separately through `scompile.py`;
`deliver2.py --no-push` runs the required server preflight and compile before delivery.
The final outcomes are recorded below when those checks finish.

The final explicit `scompile.py` check succeeded without warnings or errors in both
sandbox and library-module passes. The node copy differs from the original only in
`lean`; its primary statement is the verbatim declaration signature. Both expected
postponed proofs belong to this node, and every line of the module is at most 100
characters. The initial long-line warning was repaired before the clean check.

## Second reading by Q55

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
