## Worker report

The delivery states `AlgebraicGeometry.relativeCoefficientWindow_twoOpenLocality` in
`Sheaf.AlgebraicGeometry.RelativeCoefficientWindowTwoOpenLocality`, with `sorry` as its
entire proof. It adds the definition module
`Sheaf.AlgebraicGeometry.RelativeCoefficientWindowApproximation`. All six declarations
in that module contain real constructions; there are no additional postponed theorems.
The item's statement, proof, and proof dependencies are unchanged. Its statement
dependencies gain the definition node described below.

Source read: `literature/stacks-project/perfect.tex`, lines 7545–7560, the lemma labelled
`lemma-flat-proper-pseudo-coherent-direct-image-general` (Tag 0CSD) and the unnumbered
paragraph after it. The paragraph asserts proper direct image preserves relative
pseudo-coherence and cites Kiehl. It does not state this approximation or locality lemma.
The node explicitly supplies an agent-written prerequisite and proof, with the primary
Kiehl descente source WANTED. The module retains that attribution. No source correction
or STATEMENT-DISPUTED flag is needed. The supplied proof actually establishes P(W) for
arbitrary quasi-compact W, which implies the conditional locality assertion and explains
why its three approximation premises need not enter that proof.

Hypothesis and clause correspondence:

- Commutative rings B and A: `B A : CommRingCat.{u}`. Noetherian B:
  `[IsNoetherianRing B]`. Arbitrary ring map: `b : B ⟶ A`.
- Separated finite type Y over Spec B: `f : Y ⟶ Spec B`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, `[QuasiCompact f]`. The last two classes together are
  finite type, not finite presentation and not properness.
- Quasi-compact open subschemes U,V: `U V : Y.Opens`, with `IsCompact (U : Set Y)`
  and the corresponding condition on V. Their scheme inclusions are `U.ι`, `V.ι`.
- P(U), P(V), P(U intersection V): the three hypotheses `hPU`, `hPV`, `hPUV` use
  `HasRelativeCoefficientWindowApproximation` on `U.ι ≫ f`, `V.ι ≫ f`, and
  `(U ⊓ V).ι ≫ f`. The conclusion uses `(U ⊔ V).ι ≫ f`. Thus the statement retains
  every premise; it does not assert unconditional existence on the three smaller opens.
- The property quantifies over all `D : CommRingCat.{u}`, maps `d : B ⟶ D` with
  `d.hom.FiniteType`, and supplied `t : D ⟶ A` satisfying `d ≫ t = b`.
- For W represented by its structure morphism f, the actual base change is
  `pullback f (Spec.map b)`, with `pullback.snd` its map to Spec A. K ranges over
  its `schemeDerivedCategory`, with both `schemeDerivedQCohProperty _ K` and the
  exact dependency predicate `Scheme.IsPseudoCoherentRelativeTo ... K`.
- The integer a is unrestricted. The output is `E : CommRingCat.{u}` (D' in the
  node), `s : D ⟶ E`, `s.hom.FiniteType`, and `e : E ⟶ A` with `s ≫ e = t`.
  The binder `h : (d ≫ s) ≫ e = b` supplies the derived base-change projection's
  commutativity proof. It follows from the already specified factorization and
  imposes no additional condition or choice of map.
- F belongs to `schemeDerivedCategory (pullback f (Spec.map (d ≫ s)))`. Boundedness
  is `∃ l v : ℤ, ∀ i, i < l ∨ v < i → IsZero (H^i(F))`; no requirement `l ≤ v`
  excludes the zero complex. Coherence is the genuine
  `RingedSpace.IsCoherent _ (H^i(F))` for every i, including finite-type kernels.
- Gamma is a morphism from F into `schemeDerivedDirectImage` of the actual
  `coefficientWindowProjection`. This projection is `pullback.map` with identity
  on W and `Spec.map e` on the coefficient scheme, with genuine commutativity proofs.
- M is `coefficientWindowModule e`: `DerivedCategory.singleFunctor _ 0` applied
  to `tilde` of `ModuleCat.of A A` restricted along `e.hom`. Its E-action is therefore
  exactly the supplied one, not an independent algebra structure.
- The A-structure map `coefficientWindowMultiplication` is the ordinary pullback
  comparison `Scheme.Modules.tildePullbackIso e`, followed by the scalar extension/
  restriction adjunction counit, then `tildeSelf`. The counit multiplies a tensor b
  to ab. `coefficientWindowScalar` pulls this map along the map to Spec A, after
  the pinned derived square comparison; the single-module comparisons and ordinary
  structure-sheaf pullback map yield the tensor unit (definitionally the degree-zero
  structure sheaf in the shared derived tensor construction).
- `coefficientWindowTheta` is the forward Hom equivalence of the canonical derived
  adjunction applied to the canonical tensor comparison, tensored scalar map and
  inverse Hom equivalence of gamma, followed by `λ_ K`. The tensor comparison choice
  satisfies the existing uniquely determining K-flat predicate. The composition/
  adjunction entry points are pinned to the shared derived counits. No arbitrary
  natural isomorphism, arbitrary action map, or mere Nonempty datum is substituted.
- A cone is expressed by existential C,j,delta with `Triangle.mk theta j delta ∈
  distTriang ...`. Its final two clauses are `schemeDerivedQCohProperty _ C` and
  `∀ i, a ≤ i → IsZero (H^i(C))`, exactly including degree a. Using a distinguished
  cone triangle avoids selecting a noncanonical cone and adds no assumption.
- No flatness, injectivity, faithfulness, nonzero-ring, or surjectivity assumption
  occurs on any coefficient map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- Convention node `def-pc-morphism-conventions`: the standard `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, and scheme opens; it has no separate declaration.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and `pullback.map`; scheme pullbacks are the existing instance.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, on the existing `SheafOfModules` carrier.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsPseudoCoherentRelativeTo`, with its every-m affine-chart definition.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `WeilConjectures.AlgebraicGeometry.Coherent`, `RingedSpace.IsCoherent`, and the
  Mathlib quasi-coherent/finite-type predicates. This current repaired interface
  is usable; no dependency repair is needed.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`; `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `derivedPullback`; `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  the global `schemeDerivedTensorMonoidal` instance, reached through the tensor interface.
- `WeilConjectures.AlgebraicGeometry.DerivedAdjoint`:
  `nonempty_derivedPullbackAdjunction`; the construction uses the more specific,
  already existing pinned `canonicalSchemeDerivedAdjunction` from
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation`, together with
  `canonicalDerivedSquareComparison` from that module.
- Mathlib `Pretriangulated.Triangle.mk`, `distTriang`, and the shared derived-category
  triangulated instance render `def-weil-triangulated-category`'s Mathlib match.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.map`, `tildeSelf`.
- Existing construction helpers are `Scheme.Modules.tildePullbackIso` from
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`,
  `Scheme.Modules.canonicalSinglePullbackMap` from
  `WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`, and
  `exists_canonicalPullbackTensorComparison` from
  `WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison`.

Every already stated proof dependency's module is imported without `public`. The
Mathlib proof leaves use the already imported quasi-compact and finite-type APIs,
plus `Mathlib.RingTheory.FiniteType`. Two proof dependencies have no recorded
Lean declaration yet (`lem-sfb-relative-pseudocoherence-all-affine-charts` and
`lem-sfb-sheaf-single-degree-coefficient-cancellation`; the Mathlib leaves require
no new module); there is no statement dependency on these theorems,
and no import is invented for them. The maintainer can add their proof imports when
those statements land.

Edge cases checked before drafting and again against the definition: U or V empty;
both empty; U=V; disjoint opens; zero K and F; zero coefficient ring A (Spec A empty);
noninjective and nonflat maps such as Z to F_p and k[epsilon]/(epsilon^2) to k;
arbitrary negative, zero and positive a. The definition quantifies over arbitrary
finite-type stages and retains the factorization map, so these cases are included.
The shared universe u does not bound coefficient stages in a smaller universe than B
or A: arbitrary finite-type stages admit u-sized presentations. The localization
universe w is explicit and independent. The family of HasDerivedCategory instances
only selects localizations and imposes no geometric restriction.

Searches (before writing, for both the item and P):

- msearch.py leanfinder, `Two open locality of finite window derived coefficient
  approximation for relatively pseudo coherent complexes`: eight hits including
  local finite generation, spreading-out and topological locality; none states this
  coefficient approximation. Full hit list recorded on the new definition node.
- msearch.py loogle, `"DerivedCategory", "glue"`: OK, zero hits.
- msearch.py grep, `coefficientWindow|CoefficientWindow|coefficient.*approximation`:
  OK, zero Mathlib hits.
- msearch.py leansearch, `Finite window coefficient approximation of relatively
  pseudo coherent complexes over finite type coefficient rings`: eight hits on
  finite presentation of module sheaves and finite polynomial coefficient range;
  no match. Full hit list recorded on the new node.
- rg on `lean/WeilConjectures`, `lean/Sheaf`, and the upstream name index, plus an
  exact item-id search in WeilConjectures: no existing item or P declaration.
  Broader scalar-action searches located the canonical APIs reused above.
- rg on `dag/nodes` for finite-window coefficient approximation: only this item.
  `tools/blueprint_refs.py search 'coefficient approximation'`: zero matches;
  search `finite-window`: four condensed Hom-vanishing nodes, a different notion.
  `ancestor` reports a created node uses `blueprint.from.node = None`, matching the
  item's current ancestor record. No pre-existing node defines P.

Validation: every file compiled separately using the prescribed scompile.py against
its published live dependencies, within 60 seconds. `autoImplicit false` is set in
both files. All variables and universes are explicit, no local notation or private
notion is used, and all lines are at most 100 characters. The one theorem is left
with `sorry` as required; the definition module has no sorry.

## New nodes

`def-sfb-relative-coefficient-window-approximation` defines P for a locally finite
 type structure morphism and a supplied coefficient map; the locality theorem uses
 this on the inclusions of U,V, their intersection and union. Its six declarations
 give the actual base-change projection, A[0], multiplication, scalar map, normalized
 theta, and the quantified approximation proposition. Its source is the item's
 explicit definition of P, an agent-formulated prerequisite of the paragraph after
 Stacks 0CSD. Its record cites the original notions and the three existing canonical
 comparison interfaces. The three kinds of searches above found no existing node or
 Lean definition of this property. No new mathematical assertion is postponed.

Dry run: deliver2.py --no-push returned OK, commit 3bbf2f06293, with both files
compiled and preflight accepted. The worker delivers directly; the maintainer supplies
the independent review under the dispatcher instructions.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
