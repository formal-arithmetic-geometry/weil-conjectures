## Worker report

The delivery states `prop-sf-open-closed-triangle-all-stages` in
`Sheaf.Paper.SfOpenClosedTriangleAllStages`. The node's mathematical text and all
its dependency lists are unchanged. The five `sfOpenClosedTriangle_*` theorems
jointly cover finite, integral, rational, and algebraically closed coefficients,
and the rational and algebraically closed Weil clauses. Every theorem proof is
`sorry`. Definitions contain actual data or explicit predicates, never `sorry`.

The source was read in both snapshots: master, sec-smooth-purity,
sk-prop-sf-open-closed-triangle, order 1851; main-20261015,
sec-smooth-purity/sk-prop-sf-localization, order 2195. Their statement texts agree.
The node's current sixteen-step proof supplies the detailed sheaf-sequence route;
the released stage-1 repair note concerned the earlier long Frobenius proof step,
not a withdrawn stage-2 interface. The current node already contains that split.

### Hypotheses and clauses

| Source data or clause | Lean rendering |
|---|---|
| Prime l and finite extension E/Q_l | `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| The coefficient prime is invertible on the base, as required by the operation definitions | `(k : Type u) [Field k] (hk : IsUnit (l : k))`; the Weil clause uses the recorded finite-field datum and `hl : l ≠ D.p` |
| X is a k-scheme | `[X.Over (Spec (.of k))]` |
| X is finite type and separated over k | `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]` |
| Closed immersion i and complementary open immersion j | `(i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]` and `Set.range j.base = (Set.range i.base)ᶜ` |
| U has the induced k-structure | `[U.Over (Spec (.of k))] [j.IsOver (Spec (.of k))]`; no independent structure is used in the operation value |
| Noetherian X and finite-type U, used in the proof | `sfRecollementNoetherian` states the inherited Noetherian structure; its proof docstring specifies the structure morphism's existing Noetherian and compactness theorems. `sfRecollementOpenFiniteType` supplies the inherited finite-type and quasi-compactness witnesses. They are supplied internally, not additional hypotheses of the all-stage statements. |
| Positive finite coefficient stage A_{E,n} | `(n : ℕ) (hn : 1 ≤ n)` and `Padic.coefficientExtensionRing l E n`; `sfFiniteRecollementAt` supplies the recorded finiteness proof internally |
| Finite bounded constructible category | `intrinsicFiniteTorsionConstructible l E n hn X`; `SfRecollementConclusionOn` also requires the two outer vertices to satisfy it |
| Integral category | `sfIntegralConstructibleCategory l E X`, including derived completeness, all positive constructible reductions and one uniform cohomological interval |
| Rational category, without Karoubi completion | `sfRationalConstructibleCategory l E X`; the normalization keeps the literal integral objects and the recorded raw localization |
| Algebraically closed coefficient category | `generalAlgebraicallyClosedConstructibleCategory l Ω X`; Ω has an independent universe v and the recorded algebraic-closure structure |
| The open counit and closed unit | Finite: precisely `exceptionalOpenAdjunction.counit` and `finiteRecollementDerivedAdjunction.unit`. Integral: normalization equations on every representative complex use the actual sheaf kernel inclusion and tensor-unit normalized closed adjunction unit. Rational/common-stage: natural comparison squares carry exactly those maps through the recorded localization and inclusions. |
| j!j* and Ri*i* are the outer vertices | Finite: the recorded intrinsic functors. Integral: `SfIntegralRecollementVertices` compares the open term to `sfIntegralCompactSupportValue` for the open/identity compactification applied to the actual completed pullback, and the closed term to the vertex of a recorded `SfIntegralDirectImage` Roos triangle (R lim Res_n Ri_{*,n}) of that pullback, with the derived products supplied by `integralOperationsDerivedCountableProducts`. (Maintainer fix: the delivery had used the ordinary `sfCompletedDerivedDirectImage` here.) |
| Distinguished triangle | `Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C` in `SfRecollementConclusion`; the finite version tests the inherited triangles in the ordinary ambient derived category exactly as `FiniteOpenClosedRecollementTriangle` does |
| A third arrow exists and is uniquely determined | `∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧, ...` |
| Hom(j!j*K[m],Ri*i*K)=0 for all integers m | `∀ (K : C) (m : ℤ), Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)`; in a preadditive category this means the Hom group is zero |
| Functoriality in K | For all `f : K ⟶ L` and distinguished completions δ,δ', the third square is `P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C 1).map (P.openTerm.map f)`; the first two squares are naturality of the recorded counit and unit |
| Descent of X,Z to k_0 | `D : FiniteFieldDatum`, `X₀ Z₀ : Over (Spec (.of D.k₀))`, the recorded geometric fibres, and the explicit equality identifying i with `(Over.pullback ...).map i₀`. The complementary open descends with the closed complement. |
| E- and Qbar-Weil complexes | The actual endofunctors `sfWeilFrobeniusPullback` and `sfCommonStageWeilFrobeniusPullback`; `SfRecollementWeilEquivariant` quantifies over `IsoAlgebra G`, definitionally the recorded fixed-pair categories |
| All three arrows Weil-equivariant | The first two explicit commuting-square equations use `K.str.hom`; the third uses `G.map δ`, the exact shift comparison and the shifted outer Weil isomorphism. The outer isomorphisms are uniquely characterized by the first two squares. |

`SfRecollementPresentation` contains only two endofunctors and two natural
transformations. It assumes no triangle, vanishing, decomposition or outer Weil
structure. Integral and common-stage presentations occur in existential theorem
conclusions together with their actual-operation normalizations. They are never
chosen to define a new object from a non-unique existence theorem. The normalized
isomorphisms transport the original operations; they do not substitute arbitrary
maps for the counit and unit.

The canonical integral sheaf construction is independent of choices of cones.
`sfRecollementCoefficientMap` is the adjunct of the already normalized completed
coefficient map. `sfRecollementModuleAdjunction` uses the published tensor-unit
adjunction for that specific map. The closed term is its left/right composite;
the open term is its kernel and the open counit is the actual kernel inclusion.
Kernels are determined by their universal property. The named proof lemmas needed
to derive and restrict these constructions have source and proof docstrings.
The two Weil theorems supply an exact shift structure on the specified Frobenius
pullback rather than assuming a triangulated structure on the fixed-pair category.

### Dependency declarations used

- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization` and its inherited triangulation.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `inclusion`, the
  literal `stage`/`obj` pairs and their existing triangulation.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`'s underlying
  `sfIntrinsicDerivedPullback`, the actual `integralDerivedPullback`, and the
  rational/common-stage pullbacks used by the recorded Frobenius functors.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedCoefficientMap` and the recorded
  integral direct image `SfIntegralDirectImage` (the specified Roos triangle of the
  finite-image tower), used for the closed vertex.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`:
  `sfIntegralCompactSupportValue`, using
  `Compactification.ofIsOpenImmersion j`, and its recorded rational/common-stage
  transport. No second compact-support construction is introduced.
- `Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement`:
  `finiteRecollementDerivedAdjunction`; the finite first arrow is the recorded
  `exceptionalOpenAdjunction` counit. Distinguishedness is exactly the predicate
  in `FiniteOpenClosedRecollementTriangle`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`, with the recorded `IsoAlgebra` fixed pairs
  (`sfWeilComplex`, `sfCommonStageWeilComplex`).
- The canonical adjunct is the existing
  `AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction` of
  `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`. Mathlib's
  functor-category kernel supplies the actual open-term data.

Every recorded statement-dependency module is explicitly publicly imported.
Already stated proof dependencies are imported without `public`, keeping the
node's sheaf-sequence, completion, scalar-extension and mate proof route available.
No definition or dependency-node record is replaced in this delivery.

### Edge cases

Checked the empty open (kernel of the identity is zero), empty closed part (the
kernel of the map to zero is the whole object), the empty scheme and zero complex.
The connecting map need not vanish: only Hom from the shifted open term to the
closed term vanishes. Both signs and zero of m are retained by `m : ℤ`.
The first positive finite exponent is n=1; n=0 is excluded exactly as in the
coefficient definitions. No Tor-amplitude or flatness hypothesis is added for the
finite quotient. Integral boundedness is the existing uniform-reduction bound,
not boundedness imposed on a resolution. Rationalization adjoins no idempotents.
Qbar morphisms may require a larger common stage than either object, and all such
morphisms are covered by naturality of the stage comparisons. The closure universe
is independent of the scheme universe. The Weil clauses permit arbitrary Weil
isomorphisms, including nonsplit ones, and use no Ext groups of a derived category
of Weil sheaves. Geometric Frobenius is semilinear over k; no k-linearity condition
has been imposed on it.

### Searches

1. `msearch.py`, LeanFinder: “open closed recollement distinguished triangle
   extension by zero closed immersion constructible derived category all
   coefficients” returned eight generic derived-category/t-structure hits, no
   all-stage recollement theorem.
2. `msearch.py`, Loogle: `Triangle, distinguishedTriangles, Adjunction` returned
   no hits (unqualified identifier Triangle was unknown to that service).
3. `msearch.py`, grep: `recollement|openClosed|open_closed` in Mathlib
   CategoryTheory returned zero hits.
4. `msearch.py`, LeanSearch: “open closed recollement distinguished triangle”
   returned the generic distinguished-triangle predicates and short-exact-sequence
   triangle results, not the scheme/coefficient statement.
5. LeanSearch and LeanFinder: “canonical open closed recollement presentation unit
   kernel exact functors coefficient stages” returned generic kernel, exactness,
   Grothendieck-category and unrelated profinite results. No presentation interface
   was found. Grep `RecollementPresentation|recollement|openClosed` in Mathlib
   CategoryTheory returned zero hits.
6. `rg` in the source `WeilConjectures` and the side `lean/Sheaf` found the existing
   finite recollement definition, finite adjunctions, ringed localization and the
   generic completed-comparison modules read above, but no theorem with all four
   stages and the fixed-pair Weil clauses. The old audit's
   `WeilComplex.exists_distTriang_openClosed` was also read through
   `scompile.py --source WeilConjectures.WeilSheaf.LowerShriekFunctoriality`.
   Its own docstring explicitly describes a weakening: only the vertices of an
   unspecified distinguished triangle are identified up to isomorphism, without
   specifying the canonical first two arrows. It uses the older Weil-complex
   interface and does not state all four coefficient stages or uniqueness.
   It therefore cannot serve as an exact existing declaration for this node.
7. `rg` for the exact item id in source `WeilConjectures` returned no match.
   `rg` for `SfRecollement`/`sfRecollement`/`sfOpenClosedTriangle` in Mathlib,
   source and side declarations returned no existing names.
8. `tools/blueprint_refs.py search 'recollement presentation'` returned zero
   blueprint matches. DAG text grep found incidental recollement language in
   `thm-sf-dual-perfect` and `def-tw-frobenius-action`, not a duplicate interface.

No statement is marked disputed. No mathematical text, proof step or dependency
was silently corrected. Validation uses the prescribed single-file compiler and delivery preflight.

### Validation

`scompile.py Q133 prop-sf-open-closed-triangle-all-stages` completed with exit code 0
for the delivered module, in both sandbox and library module contexts, with no
errors or warnings. Initial diagnostics were repaired by specifying the source and
target functors of the termwise counit map, supplying the already inherited
shift-additivity family explicitly at finite coefficient fields, and making the
Noetherian proposition a named theorem with its source and proof plan. No extra
mathematical hypotheses, universe equalities, or timeout increases were introduced.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer fix (review of 5de5966797ab)

`SfIntegralRecollementVertices` now identifies the integral closed vertex with the
object of a recorded `SfIntegralDirectImage` of the completed pullback, as the node's
[def-weil-derived-direct-image] defines Ri_* (R lim Res_n Ri_{*,n}(K_n)). Before, it
used the ordinary completed-coefficient derived image. That is isomorphic only by a
proof-step theorem (prop-weil-pbc-direct-image-limits), and the object it named was
not the node's. No other declaration changed, and the item's `lean.statement` is unchanged.
