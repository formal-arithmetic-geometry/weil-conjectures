## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions` states
`AlgebraicGeometry.Etale.CoordinateTrace.contractions`, with its proof `sorry`.
Every other declaration is an abbreviation or a composite of existing canonical maps,
with real data. No new node, dependency repair, or statement correction is needed.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md`, both triangles. This node
isolates the contraction equations before evaluation of the diagonal integrals.
The node's mathematical statement is unchanged. The returned-delivery repair adds
the five requested landed nodes to `stmt_deps` and updates `lean`.

Hypothesis and clause correspondence (names below lie in `AlgebraicGeometry.Etale.CoordinateTrace`):

- A finite commutative ring is `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`.
  This is the coefficient universe of the recorded categories. Finite rings can
  always be lifted to this universe, with no mathematical restriction.
- Arbitrary schemes and a proper map are `{X Y : Scheme.{u}}`, `f : X ⟶ Y`,
  `[IsProper f]`. There is no other scheme hypothesis.
- W and its projections are exactly `pullback f f`, `pullback.fst f f` and
  `pullback.snd f f`, not an arbitrary square or comparison.
- `DerivedCategoryModule A T` is the recorded ordinary unbounded category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`. `tensor` merely abbreviates
  evaluation of `derivedTensor`; it introduces no new tensor product.
- `pull` is the existing left-derived `upperStar`, canonically the exact inverse
  image by `leftDerivedUpperStarIsoMapDerivedCategory`. `push` is the existing
  total right-derived `lowerStar`, using the canonical derived adjunction.
- `J` is a module sheaf on Y, and `hJ : Scheme.IsLisseRankOneSheaf J` says it is
  etale locally isomorphic to the constant free rank-one A-module. The definition
  was read in `WeilConjectures.ConstructibleSheaf.LisseRankOne`: an etale cover and
  a `Nonempty` isomorphism with the constant sheaf on every cover member.
- `d : ℤ` and `shiftedLine A J d` put J in degree zero and shift by `2 * d`.
  L_X is `(pull A f).obj (shiftedLine A J d)`. The representative of L_W is
  p2*L_X. `coordinate` is the canonical comparison p1*f* -> p2*f* induced by
  fp1=fp2. Thus neither an equality of unrelated objects nor extra line data is
  assumed. `H A f L` is the actual functor K |-> f*K tensor f*L.
- `orderedProjectionIso` is the symmetry-conjugate of the recorded
  `rightDerivedLowerStarProjectionMap`: swap outside, apply that map, then map
  the inside swap through pushforward. Invertibility comes from the existing
  proper projection theorem with `isAddTorsion_of_finite`, with no extra input.
- `exchange2` is the existing `derivedBaseChangeMap` on the actual pullback
  square; `exchange1` uses its flipped square. The exact-inverse-image record
  exposes `exactDerivedBaseChangeMap`; its note identifies this same map under
  `leftDerivedUpperStarIsoMapDerivedCategory`. Using its left-derived presentation
  is a canonical transport, not a new exchange. The two squares use the same
  counits and inverse-image composition maps. Their inverses use the existing
  proper torsion-ring unbounded base-change theorem.
- `t`, `t1` and `t2` have the node's specified source and coefficient-unit target.
  `ht1` is beta1 followed by t1 = f*t followed by the canonical unit comparison.
  `ht2` additionally maps `coordinate` through Rp2*, converting beta2's
  p1*L_X to the chosen p2*L_X representative of L_W. These are precisely the
  stipulated trace compatibilities, and impose no diagonal identity.
- `evaluation` is e_K: inverse ordered f-projection, K tensor t, right unitor.
  `comparison` is C_M: inverse original-order p2-projection, followed by the
  inverse beta2 tensored with the identity of L_X. Inverting the original-order
  projection is exactly the symmetry-conjugated extraction specified in the node.
- The first conjunct quantifies over every `M : DerivedCategoryModule A X`.
  Its left side is F(C_M) followed by e_(FM). Its right side begins with
  `directComparison`, which composes the canonical direct-image compositors,
  the equality fp2=fp1, and the inverse compositor. It then applies F to inverse
  ordered p1-projection, M tensor t1, and the right unitor. The common source is
  FRp2*(p1*M tensor L_W). This explicitly renders the source identification in
  the first displayed equation.
- The second conjunct quantifies over every `K : DerivedCategoryModule A Y`.
  Its left side is C_(HK) followed by H(e_K). Its right side first maps
  `coordinateH` tensor identity through Rp2*: this is the canonical
  p1*HK -> p2*HK comparison, obtained from the two pullback tensor isomorphisms
  and fp1=fp2. Then it applies inverse ordered p2-projection, HK tensor t2,
  and the right unitor. This renders the second displayed equation with its
  stipulated source identification.
- All equalities are actual equalities of derived morphisms, without a diagonal
  class, diagonal integrals, Noetherianity, bounds, constructibility, or a
  Tor-amplitude assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  including stability under pullback. The base-change proof dependency is the
  existing properness stability instance (`lem-weil-pbc-proper-base-change`).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.condition`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, re-exporting
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `Etale.constantComplex`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `leftDerivedUpperStarIsoMapDerivedCategory`, `leftDerivedUpperStarComp`,
  `rightDerivedLowerStarComp`, `derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`,
  `derivedTensorRight`; `...TensorStructure`: `derivedTensorRightUnitor`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap`, its counit-transpose characterization.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `exactDerivedSquareUpperStarIso`, `exactDerivedBaseChangeMap` are read as the
  inherited dependency's exact presentation; the statement uses the module map
  `derivedBaseChangeMap` owned by `sbc-def-base-change-map` instead. No claim is
  made that the exact-presentation declaration occurs in the statement.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `derivedSquareUpperStarIso`, `derivedBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`:
  `isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion`.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`:
  `isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring` (the published
  public declaration of the recorded proper unbounded torsion-ring theorem).
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`: `derivedTensorSymmetry`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarTensorIso`, `leftDerivedUpperStarUnitIso`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`.
- Proof imports retain `Sheaf.Paper.RingedKunnethFactorizations`
  (`SheafOfModules.ringedKunnethFactorizations`),
  `Sheaf.Paper.RingedProjectionTensorComposition`
  (`SheafOfModules.ProjectionCoherence.ringedProjectionTensorComposition`),
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair`
  (`SheafOfModules.LineEvaluation.evaluation_inverse_pair`),
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
  (`SheafOfModules.site_derived_tensor_descent_independentCoefficients`), and
  `Sheaf.Paper.RingedExchangeTensorCoherence`
  (`SheafOfModules.ringedExchangeTensorCoherence`).
  `CategoryTheory.Adjunction.eq_unit_comp_map_iff` is already available through
  `Mathlib.CategoryTheory.Adjunction.Basic`; its signature was read directly.

Edge cases checked before finalizing: the zero ring is permitted; empty schemes
and identity f are permitted; t=0 gives both zero contractions; d=0 and negative
integers are included; M and K can be zero or unbounded in either direction.
The sign is (-1)^(4d²)=1 for every integer d. An odd shift or a higher-rank line
would not in general have identity self-symmetry, so hJ and the even shift are
material hypotheses. The two trace equations have separate, correctly oriented
coordinate transports. No hypothesis is a vacuous substitute for properness or
for the line condition.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: `coordinate trace contractions projection formula proper base change
  derived sheaves`: 8 hits, on sheaf presentations and scheme pullbacks, no match.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.MonoidalCategory`: 12 hits,
  generic adjunction monoidal structures, no coordinate contraction equality.
- Mathlib grep, CategoryTheory:
  `trace.*(baseChange|projection)|coordinate.*[Cc]ontraction`: zero hits.
- LeanSearch: `Compatibility of coordinate trace contractions with derived
  projection formula and proper base change`: 8 hits, on linear/algebra traces
  and affine coordinates; none is this statement.
- rg in `lean/WeilConjectures` for the item id and `coordinateTrace`: no match.
  rg in `lean/Sheaf` for coordinate/trace/contraction names finds composite-trace
  lemmas and the downstream projective-line proof plan, not these equations.
  Read `SfAffineBaseP1TraceAdjunction.lean`: it explicitly uses this item and does
  not supply it. Read the existing LisseRankOne and tensor-symmetry declarations
  instead of duplicating their notions.

Validation: every delivered Lean file is compiled with `scompile.py`, as a separate
module against the published live build. No local/global lake build is run.
There is one postponed theorem, with the full six-step natural-language proof in
its docstring and the matching existing DAG node. No disputed statement or node
fault was found.

## Second reading by NE

Self-audit, not a claim of an independent agent review: the dispatcher forbids
starting agents and the maintainer supplies the independent review. I reopened
the node and module and checked each hypothesis and clause as mapped above.
In particular beta2 uses the unflipped self-product, beta1 the flipped square;
L_W is p2*L_X, so ht2 needs the p1-to-p2 coordinate map, whereas ht1 does not.
The first RHS has the direct-image path comparison before F of inverse p1
projection; the second RHS has the pullback/tensor coordinate comparison before
inverse p2 projection. Removed an unnecessary explicit equality binder for L_Y:
`shiftedLine` now gives J[2d] directly. All helpers are actual composites and all
theorem proofs are `sorry`. Four long lines were wrapped after compilation.


## Returned delivery repair

Return reviewed: immutable head `2339318befe8`, recorded in `coord/returns/NE.md`.
The reviewer accepted the mathematics and identified missing statement-dependency
owners. Compared the retained sandbox node against current main: every non-Lean
field was identical before repair. Rebased the node copy on current main while
retaining its Lean record; the delivery wrapper fetches and builds on the latest
main again at delivery time.

1. H2: added exactly these five landed nodes to `stmt_deps`, as requested:
   `lem-kun-tensor-sym` owns `derivedTensorSymmetry` used by `swap`;
   `lem-kun-tensor-unit` owns `derivedTensorRightUnitor` used by `evaluation`
   and both equations; `sbc-def-base-change-map` includes the original
   module-coefficient `derivedBaseChangeMap` in its `lean.declarations`, used by
   `exchange1` and `exchange2`; `lem-kun-0f0g` supplies the `IsIso` proof used by
   `orderedProjectionIso` and `comparison`; and
   `lem-kun-proper-base-change-torsion-ring` supplies the `IsIso` proof for both
   exchanges. Read each current node's statement and Lean record and the full
   relevant source signatures/docstrings. The two IsIso inputs assume precisely
   properness and additive torsion, supplied here by `[IsProper f]` and finite A.
   Added public imports of `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
   and `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`, the two recorded
   dependency modules not already directly imported. The public proper theorem
   remains the upstream declaration re-exported by BaseChangeTheorems.Proper.
2. H4 note: chose the reviewer's explicit five-node addition alternative. The
   exchanges remain the accepted `derivedBaseChangeMap` construction and now cite
   its actual owner. The report distinguishes the inherited exact-presentation
   dependency from the declaration actually used. It does not claim that merely
   importing `exactDerivedBaseChangeMap` constitutes using it in the statement.
3. Advisory: `derivedSquareUpperStarIso`, `rightDerivedLowerStarComp` and
   `leftDerivedUpperStarUnitIso` remain the existing canonical library helpers.
   The return calls their missing ownership advisory and requests no new nodes
   for them. Their definitions and orientations were retained, as accepted by
   the mathematical review. No new declaration or postponed theorem was added.

The Lean declaration bodies and theorem signature are identical to the returned
version; only the two required public imports were added. The repair is the
substantive DAG dependency delta above, not an unchanged re-push. All original
hypothesis/clause and edge-case checks remain valid. No statement correction is
needed, and `proof`, `proof_deps`, and the mathematical `statement` are unchanged.
Compile, dry-run, and final delivery are rerun with the prescribed wrappers.

Repair validation: explicit `scompile.py` passed for the delivered module in both
sandbox and library modes, with no warnings (7.4 s and 6.0 s).
