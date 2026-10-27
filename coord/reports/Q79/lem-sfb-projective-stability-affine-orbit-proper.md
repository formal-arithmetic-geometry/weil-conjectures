## Worker report

The delivery states `AlgebraicGeometry.ProjectiveRepresentation.stable_iff_vectorOrbit_proper`
for the exact item. Its hypotheses render as follows: `k : Type u` with `[Field k] [IsAlgClosed k]`
renders the algebraically closed field; `E` and `hr : 2 ≤ Module.finrank k E` render the
r-dimensional space with r ≥ 2; `V`, finite dimensionality and `[Nontrivial V]` render the
nonzero finite-dimensional representation space; `idx`, `Fintype idx`, and `DecidableEq idx`
render a finite basis index; `b : Module.Basis idx k V` is the chosen basis; `ρ` is a
homomorphism from `specialLinear k (Module.finrank k E)` to `GeneralLinearGroup idx k`; `Y`
with `[IsHProjective Y.hom]` is projective and `j` with `[IsClosedImmersion j.left]` is the
equivariant closed projective embedding; `D : LinearizedEmbedding ρ j` supplies the action and
dual tautological linearization; `y` is a k-valued geometric point, `v` is its nonzero vector
lift, and `hlift` states that its pulled-back coordinate sections evaluate to the basis
coordinates of `v`. The conclusion is exactly `D.linearization.IsStable k y ↔ IsProper
(vectorOrbit b ρ v)`, matching stability and properness of the affine vector orbit map.

The supporting definition module states the missing coordinate-specified linearization notion.
`entry` is the pullback of GL coordinate functions along `g ≫ ρ`; `line` is the tensor pullback
of the existing projective twist; `coordinate` uses the section-normalized tensor pullback
adjunction; `LinearizedEmbedding.coordinates` imposes the inverse-matrix formula on all test
schemes; `IsVectorLift` introduces the basis coordinate trivialization; and `vectorOrbit` is
`AffineSpace.homOfVector` with the matrix-coefficient coordinates of `ρ(g)v`.

Dependencies used are `Sheaf.AlgebraicGeometry.GroupSchemeLinearization` (the declarations
`GroupSchemeLinearization.Linearization`, `.IsStable`, and `.stabilizer`),
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (`tensorPullbackSectionAdjunction`),
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` (`GeneralLinearGroup`),
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` (`ProjectiveSpace.twist` and
`twistOneSection`), `Mathlib.AlgebraicGeometry.AffineSpace` (`AffineSpace.homOfVector`),
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective` (`IsHProjective`), and
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (`IsProper`). The item module also imports the
recorded proof-route modules, including the section algebra, smooth orbit geometry, properness,
finite morphism and Nullstellensatz declarations, for the eventual stage-3 proof plan.

Edge cases checked: `idx` is any finite type (including empty in the supporting definitions),
`v ≠ 0` is explicit, `Nontrivial V` excludes the zero representation, `r ≥ 2` excludes the
rank-one exception, all test schemes may be nonreduced, no characteristic assumption is made,
and the stabilizer remains scheme-theoretic through the existing equalizer definition.
The constructions use the chosen basis to identify affine space with `Spec (Sym V⋆)` and do not
restrict to reduced test schemes.

Searches recorded in `searches.jsonl` and the node files: LeanFinder and LeanSearch searches for
projective stability, proper orbit morphisms, and induced dual tautological linearizations; Loogle
for `IsProper` and orbit; grep over Mathlib and project AlgebraicGeometry for semistability,
linearization and orbit maps. No exact existing declaration was found. Existing declarations
were reused wherever available. Earlier searches also checked the source repository and
`lean/Sheaf` by the item id; no declaration exists.

## Second reading by Q79

I reread the node and both modules. The item theorem has all original clauses: the algebraically
closed field, r ≥ 2, finite-dimensional nonzero V, rational SL representation, projective Y,
closed equivariant embedding, dual tautological linearization, semistability, closed orbit,
and zero-dimensional scheme stabilizer. The Lean conclusion is the recorded stability predicate
and `IsProper` of the explicitly constructed orbit map. The new definition node supplies each
notion introduced by the Lean interface and its module has no `sorry` in definitions.
The only postponed item proof is the single theorem `stable_iff_vectorOrbit_proper`; its proof is
`sorry` as required for stage 2. No statement mismatch or source fault was found.

## New nodes

`def-sfb-projective-representation-linearization` states the induced dual tautological
linearization and vector orbit construction, sourced to MFK Chapter 1 §1 and Chapter 2 §1,
Proposition 2.2, with Morrison Sections 2.1--2.2 as the locally available reconstruction.
The Mathlib/source/project search found no existing declaration or DAG node for this exact notion;
the searches and their verdicts are recorded in its `mathlib_searches`.

The coordinate choices do not restrict the vector spaces: the first proof step chooses bases of
E and V. The source's SL(E) is transported to the recorded SL of rank `finrank k E`; choosing a
basis of E identifies their group schemes, and a basis of V identifies GL(V), projective space
of lines in V, and affine vector space with the displayed coordinate models. Since all rational
homomorphisms `ρ` and all bases `b` are quantified, this loses no representation or vector lift.
For the lift condition, a nonzero v on the line j(y) gives evaluation at v, which is the specified
isomorphism `e : y*L ≅ k`. Conversely the coordinate equations recover that same line. Scalar
multiples of v give exactly rescalings of e and are all included.

In the second reading I checked the sign directly: a covector φ at x transports to φ composed
with g inverse at gx, so `D(g,x)(s_i(x)) = Σ_l ρ(g inverse)_{il} s_l(gx)`. Thus the formula in
`LinearizedEmbedding.coordinates` describes O(1), the dual tautological line, and its ratios force
the projective action `j(gx) = [ρ(g)j(x)]`. This includes arbitrary nonaffine and nonreduced tests;
it does not merely assert equivariance on k-points. Generation by the coordinate sections fixes
the line map, excluding an arbitrary character twist. The ordinary pullback appearing inside
`D` and in the evaluation trivialization is the existing recorded linearization API; `line j`
itself uses the stipulated tensor pullback, and no alternate linearization or stabilizer was
defined. The full equalizer's dimension is what `.IsStable` tests; it is not the dimension or
cardinality of its k-points. For the trivial representation V=k, semistability may hold but the
stabilizer is SL_r of positive dimension and the constant affine orbit map is not proper, so
both sides are false. For the standard SL_r representation every nonzero vector is unstable,
and the affine orbit misses zero but has zero in its closure, again consistent with both sides.
An empty Y supplies no y, rather than being excluded by an added nonemptiness hypothesis.

The second reading is a self-rereading, not a claim of a second agent: the dispatch brief forbids
starting other agents and assigns independent delivery review to the maintainer.

Exact search queries and results: LeanFinder `Projective geometric invariant theory stability is
equivalent to properness of the affine vector orbit morphism` returned topological proper-action
and generic scheme properness lemmas, none this criterion. Loogle `"IsProper", "orbit"` returned
zero hits. LeanSearch `Projective stability semistable linearized group scheme action affine cone
orbit proper` returned ordinary vector-space projectivization actions, not scheme linearizations.
For the new definition node, LeanSearch `Induced dual tautological linearization on a closed
projective subscheme of a rational representation by coordinate transformation` returned dual
linear maps and vector-space projectivization; LeanFinder `Induced linearization of O(1) for a
group scheme rational representation projective embedding` returned projective objects in Rep
and ordinary projectivization. Mathlib grep `tautological|linearization|orbitMap` in
AlgebraicGeometry returned zero hits. Project `rg` found the existing general group-scheme
linearization and the PGL-specific module, both read; neither supplies this induced coordinate
specification or vector orbit construction. DAG grep for dual tautological terminology found
the item and slice/line-degree theorems, no definition of the needed notion. The blueprint search
`projective representation` returned zero blueprint nodes; `tautological` returned seven unrelated
Thom, twisting, and projective-bundle items. `blueprint_refs.py ancestor` returned None, so the
new node preserves that inherited null ancestor and prepends this item to the full via chain.
`lean_names_upstream.py show` found no item attachment. No source or statement fault was found;
no statement correction or dependency module was necessary. The item changes only `lean` and
adds the new definition id to `stmt_deps`.

Validation: scompile.py compiled both delivered files separately in dependency order, with no
errors or warnings. The first compile identified `ι` as a notation token imported by the
library, so the explicitly bound index variable was renamed `idx`. The final signatures have
both auto-implicit options disabled, and the one named theorem has only its expected `sorry`.
The dry run reported `OK (dry run)` for commit `1ba1048e8b6`, passing preflight and per-file
compilation. This report update makes that dry-run commit illustrative; the final dry run and
push are executed again with the complete report.
