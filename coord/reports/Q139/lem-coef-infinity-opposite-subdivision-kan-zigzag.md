## Worker report

Repair of the delivery returned at immutable head `d25edc8e066d` for H3, H8 and
H11. The retained packet first passed `deliver2.py --no-push` (commit
`71042afe8a`), but reading its mathematical statement confirmed the reported
omissions. The repaired module is
`Sheaf.AlgebraicTopology.OppositeSubdivisionKanZigzag`; its main declaration is
`SSet.opposite_subdivision_kan_zigzag`. The DAG statement, dependencies, proof
and all other node fields are unchanged; only `lean` changes. The saved node
was compared field by field with current shared main: only `lean` differed.
The delivery wrapper builds the new commit on the current `newtargets-dag`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small simplicial sets | `SSet.{u}` throughout, with all universes and variables explicitly bound. |
| Operator reversal by `ρ_n α ρ_m` | Existing `SSet.opFunctor` and `T.op`, rather than a second opposite construction. `SSet.op_map` uses `SimplexCategory.rev.map`, whose `rev_map_apply` is `(α i.rev).rev`. `SSet.opObjEquiv` identifies the degreewise labels. |
| Natural involutive isomorphism `Sd T ≅ Sd(T.op)` | One outer `∃ η : sd ⟶ opFunctor ⋙ sd` supplies every occurrence of η in the entire theorem. `IsIso (η.app T)` and both equations through `opFunctorCompOpFunctorIso` specify its inverse. Naturality is part of this `NatTrans`. |
| The stated formula on every labelled flag of nonempty subsets | For every `T n r σ t`, the next conjunct provides a flag `t'` with `(t'.obj i).finset = (t.obj i).finset.image (fun a ↦ ULift.up a.down.rev)` for every i, and states the equation for η on `SubdivisionFacePoset.simplexInclusion σ`. `oppositeSimplex σ` has precisely the same underlying simplex label in `T.op`. No flag or simplex representative is omitted, including degenerate flags. |
| First weak-equivalence zigzag | The first conjunct asserts weak equivalence of `subdivisionLastVertex.app T`, `η.app T`, and `subdivisionLastVertex.app T.op`. Their types are exactly the three arrows in the node's first display, for arbitrary T. |
| Natural realization homeomorphism with barycentric-coordinate formula | One family `H T : toTop.obj T.op ≃ₜ toTop.obj T` has the naturality equation for every simplicial f. On every representative labelled by σ, the next equation uses `SimplexCategory.toTopHomeo` to represent the standard topological simplex and requires coordinates `t' i = t i.rev`. This specifies the claimed homeomorphism rather than an arbitrary natural one. |
| Opposite preserves and reflects weak equivalences and preserves Kan complexes | The quantified equivalence for `Enhanced.IsWeakHomotopyEquivalence (opFunctor.map f)` is precisely preservation and reflection. `KanComplex T ↔ KanComplex T.op` also expresses reflection, which follows from the same involution; in particular it includes the asserted preservation. |
| For every Kan T, all objects of the second displayed zigzag are Kan | `∀ T, KanComplex T →` is the hypothesis; the conclusion includes `KanComplex T.op`, `KanComplex (exInfinity T)`, `KanComplex (exInfinity (sd.obj T))`, and `KanComplex (exInfinity T.op)`. Together with the hypothesis these are all five objects, including the previously missing middle object E(Sd T). |
| Exactly the four arrows of that same zigzag are weak equivalences | The four predicates refer to `exInfinityUnit.app T`, `exInfinityFunctor.map (subdivisionLastVertex.app T)`, `exInfinityFunctor.map (η.app T ≫ subdivisionLastVertex.app T.op)`, and `exInfinityUnit.app T.op`. The η is the single outer natural involutive comparison, not another existential local to T. |
| Naturality of the all-Kan zigzag | Four displayed equations for each f give the four commuting squares, using f, `E.map f`, `E.map (sd.map f)`, `E.map (opFunctor.map f)` and `opFunctor.map f` as vertical maps. Naturality holds for these canonical maps on all simplicial sets, hence in particular on Kan complexes. |
| Every arrow commutes with finite-product projections | Specialize those same four equations to each `Pi.π K i`. The η naturality also gives its projection square. The subsequent quantified finite-product clause asserts `IsIso (piComparison exInfinityFunctor K)` and both its projection equation and its unit/projection equation. `I : Type v` with `[Finite I]` is independent of u. `terminalComparison` explicitly includes the empty product. No preservation of products by Sd is required. |
| Maps of Kan complexes `u : U → W`, `v : V → W` | The shared path family `e` and both its clauses quantify with `[KanComplex U] [KanComplex V] [KanComplex W]`. Helpers construct the path pullback for arbitrary simplicial sets, but the theorem's path assertion has exactly the node's Kan hypotheses. |
| The specified path-space pullback | `oppositePathPullback u v` is the iterated categorical pullback `pullback (pullback.snd u ev₀ ≫ ev₁) v`. Its three projections `oppositePathLeft`, `oppositePathComponent`, `oppositePathRight` recover the endpoint, path and endpoint. Evaluation and constant paths are the recorded `Enhanced` constructions. |
| Exchange endpoints and reverse the interval | The same `e U V W u v` has both morphism equations exchanging the left and right projections, with `opFunctor.map` on the original projections. Its path formula evaluates the output on every degree-m pair `(β, γ)` as the original path on `(SimplexCategory.rev.map β, SimplexCategory.rev.map γ)`, then views that value in `W.op` via `opObjEquiv.symm`. This is exactly `h_m(ρ₁ β ρₘ, ρₙ γ ρₘ)`; both the interval and the parameter reversal are specified. |
| Natural isomorphism in the entire cospan | There is one `∃ e` over all Kan cospans, not a separate unrelated isomorphism for each one. For any cospan morphism `(a,b,c)` with `u ≫ c = a ≫ u'` and `v ≫ c = b ≫ v'`, the last clause states `opFunctor.map f ≫ e'.hom = e.hom ≫ g` for the induced path maps f and g. `IsOppositePathMap` states their three projection equations; these uniquely characterize the existing pullback-induced maps. Quantifying over such f and g avoids an additional chosen pullback model and adds no assumption: the pullback universal property supplies them for every commuting cospan morphism. |
| Compatibility with constant-path comparisons of strict squares | `OppositePathComparisonCompatible` quantifies over every strict square `a ≫ u = b ≫ v`, and over its comparison k characterized by its exact two endpoints and middle map `a ≫ u ≫ Enhanced.constantDiagrams Δ[1] W`. After reversal the conclusion fixes the endpoints to `opFunctor.map b` and `opFunctor.map a` and the path to `opFunctor.map (a ≫ u) ≫ Enhanced.constantDiagrams Δ[1] W.op`. Thus it specifies the same square and the same base simplex, rather than merely some constant path. The pullback universal property supplies k without an extra hypothesis on the square. |

Dependency interfaces read and used, including their full signatures and docstrings:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.evaluation`,
  `constantDiagrams`, `IsWeakHomotopyEquivalence`, and the inherited Mathlib
  `SSet`, `KanComplex`, `ihom` and realization conventions. This is the module
  recorded by `def-cbc-enhanced-diagrams-cones`.
* `Sheaf.AlgebraicTopology.SubdivisionFacePosetCalculus`:
  `SSet.SubdivisionFacePoset.simplexInclusion` and
  `subdivision_face_poset_calculus`. The former is the canonical coprojection
  `stdSimplex.sdIso.inv.app n ≫ sd.map σ`; the latter supplies the colimit and
  last-vertex normalization used by the proof plan.
* `Sheaf.AlgebraicTopology.SubdivisionLastVertexEquivalence`:
  `SSet.subdivisionLastVertex` and
  `subdivisionLastVertex_isWeakHomotopyEquivalence`; the last-vertex natural
  transformation is the dependency's canonical, normalized one, for every T.
* `Sheaf.AlgebraicTopology.ExInfinityFiniteProducts`: `SSet.exInfinity`,
  `exInfinityFunctor`, `exInfinityUnit`, `ex_infinity_finite_products`. These are
  the actual sequential colimit of iterated Ex and its stage-zero inclusion;
  the product assertion uses its canonical comparisons.
* Proof-only import `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`:
  `SSet.KanQuillen.right_proper_kan_quillen_core`, for two-out-of-three and
  composition of realization weak equivalences, without a Kan hypothesis on Sd T.
* Mathlib `AlgebraicTopology.SimplicialSet.Op`, `SimplexCategory.Rev`,
  `SimplicialSet.Subdivision`, `SimplicialSet.TopAdj`, and
  `CategoryTheory.Monoidal.Closed.FunctorToTypes` were read for the actual
  opposite, simplex reversal, flag model, realization representatives and
  functor-space simplex types. `TopAdj` is explicitly publicly imported for
  `SimplexCategory.toTopHomeo`.

All helper definitions belong to this node's specified constructions and are
listed in `lean.declarations`. They contain real data or actual proposition
formulas, with source/blueprint docstrings. Only the node's named theorem is
postponed. No new independent notion, dependency repair or statement correction
is needed.

Searches retained and checked:

* Saved `leanfinder`: “opposite simplicial set subdivision Ex infinity Kan weak
  homotopy equivalence path pullback”; results concerned spines/paths and
  model-category generators, not this comparison package.
* Saved `loogle`: `SSet.opEquivalence, SSet.exInfinity, KanComplex`; no matching
  theorem (`exInfinity` is a project construction, not a Mathlib identifier).
* The DAG's existing LeanSearch, LeanFinder, Loogle and grep records found the
  opposite involution and basic subdivision/Ex APIs, with realization comparison
  left TODO in `SimplicialSet/Op.lean`.
* Repair `msearch.py ... grep 'oppositePath|opposite_subdivision|op.*realiz|realiz.*op'
  AlgebraicTopology/SimplicialSet`: five hits, only the realization API and the
  opposite-realization TODO; no existing comparison declaration.
* Repair `rg` for `oppositePath`, `opposite_subdivision` and the node id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared `lean/Sheaf`:
  no hits. Additional searches for `oppositeSimplex`, `oppositePathLeft` and
  `IsOppositePathMap` in those trees and Mathlib: no declaration clashes.
* Opened the current blueprint proof paragraph 2 and the retained node's full
  nine-step argument. [Kerodon 00YZ](https://kerodon.net/tag/00YZ) states the
  last-vertex weak equivalence for an arbitrary simplicial set; the extra
  reversal comparisons are explicitly attributed to the retained argument.

Edge checks, before and during the repair:

* Empty T has no simplex representative, so the representative conditions have
  no spurious inhabitance requirement. None of the weak-equivalence assertions
  assumes Kan before the all-Kan clause.
* In dimension zero reversal fixes the unique vertex and coordinate. On Δ¹ it
  swaps vertices; the flag `( {0}, {0,1} )` becomes `( {1}, {0,1} )`, still
  increasing by inclusion. Repeated flag entries are allowed, so degeneracies
  are covered. Reversal of every subset of dimensions 0 through 3 preserves
  inclusion and squares to identity.
* The two outer one-dimensional horns exchange; the horn argument does not
  silently exclude i = 0 or i = n.
* The displayed naturality squares use E(Sd f), without a Kan assumption on
  Sd T and without a product-preservation assertion for Sd. For finite
  products, substituting f = `Pi.π K i` gives the required four squares.
  For the empty index type the projection equations are vacuous, while the
  terminal-comparison isomorphism remains an explicit conjunct.
* For empty path pullbacks, the projection and simplex equations have their
  correct unique/vacuous interpretation. For a constant path at w, the reversed
  value is `W(γ̄) w = W.op(γ) w`, independent of β, with exactly w as base label.
* Concrete diagnostic of the old predicate: take U and V to be discrete
  two-point Kan complexes and W a point. Every path component is constant, so
  the old predicate permits composing the swap with a nontrivial permutation
  of one endpoint. The repaired endpoint equations reject this wrong map.
  The full path formula additionally excludes an incorrect automorphism of
  nonconstant paths with the same endpoints.

Compilation: `scompile.py Q139 lem-coef-infinity-opposite-subdivision-kan-zigzag
<module.lean>` compiled the repaired sandbox probe and actual module cleanly
(1.9 s and 2.3 s). The first repair compile identified that `toTopHomeo` requires
`Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`; adding that exact import fixed
it. There are no remaining warnings or errors, and no `#check` lines. All lines
are at most 100 characters. All variables/universes are explicit and
`autoImplicit` is false. No mathematical statement dispute remains.

## Second reading by Q139

Reopened the full DAG statement, all nine proof steps, and the final Lean file
for a separate clause-by-clause pass. The table above records the correspondence;
the findings and repairs against returned head `d25edc8e066d` are:

1. **H3, explicit reversal:** the former theorem specified only a natural
   subdivision isomorphism and a natural homeomorphism. It did not constrain
   them to the node's flag and barycentric formulas. The new flag equation
   quantifies over every σ and flag and uses pointwise reversed finite subsets;
   the realization equation uses the same simplex label and `t' i = t i.rev`.
   Reading `SSet.op_map` and `SimplexCategory.rev_map_apply` confirms the
   opposite convention is exactly ρ αρ, without reversing the flag order.
2. **H3, shared all-Kan comparison:** the former Kan clause chose another η
   separately for each T, without the first η's properties, and omitted
   `KanComplex (exInfinity (sd.obj T))`. All clauses now share one outer η;
   the fifth-object check counts T (hypothesis), ET, E(Sd T), E(T.op) and
   T.op. The four weak-equivalence predicates match the four arrows, and the
   four naturality equations have the correct source and target in each square.
   Specialization to projections gives every product square, with no Sd
   product comparison inserted.
3. **H3, path comparison:** the former isomorphism and predicate did not fix
   the exchanged endpoints, reverse the actual path, assert naturality in all
   cospan objects, or retain the same constant path. Reading the actual
   functorHom simplex type confirms the new evaluation formula: the parameter
   argument is `γ.op`, its reversed argument is `(rev.map γ).op`, and the
   interval simplex is `stdSimplex.objEquiv.symm β` with reversal `rev.map β`.
   The output lies in `W.op`. Both endpoint equations use the original
   opposite projections. A single family e is used in the cospan naturality
   square and the constant-path predicate. Those predicates characterize the
   canonical induced/comparison maps by all three projections, so they are
   not arbitrary maps or added existence assumptions.
4. **H3, hypotheses and edge cases:** the original path clause quantified over
   arbitrary cospans; the repaired path clause has the node's three Kan
   hypotheses. The first subdivision and realization clauses still allow all
   simplicial sets. Independent finite index universes and the terminal case
   remain. The discrete two-point counterexample above demonstrates why the
   old predicate failed and why the repaired one rejects the incorrect map.
5. **H8:** replaced the short proof summary by all nine proof steps, including
   colimit descent, realization quotient descent, horn reversal, natural-unit
   two-out-of-three, all-Kan and projection squares, interval and parameter
   reversal, cospan naturality and equality for the same strict square. Each
   named dependency is identified where its mathematical input enters.
6. **H11:** replaced the absent/disclaimer-only second reading with this
   explicit semantic check. The final check also read every helper definition,
   verified real data and source tags, matched the verbatim signature in the
   `lean` record, and compared non-lean node fields with the current main node.

No hypothesis, conclusion, source object or canonical map was silently replaced.
The final module states the retained node, with only its proof postponed.

## Maintainer repair of H4

A broader search by the independent maintainer reader found the same iterated
path-pullback definition at `SSet.Enhanced.simplicialHomotopyPullback` in
`Sheaf.CategoryTheory.SourceAttachmentGluing`, lines 84--91. The delivered
`oppositePathPullback` repeated that definition. It is now an abbreviation for
the existing declaration, with its module imported. The three projections and
all comparison predicates retain exactly their previous meaning by unfolding.
The main theorem signature and natural-language node statement are unchanged.
No additional theorem assumption is introduced. The existing construction takes
arbitrary maps between `SSet.{u}`, so this repair imposes no Kan, finiteness or
universe condition. Its owning node is `lem-coef-infinity-source-gluing`; a
traversal of its statement/proof dependency closure found no path back to this
item (152 nodes visited).

Maintainer reproduction through `scompile.py Q139
lem-coef-infinity-opposite-subdivision-kan-zigzag <fixed module>` passed both
checks with no diagnostics: sandbox 3.2 s and library module 2.4 s. The immutable
module was also reproduced before the fix (sandbox 2.0 s, library 2.1 s). The
installed wrapper reports server execution with a private side overlay; no direct
SSH command, project edit or global build was used by the reviewer.
