## Worker report

This is the Stage 2 statement delivery for
`lem-coef-infinity-kan-homotopy-coherent-cube-invariance`, in
`Sheaf.CategoryTheory.InfinityKanHomotopyCoherentCubeInvariance`.
The retained NP sandbox contained only old stage-1 brief markers, not a Lean
module or node record. Q25's already reviewed delivery is a stage-1 split,
which is retained verbatim. This delivery supplies the missing `lean` record,
so the previous “item node is unchanged” split rejection does not apply.
No proof, source, status, statement, or review field was changed.

The module defines the square and cube data and postpones exactly two theorems,
`SSet.Enhanced.kan_homotopy_coherent_cube_invariance` and
`SSet.Enhanced.kan_homotopy_coherent_cube_zigzag_invariance`. Each belongs to this
node, and each has a source/proof docstring. All definitions have real data.
No object is chosen from an unproved existence theorem. `autoImplicit` is false.
There is no statement dispute or statement correction.

Clause-by-clause rendering:

- Small simplicial sets and the fixed containing universe: every object is
  `SSet.{u}`, with `universe u` explicit. The six span vertices of two squares
  have `KanComplex` fields; the two apices `A,A'` are arbitrary simplicial sets.
  The statement does not explicitly require the apices to be Kan, and its proof
  works for arbitrary `A` by the exponential Kan theorem. In particular this
  delivery adds no fibrancy hypothesis on an apex.
- For the span `u:U → W`, `v:V → W`, the object `P(u,v)` is the existing
  `simplicialHomotopyPullback s.u s.v`, not a new copy. Its definition is the
  exact iterated categorical pullback at the two endpoint evaluations from the
  node, and SSet limits are degreewise.
- A homotopy-commuting square: `KanCubeSquare` has objects `A,U,V,W`, the Kan
  proofs for `U,V,W`, maps `u,v,f,g`, and `H : A ⟶ (ihom Δ[1]).obj W`.
  `H_zero` and `H_one` are its specified endpoints `f ≫ u` and `g ≫ v`.
  This is the adjoint of the specified simplicial homotopy; it retains every
  simplex, rather than only a homotopy of realized maps or vertexwise paths.
- Its comparison sends `(f,g,H)` into the path pullback:
  `KanCubeSquare.comparison` calls the already landed
  `specifiedHomotopyPullbackComparison` with exactly those three coordinates
  and the two endpoint proofs. This construction is two universal pullback
  lifts. A comparison is not an arbitrary extra square datum.
- Homotopy pullback means this map is a weak homotopy equivalence:
  `KanCubeSquare.IsHomotopyPullback` is exactly
  `IsWeakHomotopyEquivalence s.comparison`. The latter predicate is the recorded
  realization-based component/homotopy-group definition, not a replacement.
- Strict squares are included by `H = (f ≫ u) ≫ constantDiagrams Δ[1] W` and the
  strict commutation equality. No nonconstant path is forced, no fibration
  assumption is imposed, and the theorem quantifies over every `H` satisfying
  the two endpoint equations.
- The two squares are parameters `s,s'`. `KanCoherentCube.a,b,c,d` have exactly
  the node's four directions; `ha,hb,hc,hd` assert weak homotopy equivalence
  separately for all four maps. `H_u,H_v,H_f,H_g` are the four specified side
  homotopies, oriented as `du ≃ u'b`, `dv ≃ v'c`, `bf ≃ f'a`, `cg ≃ g'a`.
- The boundary through `dH` is composed in `left_first,left_second`:
  `(dH) * (βg) * (v'G)`. The boundary through `H'a` is composed in
  `right_first,right_second`: `(αf) * (u'F) * (H'a)`.
  Both use the existing `SourceAttachmentFamilyComposes`: a simultaneous
  composition triangle plus an endpoint-fixed homotopy to the supplied
  representative. The intermediate and final paths are data, so this makes
  no canonical strict-concatenation choice and does not forget a side face.
- `coherence : SSet.Homotopy leftBoundary rightBoundary` identifies those
  two actual composite representatives. `coherence_zero` and `coherence_one`
  require its entire endpoint families to be constant in the homotopy
  parameter, at `duf` and `v'g'a` respectively. Without these endpoint equations
  the hypothesis would be weaker; they are present. All equations are maps
  of simplicial sets over the entire parameter `A`.
- The output `comparison : CoherentPathModelComparison b c d H_u H_v` is the
  already landed two-triangle construction with endpoint factors exactly `b,c`
  and path formula `α⁻¹ * dγ * β`. In its existing definition the two triangles
  share their diagonal and force `[α][η]=[dγ][β]`. Thus an arbitrary map with
  those endpoint factors cannot substitute for the specified comparison.
- The first output is its weak homotopy equivalence; on Kan objects this is
  the map's invertibility in the homotopy category. The next output states
  `IsIso` explicitly for its image under `spaceWeakEquivalences.Q`, the exact
  localization used by `spaceHomotopyCategory`. The existential witnesses in
  this conjunct are proofs of the Kan condition on the existing path objects,
  not arbitrarily selected objects or maps.
- Cube coherence identifies the two maps from `A`:
  `Nonempty (SSet.Homotopy (s.comparison ≫ comparison.map)
    (cube.a ≫ s'.comparison))`. Both comparison maps retain the specified `H`.
- Path concatenations mean homotopy classes represented after filler choices:
  comparison data contain the triangles, while
  `∀ comparison', Nonempty (SSet.Homotopy comparison.map comparison'.map)`
  asserts independence of every coherent choice. No interval reversal or
  strict concatenation is asserted or defined.
- Consequently the two square tests agree:
  `s.IsHomotopyPullback ↔ s'.IsHomotopyPullback` is the last conjunct.
- Stability under a finite zigzag is the second theorem. Its
  `Relation.ReflTransGen` uses a disjunction of forward and backward
  `Nonempty (KanCoherentCube ...)` edges. It asserts both an isomorphism of
  endpoint path pullbacks in the same Kan localization and equivalence of
  the endpoint square tests. Reflexivity includes the length-zero zigzag.

Dependencies and reuse (all source signatures/docstrings were opened):

- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib `SSet`, `KanComplex`,
  internal hom and the module's `evaluation`, `constantDiagrams`,
  `IsWeakHomotopyEquivalence`, `spaceWeakEquivalences`, `spaceHomotopyCategory`.
  Its existing `coneCategory` record contains these helper declarations.
- `lem-coef-infinity-source-gluing`, module
  `Sheaf.CategoryTheory.SourceAttachmentGluing`: `simplicialHomotopyPullback`,
  `SourceAttachmentFamilyComposes`, and the factor projections used by the
  existing comparison data. The general gluing theorem is not an assumption
  of this lemma; its shared construction helpers are reused.
- `lem-coef-infinity-homotopy-pullback-pasting`, module
  `Sheaf.CategoryTheory.InfinityHomotopyPullbackPasting`:
  `specifiedHomotopyPullbackComparison`. This is the canonical universal lift,
  and the pasting theorem itself is not a hypothesis here.
- `lem-coef-kan-homotopy-commuting-pullback-invariance`, module
  `Sheaf.CategoryTheory.KanHomotopyCommutingPullbackInvariance`:
  `CoherentPathModelComparison` and `PathModelComparisonFamily`.
  The output type is reused instead of writing the same span comparison twice.
- Added exactly the preceding three already landed owners to `stmt_deps`,
  under brief-stage2 section 5, “STMT_DEPS MAY GAIN LANDED NODES”. No new node
  and no dependency module are necessary. A read-only traversal of their
  statement/proof dependency closures found no path back to this item.
- All recorded stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`,
  `Sheaf.AlgebraicTopology.RealizationWeakEquivalence`,
  `Sheaf.AlgebraicTopology.KanPullbackPathComparison`, and
  `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`.
  The two Mathlib proof leaves are imported as
  `Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated` and
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`;
  the latter also supplies the functor-space Kan leaf.

Edge cases checked before finalizing the statement:

- Empty Kan vertices and empty apices: no `Nonempty`, basepoint, or chosen
  vertex hypothesis occurs. Boundary/coherence fields are maps, so empty
  parameters cause no artificial choices. A path from an inhabited source
  into an empty target remains impossible, as it should.
- Discrete Kan vertices reduce homotopies to equality and the model to the
  ordinary degreewise pullback; the directions of the factor maps agree.
- Identity maps and constant face/square paths recover the strict cube case.
- For groupoid nerves, the equation `[α][η]=[dγ][β]` gives exactly
  `η=α⁻¹ dγ β`. The two cube boundary expressions have the same source and
  target, and substituting this equation gives `λ v'G = u'F H'a`, checking
  both the inverse orientation and the role of coherence.
- `A` may be a non-Kan simplicial set: no `kanA` proof is stored or assumed.
  Kan mapping spaces into `W'` suffice for the node's argument.
- Zero-dimensional lifting and degeneracies are included by the proof plan;
  no dimension bound was introduced. All maps and homotopies remain
  simplicial, including their higher-dimensional naturality.
- Finite zigzags permit both directions and length zero. A common arbitrary
  universe `u` accommodates every finite collection of small simplicial sets.

Searches made with the prescribed tools (raw msearch records remain in the sandbox):

- `msearch.py leanfinder`, query “Homotopy coherent cubes of Kan simplicial sets
  preserve and reflect path model homotopy pullbacks”: eight hits, principally
  `HomotopicalAlgebra.PathObject.trans_P`, `trans`, `trans_ι` and the binary-product
  square in `SSet.Truncated.HomotopyCategory`. Their displayed types concern
  composition of model path objects or product edges, not the item.
- `msearch.py leansearch`, query “Homotopy coherent cube of weak equivalences
  between Kan path pullback squares preserves homotopy pullback”: eight hits,
  including `CategoryTheory.Square.IsPullback.iff_of_equiv`, `of_equiv`, and
  `CategoryTheory.IsPullback.of_iso'`. Their ordinary categorical pullback
  signatures do not express a specified simplicial homotopy-coherent cube.
- `msearch.py loogle`, query `SSet.Homotopy`: eleven hits. The existing
  `SSet.Homotopy` is used directly; its definition and endpoint lemmas were
  opened in Mathlib `SimplicialSet/Homotopy.lean` and `RelativeMorphism.lean`.
  No hit states the cube-invariance theorem.
- `msearch.py grep`, query `coherentCube|coherent_cube|HomotopyCommutingSquare`
  in `AlgebraicTopology`: zero hits.
- `rg` in slopmaster2 `WeilConjectures` for
  `coherentCube|coherent_cube|HomotopyCommutingSquare|KanCoherentCube`, and
  `grep -rn` for the exact blueprint id: no matches.
- `rg` over `lean/Sheaf` for cubes and path pullbacks found the strict invariance,
  homotopy-commuting span comparison, source-attachment path model, canonical
  specified-homotopy comparison, and other coherent-nerve cubes. Their relevant
  signatures were opened. None is this cube theorem; the existing definitions
  are reused as listed above. Exact new names have no match in `lean/Sheaf`,
  Mathlib, upstream sources or `dag/lean_names_upstream.json`.
- DAG text search found this node and its citers, not another node defining
  this exact coherent square-comparison theorem.
  `tools/blueprint_refs.py search 'homotopy coherent cube'` returned zero
  blueprint nodes. No additional notion node was introduced.

Source read: Kerodon https://kerodon.net/tag/02X4 and
https://kerodon.net/tag/032B. The first supplies the evaluation-equivalence
context; it does not itself assert this coherent-cube lemma. The detailed
mathematical source is the retained node's eight-step agent argument, as its
source field already states. This distinction is preserved in the module.

## Second reading by NP

Author self-check under the direct-worker brief; no independent second reader
is claimed or invented. The maintainer performs the independent delivery review.
I reopened the item, the full delivered module, and the reused comparison,
family-composition, endpoint and localization declarations. In the initial
draft the apex binder was not attached to the square, the purported boundary
paths were unrelated to the six supplied face homotopies, relative endpoints
were absent, and the result omitted its comparison homotopy and zigzag clause.
All those defects were repaired before delivery: the square now bundles its
apex; the four composition predicates constrain both exact boundary paths;
coherence fixes both endpoints; the comparison output uses the existing
triangle model; and both the comparison homotopy and zigzag clause are explicit.
A spurious initial Kan hypothesis on the apex was also removed.
I checked conjunction/iff grouping (the final iff is parenthesized),
`α⁻¹ dγ β` orientation, the actual localization objects, and that all new
helpers belong to this node. The existing definitions were imported instead
of duplicated. The single-file compile uses only scompile.py; validation and
delivery results are recorded below.

Validation: scompile.py compiled the final single file as both sandbox and
library module, cleanly, under the prescribed 60-second per-file limit
(sandbox 8.1 seconds, library 15.6 seconds). No global build was run.
The prescribed deliver2.py --no-push dry run passed preflight and per-file
compilation, producing dry-run commit bef683a14c; nothing was pushed by it.
