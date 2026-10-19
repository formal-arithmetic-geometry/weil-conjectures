## Worker report

The module `Sheaf.CategoryTheory.RelativeJoinFixedSourcePrism` states
`SSet.Enhanced.relativeJoin_fixedSourcePrism`, with `sorry` as its entire proof.
It introduces only concrete auxiliary constructions belonging to this prism:
the cylinder quotient, collapsed point, top endpoint, graph of the vertex,
attachment pushout, its two legs, and its canonical map to the base. All eight
helpers have actual data; none selects a map from an existence theorem.
The compatibility proof inside the pushout desc is just the product and
terminal-object identity, not a postponed mathematical theorem.

Source checked: [HTT, Lemma the project server](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
second specialization on printed p. 433 (PDF p. 451, one-based). The source attaches a left cone
along `Z × {x}`. The node uses the explicit collapsed-cylinder model and expands
the associated simplicial prism; its four proof steps are reproduced in the theorem
docstring. Source quasicategory and fibration hypotheses belong to the subsequent
extension into Y, not to the combinatorial prism stated here. No correction of
the node's statement is needed.

Hypotheses and constructions, matched in their order in the node:

- Simplicial sets in one fixed arbitrary universe: `universe u`,
  `(Z X : SSet.{u})`. There is no quasicategory instance or size restriction.
- A vertex of X as a map from the point: `(x : Δ[0] ⟶ X)`.
- The collapsed cylinder `C_Z` is exactly the existing `fatLeftJoinCone Z`:
  `pushout (stdSimplex.isTerminalObj₀.from Z) (coneCylinderEnd Z 0)`.
  Its indexing object Z identifies `Z × {0}` with Z. Pushouts of simplicial
  sets are degreewise pushouts, so this is the quotient in the node.
- The map c is `fixedSourceCylinderQuotient Z`, the second pushout leg;
  p is `fixedSourceCylinderPoint Z`, the first leg from `Δ[0]`;
  c₁ is `fixedSourceCylinderTop Z`, the top endpoint followed by c.
- `fixedSourceGraph Z x` is `lift (𝟙 Z) (terminal.from Z ≫ x)`,
  namely `z ↦ (z,x)` in all degrees.
- K is `fixedSourcePrismAttachment Z x`, the pushout of that graph and c₁.
  j and k are `fixedSourcePrismProduct Z x` and
  `fixedSourcePrismCylinder Z x`, respectively.
- a is `fixedSourcePrismBase Z x`, defined by `pushout.desc` with
  `snd Z X` on the product and `terminal.from (fatLeftJoinCone Z) ≫ x`
  on the collapsed cylinder. Their agreement on Z is proved structurally.
- T is the recorded `relativeJoin (fixedSourcePrismBase Z x) (𝟙 X)`.
  i_K, i_X, π are the recorded `relativeJoinInl`, `relativeJoinInr`,
  and `relativeJoinProjection` at precisely these two maps.
- `rightJoinCone Z` is the existing `Z ⋆ Δ[0]`;
  `rightJoinConeInclusion Z` is its Z inclusion and
  `orderedJoinInr Z Δ[0]` is its apex map.

Conclusion, one entry for every clause:

1. The existential P has domain `rightJoinCone Z ⊗ X` and codomain T.
   The first conjunction is `P ≫ π = snd (rightJoinCone Z) X`, exactly “over X”.
2. The existential J has domain `rightJoinCone Z ⊗ Δ[1]` and codomain T.
   The second conjunction is `J ≫ π = terminal.from _ ≫ x`, exactly
   “over the constant vertex x”.
3. Restriction of P to Z × X is precomposition with
   `rightJoinConeInclusion Z ⊗ₘ 𝟙 X`, equal to `j ≫ i_K`.
4. Restriction of P to the apex × X is precomposition with
   `orderedJoinInr Z Δ[0] ⊗ₘ 𝟙 X`, equal to `snd Δ[0] X ≫ i_X`.
   The projection identifies point × X with X, as in the node.
5. Restriction of J to time 0 is precomposition with
   `coneCylinderEnd (rightJoinCone Z) 0`, equal to the constant map
   `terminal.from _ ≫ p ≫ k ≫ i_K`.
6. Restriction of J to time 1 is precomposition with
   `coneCylinderEnd (rightJoinCone Z) 1`, equal to
   `lift (𝟙 _) (terminal.from _ ≫ x) ≫ P`, precisely P at x.
7. Restriction of J to Z × Δ[1] is precomposition with
   `rightJoinConeInclusion Z ⊗ₘ 𝟙 Δ[1]`, equal to `c ≫ k ≫ i_K`.
8. The final two equations specify the entire apex interval, after
   precomposition with `orderedJoinInr Z Δ[0] ⊗ₘ 𝟙 Δ[1]`.
   Its first relative-join coordinate is the splitting map `relativeJoinRho Δ[0]`
   with the initial point sent by `p ≫ k` and the final point sent by x.
   Its second coordinate is `(t,x_n)`, with t the interval projection.
   These are exactly the canonical relative-join edge from k(p) to x,
   including all its degenerate simplices. The two coordinates jointly
   determine a map into the degreewise pullback, so this neither weakens
   the clause to an arbitrary edge with those endpoints nor strengthens it.
9. Empty Z is covered by the unrestricted binder. The initial blocks are then
   empty, `C_Z` and K are points up to their canonical pushout identifications,
   P is the final inclusion, and J is the canonical point-to-x edge.
   No nonemptiness, quasicategory, fibration, filteredness or colimit hypothesis
   occurs anywhere in the signature.

Dependency declarations used and read with their defining code/docstrings:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the enhanced simplicial
  conventions and `SSet.Enhanced.coneCategory` were checked; this theorem
  uses their underlying Mathlib simplicial-set, standard-simplex and product
  encoding, without requiring a cone to be universal.
- `Sheaf.CategoryTheory.RelativeInfinityCone`:
  `SSet.Enhanced.rightJoinCone`, `rightJoinConeInclusion`.
  The underlying `orderedJoinFunctor`, `orderedJoinInr` supply the apex.
- `Sheaf.CategoryTheory.RelativeJoin`:
  `SSet.Enhanced.relativeJoin`, `relativeJoinProjection`, `relativeJoinInl`,
  `relativeJoinInr`, `relativeJoinFst`, `relativeJoinSnd`, `relativeJoinRho`.
  Their degreewise pullback and splitting definitions were read in full.
- `Sheaf.CategoryTheory.InfinityJoinConeCalculus`:
  `SSet.Enhanced.fatLeftJoinCone`, `coneCylinderEnd`. The existing node
  `lem-coef-infinity-join-cone-calculus` is added to stmt_deps solely to reuse
  these already landed constructions; its large equivalence theorem is unused.
- Mathlib `stdSimplex.isTerminalObj₀`, Cartesian `lift`, `snd`, tensor of maps,
  and `CategoryTheory.Limits.pushout`, `pushout.inl`, `pushout.inr`,
  `pushout.desc`. No alternative join, interval or collapsed cone is defined.

Edge cases checked before writing: Z empty as above; Z a point with X a point
(the prism is the two triangles sharing the prescribed interval); Z a point
with X = Δ[1] and either vertex x; constant interval parameters 0 and 1;
pure Z and pure apex cone blocks; and simplex operators discarding either block.
The node's two-case J rule agrees when a nonempty zero tail disappears under
restriction because the surviving cylinder block is constant p. In degree zero
the equations give exactly the specified vertices. Empty X supplies no vertex x,
as required by the source hypothesis, rather than imposing a new nonemptiness
hypothesis. All objects use the same arbitrary u, including the empty Z case.

Searches for an existing statement, performed through msearch.py and direct rg:

- LeanFinder query: `Simplicial relative join fixed source cylinder prism with exact endpoint restrictions`.
  Eight hits include `CategoryTheory.PreOneHypercover.cylinder_I₀`, `SSet.ι₁`,
  `SSet.ι₀_snd`, `SSet.ι₁_snd`, and general model-category cylinders.
  These supply interval operations, not the fixed-source relative-join theorem.
- LeanSearch query: `Simplicial relative join fixed source cylinder prism`.
  Eight hits include general model-category precylinders and
  `SSet.RelativeMorphism.Homotopy.mk`. None has the required relative join
  or exact apex normalization.
- Loogle query: `"SSet.join"`: zero hits.
- Mathlib grep via msearch.py:
  `relativeJoin|join.*[Cc]ylinder|[Cc]ylinder.*join`, subdirectory
  `AlgebraicTopology`: zero hits.
- rg over upstream `WeilConjectures` and project `lean/Sheaf` for
  `relativeJoin|fixedSourcePrism|fixed.source.*prism`: upstream has no match;
  project has the relative-join interface, relative-join prism comparison and
  cocartesian-cylinder extension, but no fixed-source prism. Their signatures
  concern different constructions and do not give this theorem.
- `grep -rn` for this item's blueprint id in upstream `WeilConjectures`: no match.
- rg for the proposed declaration/helper names in upstream, project Lean and
  `dag/lean_names_upstream.json`: no match.
- A broader source search for cylinder pushouts found the exact existing
  `fatLeftJoinCone` and `coneCylinderEnd`, which this delivery reuses.

No new DAG nodes, dependency repairs, disputed statements, or statement corrections.
All helper declarations are listed in lean.declarations and have source/blueprint
docstrings. The node differs only in lean and its one added landed stmt_dep.
The theorem's recorded signature is copied verbatim from the file.

Validation: scompile.py compiled the final module cleanly, both the sandbox check
and its library-path confirmation, approximately 1.3 and 1.4 seconds respectively.
Only the theorem is postponed. The initial compile exposed a redundant tactic
following a solved terminal-object identity; removing it gave the clean result.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
