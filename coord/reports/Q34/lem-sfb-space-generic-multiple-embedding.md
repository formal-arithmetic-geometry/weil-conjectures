## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGenericMultipleEmbedding` states
`AlgebraicGeometry.AlgebraicSpace.exists_generic_multiple_embedding`; its sole proof
is `sorry`. No definition data or auxiliary proof is postponed. The accepted Q28
stage-1 split is unchanged. Its earlier stage-1 unchanged-item refusal does not
apply to this stage-2 assignment (standing brief, stage handoff, 2026-10-22).

Hypothesis and clause correspondence:

- The base scheme and algebraic space are `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
  The small étale module category is exactly the recorded `X.Modules`, with ring
  `X.structureSheaf`, not a category of modules on the Zariski space of points.
- Local Noetherianity on every étale scheme chart is `hln`.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)` in the atlas topology.
  Absolute quasi-separatedness is `hqs`: fibre products of any two affine scheme
  maps have quasi-compact point spaces. This is the affine test for quasi-compactness
  of the diagonal, including arbitrary base schemes. It is the same presentation
  already used by the landed `coherentSubobjects_filtered_colimit` theorem.
- Reducedness is `hred`, on all étale chart schemes. Mathlib `IsReduced` is equivalent
  to reducedness of all local rings (`isReduced_of_isReduced_stalk` and its converse
  instance in Properties.lean).
- Nonempty irreducibility is `hirr : IrreducibleSpace (Point X.obj.obj)`; the class
  includes nonemptiness, not merely preirreducibility of a possibly empty space.
- `G H : X.Modules` have Mathlib quasi-coherence instances. `hG` and `hH` require
  `Scheme.Modules.IsQuasiCoherentFiniteType` on every chart restriction. On the
  locally Noetherian chart schemes imposed by `hln`, this is exactly coherence
  (finite type quasi-coherent modules are coherent). This uses the dependency's
  recorded finite-type interface rather than introducing a second predicate.
- Full support is `hsG` and `hsH`: every Zariski stalk on every étale chart is
  nonzero, using `¬ Subsingleton`. For quasi-coherent modules, geometric stalks
  are faithfully flat extensions of these ordinary local stalks, so the condition
  is exactly full geometric-stalk support, including at nonclosed points.
- Positive integers are natural numbers `a b` with `1 ≤ a` and `1 ≤ b`.
- The ideal is a module `J`, with actual inclusion `j` into the unit module, `Mono j`,
  `J.IsQuasicoherent`, and `¬ IsZero J`. A submodule of the regular module over the
  commutative structure sheaf is precisely a sheaf of ideals.
- `P` together with `p : P ⟶ G` and `Mono p` specifies the product submodule `JG`.
  The displayed equivalence for EVERY module monomorphism `n : N ⟶ G` says exactly:
  all products `j(r) • s` on every étale object belong to N if and only if the actual
  inclusion p factors through N. In particular N=P forces P to contain every
  product; the converse forces it to be the least such subsheaf. Thus this is the
  uniquely specified generated submodule, not an arbitrary source module or an
  unexplained isomorphism to G. Requiring products to lift to N sectionwise is
  equivalent to inclusion in a submodule sheaf: locally existing lifts are unique
  by monicity and therefore glue. This characterization includes sheafification.
- `V : OpenSubspace X` is the recorded representable open subfunctor; its point
  image is required to be nonempty.
- `∏ᶜ fun _ : Fin a ↦ P` and the analogous H expression are the finite direct sums:
  module sheaves form an additive category, in which finite products are biproducts.
  Thus α has exactly the required source and target; `Mono α` is injectivity.
- For every étale chart T factoring through V, the restriction of the SAME ideal
  inclusion j is an isomorphism (`J|V = O_V`), as is the product inclusion p
  (`(JG)|V = G|V`), and the SAME comparison map α is an isomorphism. Quantifying
  over the full subsite of charts factoring through the open is precisely
  restriction to V; no arbitrary comparison isomorphism is substituted for α.

Recorded dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `etalePullback`.
- Mathlib.AlgebraicGeometry.Noetherian: `AlgebraicGeometry.IsLocallyNoetherian`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: specialization of
  `SheafOfModules.IsQuasicoherent` and its recorded slice sheafification instances.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  `Scheme.Modules.IsQuasiCoherentFiniteType`.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: `pointTopologicalSpace`,
  `pointImage` and the underlying `Point` construction.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`; read
  its full signature and docstring as the node requests. No closed immersion
  occurs in the final hypothesis or conclusion, so no closed-space construction
  is introduced. The import retains this recorded statement dependency.
- Added already-landed statement dependencies `def-trf-space-module-scheme-restriction`
  and `def-a1-space-open-subspace`: `schemeRestriction`, `OpenSubspace` from their
  recorded Sheaf.AlgebraicGeometry modules. Their explicit constructions were read.

No proof dependency currently has a Lean record in the read clone. The proof
plan in the docstring names all eight proof dependencies and all five steps,
including the precise exponent c+d in the Artin-Rees argument.

Edge cases: the empty space is excluded exactly by irreducibility. A zero G or H
is excluded exactly by full support on the nonempty space. Zero direct-sum
multiplicities are excluded by positivity. The ideal J=O and V=X remain allowed.
For X=Spec k and nonzero finite-dimensional G,H, choose a=dim H, b=dim G and J=O;
the product characterization gives P=G. For a coherent module with additional
closed-support torsion, the ideal product can remove that torsion, so the theorem
has not silently imposed torsion-freeness or G=O^r. Nonreduced and reducible chart
schemes are not assumed integral; only X has the stated reducedness and
irreducibility. Empty charts satisfy the stalk hypotheses vacuously, as required.
No coefficient or site universe equality has been added.

Sources read: spaces-cohomology.tex, lemma-prepare-filter-irreducible (07UQ) and
lemma-property-higher-rank-cohomological (07UT), final comparison paragraph.
These give precisely the claimed generic-rank, ideal-extension and Artin-Rees
argument. No statement correction or disputed claim is needed.

Searches performed:

- msearch.py leanfinder: "Two full support coherent sheaves on a reduced irreducible
  Noetherian algebraic space admit an injective map between positive direct powers
  after multiplication by a nonzero ideal, generically an isomorphism". Eight
  hits concern germ-injectivity and restriction of scheme sections, not this result.
- msearch.py loogle: "SheafOfModules.IsFinitePresentation, Submodule.smul": no hits.
- msearch.py grep: "idealMul|ideal.*[Mm]odule|[Mm]odule.*[Ss]upport|IsFinitePresentation"
  in Algebra/Category/ModuleCat/Sheaf: five finite-presentation hits, no theorem.
- rg in lean/WeilConjectures and lean/Sheaf for ideal products, support and generic
  embeddings found the scheme-only `Scheme.idealModuleProduct` and its stalk
  theorem, not an algebraic-space embedding. grep for the item id in
  lean/WeilConjectures returned no occurrence. Focused algebraic-space searches
  found the already-landed chart restriction and open-subspace interfaces used
  here. No second definition is written.

Validation: scompile.py compiled the delivered file separately in sandbox and
library module modes on the server (16.5 s and 8.3 s), without errors or unexpected
warnings. autoImplicit is false and the scheme universe is explicitly bound.

## Second reading by Q34

I reopened the node and module and made a second clause-by-clause reading, without
starting another agent (the dispatcher explicitly forbids it). This is a self-check;
the maintainer's independent delivery review remains the independent reading.
The key points checked were that irreducibility includes nonemptiness, support
uses every point on every chart, coherence is interpreted under the Noetherian
hypothesis, and quasi-separatedness tests the absolute diagonal. The least-submodule
condition determines JG with its inclusion, so it does not replace JG by an arbitrary
module P. Taking N=P proves containment of products and taking arbitrary N proves
minimality. On V the SAME maps j,p,α are invertible; hence the comparison is an
isomorphism on the direct sums of G and H after the prescribed identification.
The chart quantifier includes all charts of V, and V is not required affine or
quasi-compact. No hypothesis or conclusion has changed in this second reading.
