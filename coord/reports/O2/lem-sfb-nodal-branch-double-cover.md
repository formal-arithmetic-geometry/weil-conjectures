## Worker report

This is a stage-2 statement delivery for lem-sfb-nodal-branch-double-cover. The live
node has an approved stage-1 split by NX dated 2026-10-22 but no Lean record; an
approved split is precisely the prerequisite for this stage, not a reason to split it
again. No stage-1 field is changed. The original statement and eleven-step proof
remain verbatim. The approved proof is included, step by step and with its uses,
in the main theorem's docstring.

The delivered modules are Sheaf.AlgebraicGeometry.NodalBranchScheme and
Sheaf.AlgebraicGeometry.NodalBranchDoubleCover. The former constructs the actual
scheme and its projection. The latter states the complete conclusion for all
families simultaneously, allowing its base-change comparisons to satisfy identity
and composition laws. The final declaration is
AlgebraicGeometry.nodal_branch_double_cover.

The construction has real data. First form the graph s=(i,id) in X times_T D. Its
closed-then-open coborder factorization gives j:D -> W, and the branch scheme is
pullback j.ker.blowupMap j with its second projection. On an affine graph chart the
exceptional fibre of Proj of the Rees algebra is Proj of the ideal-power quotients:
base change to the centre quotients degree n by J^(n+1). Thus it is exactly the
relative graph-cone construction of proof Steps 2-3. The canonical coborder
neighbourhood is used so no global closed-graph/separatedness hypothesis is added.
The only postponed part of this construction is the graph immersion proof, in
the named theorem nodalBranchGraph_isImmersion. It concerns proof data only.
No branch scheme, graded algebra, normalization or arbitrary map is chosen from
an unconstrained existence theorem.

Hypotheses of the item are bundled in NodalBranchFamily:

* Schemes X,T and morphism f are the fields X,T,f, in one explicit universe u.
* Flatness is the instance field flat : Flat f.
* Local finite presentation is lfp : LocallyOfFinitePresentation f.
* Every geometric fibre is tested by geometric, quantifying over every algebraically
  closed field Omega : Type u and g : Spec Omega -> T. The Nonempty antecedent
  permits empty fibres. IsPureDimension 1 requires every irreducible component
  to have dimension one. No connectedness hypothesis is present.
* At each point outside (pullback.snd f g).smoothLocus, geometric uses the already
  recorded IsGeometricOrdinaryDoublePoint Omega (pullback f g) x. Its full signature
  and definition were read: the completion is at the actual stalk's maximal ideal,
  and its comparison ring is MvPowerSeries (Fin 2) Omega modulo the product X 0 * X 1.
  The recorded definition uses a ring isomorphism; it is reused without a private
  copy or a different completed-local-ring convention.

Each clause of the conclusion is retained in NodalBranchDoubleCoverSystem:

* D is singular, an abbreviation for (Scheme.firstFittingIdealSheaf F.f).subscheme;
  inclusion is exactly Scheme.firstFittingSingularSubscheme F.f, and singularBase
  is its composite with F.f. These abbreviations reuse the existing dependency.
* B_f and p are branches and projection, abbreviations for the graph construction
  in the new definition node, not free fields of the conclusion.
* finiteEtale asserts IsFinite projection, Etale projection and
  projection.IsFiniteLocallyFreeOfDegree 2. FiberDegree.lean defines the last
  predicate as finite, flat, locally finitely presented, with fibre rank two.
  By the recorded lem-pc-flf-properties this is precisely the locally free rank-two
  direct-image description in the node.
* normalizationIso is an actual isomorphism in Over (F.singularBase.fiber t).
  Its left side is pullback.snd F.projection (F.singularBase.fiberι t), the branch
  scheme restricted to D_t; by pullback pasting its domain is (B_f)_t.
  Its right side is pullback.snd (F.f.fiber t).fromReducedNormalization
  (F.singularFiberInclusion t), exactly X_t^nu times_{X_t} D_t over D_t.
  The map singularFiberInclusion is the actual pullback.map of the original
  first-Fitting inclusion, not a supplied arbitrary morphism.
* singularFiberReduced asserts IsReduced (F.singularBase.fiber t).
* singularFiberPoints identifies the range of singularFiberInclusion with the
  complement of the smooth locus of the fibre's map to Spec kappa(t).
* twoGeometricBranches gives Nat.card (pullback projection g) = 2 at every
  algebraically closed geometric point of D. Its interpretation as normalization
  branches is the preceding scheme isomorphism, applied after geometric base
  change, not a separate definition of points or branches.
* singularMap and singularCartesian give the singular scheme's identification
  for every cartesian square x,a of families. The equation in IsPullback forces
  this map to be the map of the actual closed singular inclusions. The square
  being cartesian is the canonical D_{f'} = D_f times_T T' identification.
* branchMap and branchCartesian give the corresponding identification for the
  actual graph branch schemes, compatibly with p. Pasting the two cartesian
  squares with the square of families gives B_{f'} = B_f times_T T'.
* singularIdentity, branchIdentity, singularComposition, branchComposition give
  identity and composition compatibilities on these maps. Cartesian squares
  include every isomorphism of families; composing the two inverse squares gives
  inverse maps by these laws, so isomorphism functoriality is included.
* Arbitrary base changes are present without any further hypothesis on a.
  The helper baseChange_geometric states the inherited geometric hypotheses;
  baseChange constructs the actual pullback family, using that named theorem for
  its proof field. Thus the system's quantification never depends on supplying
  an extra nodality assumption after base change.
* finitePresentationFibers assumes QuasiCompact f and QuasiSeparated f, in addition
  to the locally finite presentation already in the family. This is exactly
  'finitely presented'. For every t it asserts finite and etale for D_t -> Spec
  kappa(t), and finite and etale for B_t -> D_t -> Spec kappa(t).
* properFinite asserts finite for D -> T and B -> T when IsProper f. Properness
  already supplies quasi-compactness and separatedness, hence the preceding finite
  presentation condition. No extra global properness is used in earlier clauses.

The theorem asserts Nonempty of this fully specified simultaneous conclusion.
There is no definition choosing a system from this theorem. Its fields retain
comparison maps and their laws rather than merely asserting unrelated isomorphisms.
All non-definitional theorem proofs in the delivery are sorry, with source and
proof plan: nodalBranchGraph_isImmersion (the new definition node),
NodalBranchFamily.baseChange_geometric (the item's arbitrary-base-change clause),
and nodal_branch_double_cover (the item).

Dependency declarations read and used:

* Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme:
  Scheme.firstFittingIdealSheaf, Scheme.firstFittingSingularSubscheme, including
  the uniquely characterized ideal-sheaf construction and the closed immersion instance.
* Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
* Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
* Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  pullback, pullback.fst, pullback.snd, pullback.lift, pullback.map.
* Mathlib.AlgebraicGeometry.Morphisms.Smooth:
  AlgebraicGeometry.Smooth and Scheme.Hom.smoothLocus.
* Mathlib.Topology.KrullDimension: topologicalKrullDim, used through
  Scheme.IsPureDimension in Sheaf.AlgebraicGeometry.PureDimension.
* Mathlib.RingTheory.AdicCompletion.Basic: AdicCompletion; and
  Mathlib.RingTheory.MvPowerSeries.Basic: MvPowerSeries, both used through
  IsGeometricOrdinaryDoublePoint in Sheaf.AlgebraicGeometry.ProjectiveNodalTower.
* Sheaf.AlgebraicGeometry.ReducedNormalization:
  Scheme.reducedNormalization and Scheme.fromReducedNormalization, the disjoint
  union of normalizations of the reduced irreducible components.
* Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite.
* Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale.
* Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper.
* Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and
  Scheme.fromSpecResidueField, via the actual Scheme.Hom.fiber constructions.
* WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:
  Scheme.Hom.IsFiniteLocallyFreeOfDegree.
* Mathlib.AlgebraicGeometry.Morphisms.Immersion: Scheme.Hom.coborderRange and
  Scheme.Hom.liftCoborder, the canonical closed-then-open factorization.
* WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup and blowupMap.

The modules of every already recorded proof dependency are also imported, with
ordinary non-public imports where used only by the future proof. The two new local
algebra proof nodes lem-sfb-augmented-etale-associated-graded and
lem-sfb-nodal-local-tangent-normalization have no Lean record at this delivery;
this statement does not need either notion as a statement dependency.

Edge cases checked mathematically before writing:

* Empty X, empty T, and smooth families have empty D and B; finite-etale degree two
  over the empty scheme is vacuous, and the fibre normalization products are empty.
* Disconnected geometric fibres are allowed. Equidimensionality is componentwise;
  the connected-nodal predicate was deliberately not substituted for this hypothesis.
* The smoothing uv=h gives D=V(u,v,h), and after restricting to D the graph cone
  is A[u,v]/(uv). In particular h=t^2 leaves a nonreduced total singular scheme
  over a nilpotent base, while the individual D_t remain reduced as asserted.
* Split nodes over an algebraically closed field give two copies of the base;
  a nonsplit real node gives a quadratic etale algebra, not two rational points.
  The isomorphism is over D_t, not merely over an algebraic closure.
* Characteristic two is not excluded: uv is still a split geometric node and the
  two tangent directions remain distinct; no division by two occurs.
* A non-quasi-compact disjoint union of nodal curves may have infinitely many nodes;
  finiteness of D_t and B_t is conditional on finite presentation, not unconditional.
* The graph need not be closed globally for a nonseparated family. The coborder
  construction avoids adding separatedness or taking a problematic global kernel
  before restricting the graph to a neighbourhood where it is closed.
* Arbitrary nonflat and nilpotent base changes are included. The exceptional-fibre
  comparison is a nodal assertion; the statement does not assert arbitrary-base-change
  compatibility for the blow-up of an arbitrary ideal or normalization of a total space.

Searches for existing declarations were run by the prescribed msearch.py, with its
unmodified results in searches.jsonl:

* leanfinder: 'A nodal family has a canonical finite etale double cover of its singular
  subscheme consisting of its two normalization branches, compatible with arbitrary
  base change'. Eight hits about standard etale presentations, etale algebras over
  fields, and polynomial factorization rings; none constructs this branch scheme.
* loogle: '"AlgebraicGeometry", "nodal"'. No hits.
* grep: 'nodal|branchCover|tangentCone', AlgebraicGeometry. No Mathlib hits.
* leansearch: 'For a nodal family the exceptional fibre of the blowup along the graph
  of the singular subscheme is the scheme of its two branches'. Eight hits about
  Scheme.Hom.fiber, smoothness and finite fibres; none defines the graph branch scheme.
* rg of WeilConjectures and Sheaf for nodal, Nodal, branchCover, BranchCover,
  graphCone and conormal graded constructions found the existing fibre predicates,
  local curve-branch algebras, normalization and conormal infrastructure, but no
  branch-cover construction. The exact item id has no upstream theorem declaration.
* rg of dag/nodes for graph conormal, projectivized graph, and branch scheme found
  the item and its users, plus unrelated local conormal results, but no definition
  node for this actual relative branch scheme. tools/blueprint_refs.py search
  'branch scheme' returned zero blueprint matches.

The cited local source was opened: curves.tex remark-quadratic-extension (0CBT),
lemma-split-node (0CBW), lemma-etale-local-structure-nodal-family (0CBY), and the
current graph-cone split. There is no statement correction or disputed assertion.

Both delivered modules compile cleanly through scompile.py, separately in dependency
order against the live server library. No global or local lake build was run.

## New nodes

Added def-sfb-nodal-branch-scheme. It defines the actual graph-exceptional-fibre
construction described above, with its graph, canonical closed neighbourhood and
projection. Its source is the projectivized tangent cone of Stacks 0CBT (3),
relativized by the charts of 0CBY. It uses existing first-Fitting singular schemes,
fibre products, immersion factorization and global blow-up, so it introduces no
private replacement of those notions. It has the four recorded searches above.
The main item's stmt_deps gains this definition node and the already landed nodes
def-weil-pure-dimension, def-trf-projective-nodal-tower and
 def-pc-finite-locally-free whose exact existing declarations are used.

No dependency Lean record was repaired, and no dependency module is delivered.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
