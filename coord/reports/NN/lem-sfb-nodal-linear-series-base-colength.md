## Worker report

The delivery states `AlgebraicGeometry.exists_nodal_linear_series_base_colength` in
`Sheaf.AlgebraicGeometry.NodalLinearSeriesBaseColength`. Its sole proof is `sorry`.
Seven auxiliary definitions name constructions already specified by this item; all have
real data, source docstrings, and this item's blueprint tag. They are listed in
`lean.declarations`. The delivery reuses the already landed definition-node owner for the dualizing-pair
definitions; no Lean declaration or definition node is duplicated. The node's statement, proof, and proof dependencies
are unchanged. The only added statement dependency is
`def-sfb-reduced-curve-dualizing-pair`, which owns the existing
`ReducedCurveDualizingPair` and `moduleCohomologyOverField` definitions.

Sources read: Franciosi--Tenni, author-hosted primary PDF
https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf, Proposition 2.17(ii), printed p.233,
and Theorem 3.9 proof, printed p.247 (PDF p.23); and the local Stacks definitions/interfaces
for the node's dependencies. The relevant p.247 proof decomposes sections by component
support, obtains vanishing at crossing nodes, and adjoins the base cluster without changing
its complete section space. The node deliberately isolates that elementary evaluation-ideal
argument, rather than the two-connected Clifford inequality of the paper's theorem.
The supplied CompactObject example is now a withdrawn module with no declarations; the
module header follows the live NodalLineSerreRiemannRoch and ReducedCurveDualizingModule.

Hypotheses and clauses, in the order of the natural-language node:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Specified k-scheme, projective, nonempty connected and reduced:
  `(X : Scheme.{u}) [X.Over (Spec (.of k))]`,
  `[IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]`.
  ConnectedSpace includes Nonempty; there is no extra irreducibility or smoothness assumption.
- Pure dimension one: `hpure : X.IsPureDimension 1`.
- Smooth except for the stated completed nodes: `hnodal` quantifies over closed points
  outside the structural morphism's `smoothLocus`. Its ring equivalence has exactly
  `AdicCompletion (maximalIdeal (O_x)) O_x` and `MvPowerSeries (Fin 2) k / (X 0 * X 1)`
  as source and target. Its equation on every `a : k` explicitly enforces compatibility
  with the structure map, so this is a completed **k-algebra** identification, rather
  than an arbitrary ring equivalence. No restriction on characteristic is imposed.
- Invertible module: `(L : X.Modules) [L.IsInvertible]`.
- Finite-dimensional space of global sections: `V : Submodule k (unit X ⟶ L)` and
  `[FiniteDimensional k V]`. A morphism from O_X is the actual global section obtained
  by applying it to 1. This is the usual canonical identification with Gamma(X,L) and
  hence with H^0 of the recorded Zariski module cohomology; it is not the unrelated
  abelian-sheaf cohomology. The statement has no positive-degree cohomology clause.
- One section nonzero on every generic point: `hgeneric` is a **single** `s ∈ V` with
  all `nodalSeriesGenericValue L s C ≠ 0`, using the existing
  `genericPoints.ofComponent C`. It is not the weaker assertion allowing a different
  section for every component.
- The evaluation base ideal B: the conclusion produces `B : X.IdealSheafData` with
  `B.ideal U • ⊤ = Submodule.span Γ(X,U) {s.app U 1 | s ∈ V}` on **every affine open**.
  For an invertible L this determines B uniquely: locally trivialize L and cancel its
  generator. It says exactly L times B is the evaluation image, including the canonical
  embedding, with no arbitrary map substituted. Existential characterization avoids any
  choice of uncharacterized data and is equivalent to defining the evaluation ideal.
- Coherence of B: `RingedSpace.IsCoherent X.toRingedSpace B.toModules` is the genuine
  finite-type-kernel coherence predicate, rather than just finite generation.
- Its zero scheme and finite b: `topologicalKrullDim B.subscheme ≤ 0` and
  `FiniteDimensional k (nodalSeriesCoordinateSpace k B)`.
  `nodalSeriesLength k B` is precisely `finrank k Gamma(V(B),O)` with scalar restriction
  along `B.subschemeι ≫ X ↘ Spec k`. Thus the empty scheme has length zero.
- An arbitrary partition of components is `(P : Setoid (irreducibleComponents X))`;
  its blocks are `Quotient P`. This does not assume that the blocks are connected or
  indexed by a particular finite type.
- The supported subspaces are `W : Quotient P → Submodule k V` with the exact
  membership equivalence: the generic values vanish on all components whose quotient
  class differs from the block. W is uniquely specified by this equivalence, not an
  arbitrary collection of subspaces. `iSupIndep W` and `iSup W = top` are precisely
  the internal direct sum condition. These conditions cover every partition in the
  node and introduce no choice of generators or extra geometric hypothesis.
- E_P: `nodalSeriesBoundary P` is the set of points lying on components in different
  classes. `nodalSeriesBoundaryIdeal P` is its reduced vanishing ideal, initially formed
  using closure so the definition has real data with no postponed closedness proof.
  The theorem asserts its support is **exactly** that set (not just its closure), that
  the set is finite, every point is closed and nonsmooth, the scheme is reduced, and
  its coordinate space is finite dimensional. With hnodal these are exactly the reduced
  finite crossing nodes of the node. No self-node on an individual component is counted.
- For each block a, A and C are exactly the reduced component union and its reduced
  complementary union, specified by equalities to `nodalSeriesUnionIdeal`.
  `(A + C).support = nodalSeriesBlockBoundary P a` gives the precise boundary set;
  its finiteness and `nodalSeriesLength k (A+C) = boundary.ncard` give its k-length.
  The displayed isomorphism from `∐ (Fin n) Spec k` to the **actual fibre product**
  `pullback A.subschemeι C.subschemeι` gives the scheme-theoretic intersection as a
  disjoint union of reduced k-points. The equation for every coproduct inclusion makes
  this an isomorphism over k, and n equals the cardinality of the boundary set.
  The standard sum-ideal closed subscheme is this scheme-theoretic intersection.
- Inclusion and inequality: `B ≤ nodalSeriesBoundaryIdeal P` and
  `boundary.ncard ≤ nodalSeriesLength k B`.
- Complete-series case: under `V = top`, the canonical inclusion
  `(L ◁ B.toModulesι) ≫ (ρ_ L).hom` is bijective on top sections.
  This states equality **inside** Gamma(X,L), with the actual tensor inclusion.
- Canonical Cartier case: still under `V = top`, for every existing
  `D : ReducedCurveDualizingPair k X` and effective Cartier ideal T,
  `T.IsInvertible`, `dim T.subscheme ≤ 0`, and `Nonempty (L ≅ T.toModules ⊗ D.omega)`
  render exactly `L = I_T tensor omega_X`. Quantifying over the representing pair
  avoids imposing a choice of dualizing module; its uniqueness is the recorded
  dependency's interface. No invertibility of the enlarged cluster is assumed.
- The enlarged cluster is the real ideal product `T * B`. The theorem asserts its
  coherence, dimension at most zero, finite coordinate dimension, and `T * B ≤ T`
  (equivalently V(T*B) contains V(T)). Its length equation is exactly
  `length(T*B) = length(T) + length(B)`.
- The last section equality is equality of the ranges of the **canonical** multiplication
  inclusions `(T*B).toModules tensor D.omega → D.omega` and
  `T.toModules tensor D.omega → D.omega`. It therefore preserves the common ambient
  H^0(omega_X), not merely its dimension or an unspecified isomorphism.

Dependency declarations used (the recorded interfaces were opened and their signatures read):

- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible` (locally regular principal, precisely effective Cartier).
- Mathlib `CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`;
  Mathlib scheme pullbacks/coproducts provide the indicated schemes.
- Mathlib `AlgebraicGeometry.Properties`: `IsReduced`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, publicly exposed by
  NodalLineSerreRiemannRoch: `SheafOfModules.cochainModulesMonoidal`; the delivered expressions
  use the canonical tensor, whiskering and unitors of the module category.
- Mathlib `AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`, `IdealSheafData`,
  `vanishingIdeal`, product/sum of ideals; Mathlib `IdealSheaf.Subscheme`:
  `IdealSheafData.subscheme`, `subschemeι`.
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies their canonical
  module realization `toModules` and inclusion `toModulesι` (the closed-ideal dependency's
  recorded note expressly specifies this bridge).
- Mathlib `AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`: `RingedSpace.moduleCohomology`;
  `WeilConjectures.AlgebraicGeometry.Modules.Linear`: the canonical k-action on Hom spaces.
- Mathlib `FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; `Topology.Connected.Basic`:
  `ConnectedSpace`; `Topology.Irreducible` and `Topology.Sober`: `irreducibleComponents`
  and `genericPoints.ofComponent`.
- Mathlib `RingTheory.AdicCompletion.Basic/Algebra`: `AdicCompletion`, `AdicCompletion.of`;
  `RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `X`, `C`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch`:
  `exists_nodal_line_serre_riemann_roch`; it supplies the nodal duality context and imports
  the common module, scalar and tensor interfaces. The hnodal binder here retains the
  k-algebra compatibility explicitly required by this node.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, through the preceding module, and
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- Existing definition-node owner `def-sfb-reduced-curve-dualizing-pair` (Q86) records
  `Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule`:
  `ReducedCurveDualizingPair` and its `omega` field, the existing representing pair.

Plain proof imports cover every stated proof dependency: projective-to-proper,
coherent kernel/cokernel/sum, nowhere-dense dimension drop, finite closed zero schemes,
Stacks nodal closed subcurves, Euler additivity, zero-dimensional Euler support, and
coherent finite type over locally Noetherian schemes. The recorded proper-field
preparation node has no Lean record, so has no module to import; it is not needed to
form any binder or construction of this statement. The full six-step proof is in the
main theorem's docstring, including the elementary support and Cartier multiplication
calculations.

Edge cases checked mathematically: a base-point-free V on P^1 has B=top, empty Z and b=0;
a one-block partition has empty E and empty complementary scheme; an irreducible nodal
curve's self-nodes are not crossing nodes; on two P^1 components meeting in one node,
the split space of sections vanishing at that node gives B equal to its maximal ideal
and b=1=#E; a complete nonsplit series imposes no partition conclusion unless its supported
subspaces really give an internal direct sum; the empty Cartier cluster has T=top,
T*B=B and length(T)=0. B need not be Cartier at a node. The scheme X is nonempty by
ConnectedSpace, but Z and every intersection may be empty; Fin 0 in the coproduct allows
exactly that case. All universes are explicit and neither autoImplicit nor relaxed
implicit binding is enabled.

Searches, all performed before the theorem was written:

- `msearch.py ... leanfinder`: "Base ideal of a linear series on a nodal curve contains
  boundary nodes and has finite colength". Eight hits, all Weierstrass coordinate ideals
  or power-series ideal lemmas; no match for the theorem.
- `msearch.py ... loogle`: "IdealSheafData, span". Zero hits; the remote Loogle index
  did not know IdealSheafData, so this does not establish absence by itself.
- `msearch.py ... grep`: "baseIdeal|baseLocus|evaluation", AlgebraicGeometry. Fourteen
  hits, mostly general evaluation at residue fields or Weierstrass curves; no match.
- `msearch.py ... leansearch`: "The base ideal of a line bundle linear series on a
  reduced nodal curve has finite colength and contains nodes between support blocks".
  Eight hits, including the generic vanishing-ideal/support API, but no nodal series theorem.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for base ideals/loci,
  evaluation images, supported sections and linear series; direct item-id grep upstream;
  `rg` of the proposed names in `dag/lean_names_upstream.json` and both libraries.
  No existing declaration of this theorem or the specialized helpers. The unrelated
  RootTowerCoordinateFace.baseIdeal is an affine root-tower construction, not this notion.
- The component/duality search found ReducedCurveDualizingPair, which is reused instead
  of defining another dualizing notion. The helpers are composed directly from germs,
  vanishingIdeal, closure and restriction of scalars, not replacements for those APIs.

No STATEMENT-DISPUTED issue or source correction was found. The current source spelling
`Setoid.r` was checked by compilation. A preliminary invalid attempt to package a finite
boundary as closed using a T1 assumption was removed; the delivered statement instead
asserts the underlying support-set equality and the closedness of every boundary point,
which does not assume the scheme is T1.

Validation: scompile.py NN lem-sfb-nodal-linear-series-base-colength ran the sandbox and
library module checks successfully (7.8 s and 3.2 s); no errors or residual warnings.
Delivery preflight results are recorded below once completed.

## Second reading by NN

This is a separate self-audit pass, not a claim of review by another worker; the dispatch
brief prohibits starting agents and assigns independent review to the maintainer.
I re-read the node and the actual compiled signature in order. The generic condition
uses one common section. The partition uses equivalence classes of actual components,
not connected components of X. Both independence and spanning are present. Boundary
sets use distinct classes and are asserted to be exactly the supports, so closing the
sets in their real definitions does not enlarge the result. The intersection is a
scheme fibre product and its isomorphism is over k. The two complete-series conclusions
are under V=top; the final one also requires the regular-principal ideal and the specified
identification with the existing dualizing module. Both section equalities use the
canonical embeddings rather than equality of dimensions. Empty subschemes and single
blocks are included. The explicit scalar equation corrects the potential distinction
between completed ring and completed k-algebra isomorphisms. No mismatch remains.

Delivery dry run: `deliver2.py NN lem-sfb-nodal-linear-series-base-colength --no-push`
reported OK at provisional commit `36707546d28`: preflight and per-file compilation passed.


## Repair of return at b1106b420bc3

1. The definition node `def-sfb-reduced-curve-dualizing-pair` has now landed from Q86's
   delivery for `lem-sfb-nodal-subcurve-dualizing-annihilator`. I read its current
   statement, lean record, and both definitions at ReducedCurveDualizingModule.lean:71-90.
   It owns exactly the same `AlgebraicGeometry.ReducedCurveDualizingPair` and
   `AlgebraicGeometry.Scheme.Modules.moduleCohomologyOverField` declarations required
   here. Removed this delivery's duplicate node JSON entirely from the sandbox. The
   consumer retains its dependency on the already landed definition node and imports
   its recorded module. No change to the landed node is proposed. Reconstructed the
   consumer node from current main plus only lean and stmt_deps; its statement, proof,
   proof_deps and other fields remain those of main. The Lean file and signature remain
   unchanged. Updated the consumer lean.note and this report to identify the existing
   owner accurately. The delivery now contains only the consumer node, module and report.

The earlier B3/H12 defect remains repaired: the consumer cites the definition node,
not the existence theorem node, for its plain structure. The earlier duplicate node's
blueprint metadata is no longer part of this delivery. There are no new nodes or
dependency-module repairs in this revision.

Second-reading supplement: the landed Q86 node's coherent omega, k-linear duality on
all coherent test modules, contravariant naturality, and scalar-restricted O-module
cohomology match the declarations used in the consumer. Its definition asserts no
existence or connectedness condition, so this substitution adds no hypothesis and
changes no clause. The final Cartier condition still binds the same representing pair
and uses its omega field. The main theorem's signature was compared verbatim to the
record; only classification of the existing dependency changed. Independent review
remains the maintainer's; no second agent was started.

Validation of this repair: scompile.py passed the unchanged sandbox and library checks.
The dry run reported OK at provisional commit 2f3a64be5bd: preflight and compilation
passed, staging only the consumer module, consumer node, and report. No definition-node
file is included in this revision.
