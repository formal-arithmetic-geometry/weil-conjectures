## Worker report

Module: `Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex`.
Main declaration: `AlgebraicGeometry.Scheme.Modules.subcanonicalSplittingIndex`.
All eight declarations belong to this definition node and are listed in `lean.declarations`.
There are no theorems, postponed proofs, sorries, new nodes, dependency repairs, or statement changes.

Source read: Franciosi--Tenni, *On Clifford's theorem for singular curves*, author-hosted
primary PDF https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf, Definitions 2.3, 2.9,
2.16 and Proposition 2.17(i), pp.229, 231, 233--234. The inherited reviewed statement's
maximum-admissible-partition formulation and its explicit empty-cluster convention are
retained. In particular, I have not replaced the maximum by the literal word "minimal"
in Definition 2.16, whose intended finest decomposition was already audited at stage 1.

Clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  The curve is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. These universes match the
  published dependency interface and allow arbitrary field and scheme universe `u`.
- Nonempty and connected are `[ConnectedSpace X]`, which includes `Nonempty X`.
  Projectivity is the recorded `[IsHProjective (X ↘ Spec (.of k))]`, and reducedness
  is `[IsReduced X]`. No extra smoothness or integrality is assumed.
- Pure dimension one is `SubcanonicalClusterData.pure_dimension : X.IsPureDimension 1`.
- The node condition is `SubcanonicalClusterData.nodal`: every closed point outside
  the structure map's `smoothLocus` has completed local ring isomorphic to the
  two-variable power-series quotient by `(uv)`. The displayed scalar equation on `e`
  makes this an isomorphism of k-algebras, not just abstract rings: the left scalar
  map is the canonical k-to-global-sections map, its germ, and `AdicCompletion.of`;
  the right map is `algebraMap k` into the quotient. No arbitrary algebra structure
  or extra equality of universes is used.
- A closed subscheme is `{T : Scheme.{u}} {i : T ⟶ X} [IsClosedImmersion i]`.
  Its dimension is `D.zero_dimensional : topologicalKrullDim T ≤ 0`; the empty space
  has dimension bottom, so this includes exactly the empty or zero-dimensional cases.
- The dualizing invertible module is the specified `D.dualizing` with `D.invertible`.
  `D.duality` and `D.duality_natural` express precisely its natural representing
  property for the linear dual of H1 on coherent modules, using the dependency's
  `scalarCohomology` and `scalarCohomologyMap`. This records the meaning of "dualizing"
  and does not assume that an arbitrary invertible module is dualizing. Existence
  and representing-pair uniqueness are the recorded nodal Serre-duality dependency.
- Cohomology throughout this representing property is the recorded Zariski O-module
  cohomology with scalars restricted to k. The notation h^i is explanatory in the node;
  no numerical h^i occurs in this definition. In degree zero we use actual global
  sections `Γ(F, ⊤)`, the canonical H0 model. The right-derived global-sections functor
  in `RingedSpace.moduleCohomology` has this H0, since global sections is left exact.
- `subcanonicalModule i ω` is literally `i.ker.toModules ⊗ ω`, using the recorded
  kernel ideal and sheaf tensor. `subcanonicalModuleInclusion` is the canonical
  tensor of the ideal inclusion followed by the left unitor, not an arbitrary map.
  For the invertible ω this is injective: locally the tensor is tensoring with a
  free rank-one module. Thus its global sections are exactly V, canonically regarded
  as a subspace of H0(ω) as in the node. We use this carrier rather than a duplicate
  image subtype; its identification with that subspace is by this specified inclusion.
- `IsSubcanonicalCluster i ω` says there exists ONE global section whose germ is
  nonzero at EVERY component generic point. There is no exchange of these quantifiers.
  `D.subcanonical` requires this for nonempty T, and allows empty T independently,
  because the source separately defines the zero cluster's index to be zero.
- A block A is a set of members of `irreducibleComponents X`, and thereby denotes
  its reduced union; no arbitrary subcurve or ambient set partition is substituted.
  `subcanonicalSupportedSections F A` is the intersection of the kernels of the
  actual germ homomorphisms at `genericPoints.ofComponent C` for all `C ∉ A`.
  This is precisely V_A on the V carrier. Vanishing of the F-germ is equivalent to
  vanishing of its ω-germ through the canonical injective inclusion above.
- `Finpartition (Set.univ : Set (irreducibleComponents X))` gives finite, nonempty,
  disjoint blocks covering all components. Mathlib's `Finpartition` excludes bottom
  blocks and requires supremum independence and supremum equal to the whole set.
- `subcanonicalPartitionSum` is the actual finite direct-sum summation homomorphism:
  `DirectSum.toAddMonoid` applied to the supported-subgroup inclusions.
  `IsSubcanonicalAdmissiblePartition` requires its bijectivity. Although presented
  on underlying additive groups, this is exactly the vector-space isomorphism in
  the node: each germ kernel is closed under the base-field action, the inclusions
  and the sum respect that action, and a bijective linear map has linear inverse.
  No choice of a decomposition or arbitrary isomorphism replaces the canonical sum.
- For nonempty T, `sSup {n | ∃ P, admissible P ∧ n = P.parts.card - 1}` is the largest
  such integer. The set is nonempty (the indiscrete partition, with one block), and
  bounded because a projective curve over a field is Noetherian and has finitely
  many irreducible components; a partition has at most that many nonempty blocks.
  Thus Nat's conditional supremum equals the maximum, and no unbounded-case default
  is used under the hypotheses. A natural number gives the required r(T) ≥ 0.
- For empty T, `if IsEmpty T then 0 else ...` applies before inspecting the section
  space or its partitions, exactly implementing r(empty)=0 by convention.

Dependency declarations and interfaces read and reused:

- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (finite projective-space embedding).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` (publicly re-exported by the nodal module).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`; and the published
  bridge `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, `toModulesι` (canonical kernel and inclusion).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and `Scheme.Hom.smoothLocus`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`, `RingedSpace.moduleCohomology`; the public
  nodal dependency also supplies the field-linear cohomology operations used here.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the algebraic-closure node's
  mathlib_match explicitly identifies this class for its algebraically-closed clause.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including its nonempty field.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`; `Mathlib.Topology.Sober`:
  `genericPoints.ofComponent` and its specification.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion` and its
  canonical `of` map; `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch`:
  `AlgebraicGeometry.exists_nodal_line_serre_riemann_roch` (its full signature and
  proof docstring were read; it gives exactly the dualizing representing pair used).

All node statement prerequisites were read, including their mathlib_match records
where there is no lean record. The recorded tensor/cohomology/pure-dimension/field
interfaces are reached by public imports of the nodal dependency; they are not copied.
The eight helper declarations assemble this node's own notion, not independent prerequisites.

Edge cases checked before finalization: empty cluster on any allowed curve (including
P1, where H0(ω)=0); one irreducible component (only one nonempty block, index zero);
smooth curves (the nodal condition is vacuous at singular points); arbitrary characteristic;
nonreduced zero-dimensional clusters at nodes; and reducible curves with split canonical
section spaces (the empty-cluster answer remains zero). The empty curve is excluded by
ConnectedSpace exactly as in the node. The scalar compatibility in the node condition
prevents losing the specified k-algebra structure. No additional point enumeration,
Fintype instance, separability, Cartier-cluster, or smooth-cluster restriction is required.

Searches for existing notions (msearch.py, group Q137, this item):

- LeanFinder, "splitting index subcanonical cluster on a nodal curve finest partition
  of irreducible components splitting sections": eight unrelated hits, no match.
- LeanFinder, "subcanonical cluster splitting index sections supported on irreducible
  components": eight hits about open-cover indices, shrinking and Profinite sets,
  no curve-cluster definition.
- LeanSearch, the same latter query: eight hits, including `irreducibleComponents`
  and `genericPoints`, plus unrelated Finsupp and simplicial splitting results.
- Loogle, `Finpartition, DirectSum.coeLinearMap`: zero hits, no exact notion.
- msearch grep, `subcanonical|splittingIndex|splitting_index`, AlgebraicGeometry:
  fifteen hits, all about subcanonical site topologies or unrelated gluing.
- rg in live `lean/WeilConjectures` and `lean/Sheaf`,
  `subcanonical|Subcanonical|splittingIndex|SplittingIndex|splitting_index`:
  the subcanonical hits refer to topologies, with no subcanonical-cluster splitting index.
  A second exact-name search for the new declarations found no collision.
- grep for `def-sfb-subcanonical-splitting-index` in `lean/WeilConjectures`: no match.
  DAG search found this node and its dependent curve lemmas, not an existing Lean notion.

Validation: required scompile.py compiled both the sandbox name and the final library
module without errors or warnings (6.8 s and 9.0 s in the clean run). All variables and
universes are explicit, autoImplicit is false, and all Lean lines are at most 100 characters.

## Second reading by Q137

This is a separate self-review pass; the dispatcher explicitly forbids starting other
agents, so no independent-worker review is claimed. I reopened the node, all eight
signatures, and every definition body. I matched the hypotheses and clauses above.
The first draft's global `open scoped Classical` produced a style warning; it was
replaced by `open Classical in` solely around the index definition. I also made
coefficient compatibility explicit for the completed-local k-algebra isomorphism.
The empty-cluster review caught that requiring a generically nonzero section even
for empty T would wrongly exclude genus-zero curves. The final `IsEmpty T ∨ ...`
field fixes that while still requiring subcanonicality for every nonempty cluster.
The generic-germ kernels use the twist itself, identified with the specified subspace
of canonical sections by the canonical tensor inclusion; the direct sum uses those
same kernels. The final supremum counts blocks, not points or components separately.
No remaining mismatch, node correction, or STATEMENT-DISPUTED flag was found.
