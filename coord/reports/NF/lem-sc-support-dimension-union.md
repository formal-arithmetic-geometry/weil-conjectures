## Worker report

The module `Sheaf.AlgebraicGeometry.SupportDimensionUnion` states
`AlgebraicGeometry.support_dimension_union`, with exactly one sorry and no new definition.
The source blueprint node and its seven-step DAG proof were read. The node is unchanged
except for its `lean` record. There is no statement dispute or correction.

Hypothesis and clause correspondence:

- A field K is `{K : Type u} [Field K]`.
- A finite-type K-scheme B is `{B : Scheme.{u}}`, the structure morphism
  `p : B ⟶ Spec (.of K)`, `[LocallyOfFiniteType p]`, and `[QuasiCompact p]`.
  This explicit morphism fixes the algebra used in the residue-field expression;
  it is the recorded `Hom.residueFieldAlgebraMap` convention, without separatedness.
- An abelian étale sheaf N is `Sheaf B.smallEtaleTopology AddCommGrpCat.{u+1}`.
  Its torsion hypothesis is `hN : CategoryTheory.Sheaf.IsTorsion N`, the existing
  local-section definition, not the stronger assertion that all section groups are torsion.
- The nonnegative integer a is `(a : ℕ)`, including zero.
- `hvanish` quantifies over every algebraically closed field Ω and every geometric
  point `s : Spec Ω ⟶ B`. The image point is `s default`. It compares `(a : Cardinal)`
  with `@Algebra.trdeg K ... (p.residueFieldAlgebraMap (s default)).toAlgebra`, using
  the algebra induced by p, and asserts `IsZero` of the existing geometric stalk.
- The index category of D is literally the subtype of `TopologicalSpace.Closeds B`
  satisfying `topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞)`.
  Its inherited partial order is inclusion. All and only the specified closed
  subsets occur. No assumed filteredness or arbitrary index parametrization is added.
- The open complement inclusion j_Z is
  `Scheme.Opens.ι ⟨(Z.val : Set B)ᶜ, Z.val.isClosed.isOpen_compl⟩`.
- The displayed map `N → j_* j^* N` is the component of
  `Etale.upperStarLowerStarAdjunction ... j_Z |>.unit`. The parameters `c`, `hz`, and
  `hk` specify that `D.obj Z`, with inclusion `c.app Z`, is its kernel: `hz` supplies
  the zero composite and `hk` is `IsLimit (KernelFork.ofι ... (hz Z))`.
  This is the standard universal-property encoding of the instruction “set N_Z = ker”.
  These parameters choose models of existing categorical kernels; they add no
  mathematical restriction. Such kernels exist since the sheaf category is abelian.
  The transition maps are forced: naturality of c and monicity of each kernel inclusion
  uniquely identify them with the canonical inclusions. No arbitrary sheaf map can pass hk.
- The canonical map is `(colimit.isColimit D).desc (Cocone.mk N c)` and the conclusion
  is `IsIso` of that exact morphism. The use of arbitrary compatible kernel models
  is invariant under their unique compatible isomorphisms, so gives the same assertion
  as choosing Mathlib's kernels explicitly.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded sheaf category and
  torsion material; `CategoryTheory.Sheaf.IsTorsion` is defined in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`, with
  `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` (subspace dimension).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.ZetaSeries`: `Scheme.Hom.residueFieldAlgebraMap`.
- Scheme conventions fix no independent declaration; finite type is the two
  Mathlib morphism classes already recorded there.
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels`: `KernelFork.ofι` and `IsLimit`;
  the colimit comparison uses Mathlib's `colimit.isColimit` and `Cocone.mk`.

All recorded proof-dependency modules are imported. Mathlib leaves for finite components,
Noetherianity, sobriety and stalk exactness are also imported as the proof plan.
`lem-sc-etale-section-zero-open` has no Lean module yet, so cannot be imported.
No dependency module or additional definition node was necessary.

Edge cases checked: a = 0; N = 0; empty B; the empty closed subset (dimension bottom,
therefore included for every a); Z = B when its dimension meets the bound; arbitrary
characteristic; nonseparated B. Empty B does not remove the index object Z = empty.
The residue-field and geometric-point universes match Scheme.{u}; the sheaf values use
u+1, as the recorded abelian étale category. There are no automatic implicit binders,
file-local instances, private definitions, auxiliary definitions, or let binders.

Searches made before finalizing the statement:

- msearch leanfinder: “An etale sheaf vanishing at points above transcendence degree a
  is a filtered union of kernels supported on closed subsets of dimension at most a”.
  Eight results, all about algebraic étale loci, including
  `Algebra.etaleLocus_eq_compl_support`; none is the required sheaf assertion.
- msearch loogle: `topologicalKrullDim, CategoryTheory.Limits.KernelFork,
  CategoryTheory.Limits.IsColimit`: zero results.
- msearch grep: `support.*dimension|dimension.*support`: 17 unrelated results,
  including Krull dimension of module support and analytic compact supports.
- rg of the upstream source and project Lean for `support_dimension_union`,
  `support.*dimension`, and `dimension.*support`: no matching theorem. Nearby
  `SupportDimensionCohomologyVanishing` concerns cohomology, not this filtered union.
- rg of the upstream source for `lem-sc-support-dimension-union`: no occurrences.
- DAG search found the assigned node and its citers, not another recorded declaration
  of this statement. Generic kernel, cocone and colimit notions are reused directly.

Server validation: scompile.py compiled the final file cleanly, with nice 19,
two threads and the default 60-second per-file limit. The final compile took about
1.8 seconds. No local compiler or global build was used. The theorem remains sorry
as required by stage 2. The dry-run delivery result is recorded below when complete.

## Second reading by NF

I read the source node, its Stacks/blueprint source place, every statement
dependency record, and the Lean declaration independently. The correspondence is:

- The field is `K : Type u` with `[Field K]`; the finite-type scheme is
  `B : Scheme.{u}` with its named structure morphism `p : B ⟶ Spec (.of K)` and
  `[LocallyOfFiniteType p] [QuasiCompact p]`.
- The torsion étale sheaf is
  `N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}` with
  `hN : CategoryTheory.Sheaf.IsTorsion N`.
- The bound is `a : ℕ`, so `a ≥ 0` includes zero.
- `hvanish` quantifies over algebraically closed fields `Ω : Type u` and geometric
  points `s : Spec (.of Ω) ⟶ B`; its strict cardinal inequality is exactly
  `trdeg_K κ(s default) > a`, and its conclusion is `IsZero` of the recorded
  geometric stalk `pointSmallEtale s |>.sheafFiber.obj N`.
- The index is exactly the subtype of `TopologicalSpace.Closeds B` satisfying
  `topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞)`, with no extra directedness
  or finiteness hypothesis.
- For each index object, the open complement is rendered by
  `Scheme.Opens.ι ⟨(Z.val : Set B)ᶜ, Z.val.isClosed.isOpen_compl⟩`; the natural
  transformation `c` and equations `hz`/`hk` identify `D.obj Z` and `c.app Z`
  with the kernel of `N → j_{Z*}j_Z^*N`.
- The conclusion is precisely `IsIso` of
  `(colimit.isColimit D).desc (Cocone.mk N c)`, the canonical colimit map.

The source assumptions and all conclusion clauses are present, in the same order,
with no stronger assumptions or extra conclusion. Universes agree (`Scheme.{u}`,
geometric fields `Type u`, and sheaf values `u+1`). Edge cases checked were
`a = 0`, the zero sheaf, empty `B`, the empty closed subset, `Z = B` when allowed,
arbitrary characteristic, and nonseparated schemes; none is excluded by the Lean
binders. The empty closed subset supplies an index object even for empty `B`.

I repeated the existing-definition searches with LeanFinder/Loogle, grep over
Mathlib, `WeilConjectures/`, and this project's `lean/Sheaf`; all hits were generic
étale-locus, support, stalk, kernel, or colimit results and no declaration states
this theorem. The dependency declarations were opened and match their nodes:
`Algebra.trdeg`, `topologicalKrullDim`, `Scheme.pointSmallEtale`/
`Point.sheafFiber`, `Etale.upperStarLowerStarAdjunction`, and
`CategoryTheory.Sheaf.IsTorsion`.

No mismatch was found, so no repair was needed. The module compiled through
`scompile.py` with only the expected `sorry` warning; no local compiler or global
build was used.
