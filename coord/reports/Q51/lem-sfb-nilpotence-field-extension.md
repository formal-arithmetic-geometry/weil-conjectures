## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/GroupScheme/NilpotenceFieldExtension.lean`
as `AlgebraicGeometry.isNilpotentGroupScheme_iff_fieldExtension`. Its only proof is `sorry`.
The original statement, proof plan and proof dependencies are unchanged. Its statement
dependencies gain `def-sfb-nilpotent-group-scheme`, whose module supplies a real Prop-valued
definition, `AlgebraicGeometry.IsNilpotentGroupScheme`.

Clause-by-clause reading of the item:

- A field k: `(k : Type u) [Field k]`.
- An arbitrary field extension K/k: `(K : Type u) [Field K] [Algebra k K]`.
  The homomorphism is `algebraMap k K`. There is no assumption of perfectness,
  algebraicity, separability or finite dimension.
- A k-group scheme G: `G : Grp (Over (Spec (.of k)))`. Bundling records the same
  `CategoryTheory.GrpObj` structure specified by `def-sc-group-scheme`.
- Affine: `haff : IsAffine G.X.left`.
- Finite type: `hft : LocallyOfFiniteType G.X.hom` and `hqc : QuasiCompact G.X.hom`,
  exactly the two conditions in the dependency's recorded definition.
- Smooth: `hsm : Smooth G.X.hom`.
- Connected: `hconn : ConnectedSpace G.X.left`; this includes nonemptiness.
- Scalar extension G_K: `(Over.pullback (Spec.map (CommRingCat.ofHom
  (algebraMap k K)))).mapGrp.obj G`. The underlying object is the fibre product
  with Spec K, equipped with the canonical transported group structure. It is
  the group-object version of the recorded `Over.pullback` convention, not a
  separately supplied or arbitrary structure.
- Nilpotent over k if and only if nilpotent over K: the conclusion is the `↔`
  between `IsNilpotentGroupScheme G` and that predicate on this scalar extension.

Clause-by-clause reading of nilpotence (the definition node):

- There exists s >= 0: `∃ s : ℕ`. The terms are `H : Fin (s + 1) → Grp (...)`.
- Closed normal subgroup schemes of G: embeddings `i : ∀ j, H j ⟶ G`, with
  `IsClosedSubgroupScheme (i j).hom.hom` and
  `IsNormalSubgroupScheme (i j).hom.hom` for every j. These are the existing
  declarations, including injectivity of all algebra-valued point maps.
- H_0 = G as an embedded subgroup: `IsIso (i 0)`. This permits the usual
  isomorphic representatives of the same subgroup, without changing its image.
- H_s = 1: `Nonempty (H (Fin.last s) ≅ Grp.trivial _)`; a homomorphism from the
  trivial group necessarily has identity image, so this is equality as a subgroup.
- H_(j+1) is contained in H_j: `∃ l : H j.succ ⟶ H j.castSucc,
  l ≫ i j.castSucc = i j.succ` for each `j : Fin s`. A factorization suffices:
  since the ambient embeddings are monomorphisms this is the inclusion of the
  represented closed subgroups.
- Every commutative algebra A: `(A : Type u) [CommRing A] [Algebra k A]`.
- Points g in G(A), h in H_j(A): morphisms from
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))` into G.X and
  `(H j.castSucc).X`, respectively.
- Their commutator belongs to H_(j+1)(A): existence of z in the next term with
  `z ≫ (i j.succ).hom.hom = g * (h ≫ (i j.castSucc).hom.hom) * g⁻¹ *
  (h ≫ (i j.castSucc).hom.hom)⁻¹`. Thus the order is precisely ghg⁻¹h⁻¹.

Dependency declarations read and reused:

- `Field` in `Mathlib.Algebra.Field.Defs` and `Algebra` in
  `Mathlib.Algebra.Algebra.Defs` for the fields and their extension.
- `AlgebraicGeometry.Scheme` and `Spec` in `Mathlib.AlgebraicGeometry.Scheme`.
- `CategoryTheory.GrpObj`, `Grp` and its homomorphisms in
  `Mathlib.CategoryTheory.Monoidal.Grp`.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme` and
  `IsNormalSubgroupScheme`, with their complete algebra-point signatures and
  docstrings, in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `AlgebraicGeometry.Smooth` in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `ConnectedSpace` in `Mathlib.Topology.Connected.Basic`.
- `Over.pullback` as documented by the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; `Functor.mapGrp`
  and `Functor.grpObjObj` in `Mathlib.CategoryTheory.Monoidal.Grp`, together
  with the product-preserving pullback framework in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.

The module also imports the already stated Mathlib proof inputs for affine
pullbacks, finite-type base change, proper/closed-immersion permanence, and
faithful-flat tensor injectivity. The proof-only DAG nodes
`lem-sfb-smooth-connected-relative-commutator` and
`lem-sfb-pointed-generated-subgroup-field-extension` currently have no Lean
record, so there is no module of either to import. Both are named in the
proof docstring, which reproduces the complete five-step plan. No proof-only
prerequisite is needed to type this stage-2 statement.

Edge cases checked before writing:

- s = 0: `Fin (s + 1)` still has one term, `Fin s` is empty, and the endpoints
  force G to be the trivial group. No nonexistent successor is accessed.
- The trivial group is admitted; no nontriviality or positive dimension is assumed.
- Empty G is excluded by connectedness and by its identity section, as in the node.
- Nonreduced test algebras and nonsmooth or disconnected series terms are included.
  No regularity condition is imposed on H_j.
- K = k, positive characteristic, imperfect fields, purely inseparable and
  transcendental extensions are all covered by the same statement.
- The universe u binds schemes, both fields and test algebras together, as in the
  recorded subgroup interface. It may be any common ambient universe and is not
  an independently smaller test universe. Coordinate rings of the affine test
  schemes and the universal points used in the proof are in that universe.

Searches for existing declarations:

- `msearch.py ... leanfinder "Nilpotence of a smooth connected affine group scheme
  is invariant under arbitrary field extension"`: 8 hits, mostly geometric
  reducedness and nilpotent elements in tensor rings; no matching theorem.
- `msearch.py ... leansearch "A group scheme is nilpotent if it has a finite
  descending central series of closed normal subgroup schemes"`: 8 hits,
  including `Group.IsNilpotent`, `nilpotent_iff_lowerCentralSeries` and abstract
  finite-series equivalences. None supply closed subgroup schemes.
- `msearch.py ... loogle '"IsNilpotent", "lowerCentralSeries"'`: 5 hits on Lie
  modules and abstract subgroups. No matching predicate or invariance theorem.
- `msearch.py ... grep 'nilpoten|centralSeries' AlgebraicGeometry`: 13 hits on
  nilpotent ring sections; no group-scheme definition.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for scheme nilpotence and
  central-series names found only theorem-signature existentials in
  `NilpotentConnectedCentralSeries.lean` and `GroupScheme/CentralMaximalTorusNilpotent.lean`.
  Their full signatures were read: neither defines a nilpotence predicate or
  states the field-extension equivalence. The former also assumes perfectness.
- Search for the item id in `lean/WeilConjectures` gave no declaration.
- Definition-node search of `dag/nodes` found no group-scheme nilpotence definition.
  `tools/blueprint_refs.py search nilpotent` returned 12 unrelated blueprint
  nodes concerning nilpotent ideals, affine varieties and Engel's theorem.

Source check: read the local Milne PDF at Definition 6.24, Remark 6.25,
Definition 6.34, Remark 6.35, Proposition 6.38 and Proposition 2.47. Definition
6.34 is a central normal series and Remark 6.35 is its commutator condition.
Proposition 6.38 and scalar-extension compatibility in 2.47 underlie the
item's supplied synthesis. No statement correction or dispute was necessary.

## New nodes

`def-sfb-nilpotent-group-scheme` defines exactly the finite closed-normal-series
notion spelled out in the item, following Milne Definition 6.34 and Remark 6.35,
p.133. It imports and uses the existing subgroup predicates. The three required
search kinds and the project/DAG searches above found no reusable definition.
Existing theorems inline related series but cannot be used as a predicate.
The node has its own definition module, real data with no sorry, the item's
chapter and unit, and the inherited blueprint ancestor/via chain. The item
cites it in stmt_deps.

## Validation

Both delivered Lean files compiled cleanly through scompile.py in dependency
order (exit code 0), with no errors or unexpected warnings. All Lean lines are at
most 100 characters. The node signatures were extracted verbatim from the files.
The prescribed deliver2.py dry run and final delivery also compile the two files
and run the server preflight.

## Second reading by Q51

No second reading by another worker: the dispatcher brief prohibits starting
other agents and directs this worker to deliver. The maintainer performs the
independent review. A final self-check re-opened both signatures and matched
all hypotheses and the series endpoints, normality, inclusions, and commutator
condition to the node; no mismatch was found.
