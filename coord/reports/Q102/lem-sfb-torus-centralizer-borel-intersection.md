## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusCentralizerBorelIntersection`
states `AlgebraicGeometry.exists_torusCentralizer_borel_intersection`, with `sorry`
as its sole proof. It introduces no definition or helper axiom. Source: Milne,
Algebraic Groups (2017), Theorem 17.46 and its proof, printed pp.365–366,
including footnote 2, and the restatement 17.72, printed p.376. I read those
passages in the local PDF using pdftotext. The node's eleven-step accepted
stage-1 proof is retained and rendered in the declaration docstring.

The inherited BLOCKED ending concerned an unchanged stage-1 delivery, not this
stage-2 task. The current queue places this node in stage 2; the node has a
reviewed split, no Lean record and no released repair note. No stage-1 proof,
source, statement, review or metadata has been changed.

Clause correspondence:

- An algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe `u` is explicitly declared and `autoImplicit` is disabled.
- Group schemes G, B and S are `Grp (Over (Spec (.of F)))`, with their actual
  internal group laws and group homomorphisms. This bundles the recorded
  `CategoryTheory.GrpObj` convention without changing the group-scheme notion.
- G is affine and finite type by `[IsAffine G.X.left]`,
  `[LocallyOfFiniteType G.X.hom]` and `[QuasiCompact G.X.hom]`.
- Smoothness and connectedness of G are `[Smooth G.X.hom]` and
  `[ConnectedSpace G.X.left]`. In particular the empty scheme is excluded by
  the source's connectedness convention, not by an additional assumption.
- The Borel inclusion B ⊆ G is `(iB : B ⟶ G)` together with
  `hB : IsBorelGroupScheme iB.hom.hom`. Its definition includes the closed
  subgroup condition, smoothness, connectedness, scheme-theoretic derived-series
  solvability and maximality among all such closed subgroup schemes. This is
  not abstract solvability of F-points. Affineness and finite type of B follow
  from its closed immersion into G, so no further assumptions on B are needed.
- The closed torus inclusion S ⊆ B is `(iS : S ⟶ B)` with
  `hS : IsClosedSubgroupScheme iS.hom.hom`, and
  `hT : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)`.
  The latter is exactly the node's split-torus definition over F and allows
  r = 0. It does not use maximality of S. The existing `splitTorus` recursively
  multiplies the recorded multiplicative group, with the trivial empty product.
  The closed inclusion gives affineness and finite type of S as well.
- The subgroup S ⊆ G used in the centralizer is the actual composite `iS ≫ iB`.
- Representability by a smooth connected closed subgroup C ⊆ G is the
  existential `(C : Grp (Over (Spec (.of F)))) (iC : C ⟶ G)` and the conjunction
  `IsClosedSubgroupScheme iC.hom.hom ∧ Smooth C.X.hom ∧ ConnectedSpace C.X.left`.
  Affineness and finite type of C follow from closedness in G.
- The centralizer's defining equality for every commutative F-algebra is
  `∀ (A : Type u) [CommRing A] [Algebra F A],
  ReductiveTorusCentralizer.centralizerPoints (iS ≫ iB) A =
  Set.range (fun c : StandardGroupSchemes.affine F A ⟶ C.X ↦ c ≫ iC.hom.hom)`.
  I read the reused predicate: it quantifies over every commutative F-algebra
  A', every F-algebra map A → A', and every point of S over A', requiring
  `Commute` for the extended point and the image of the S-point. Giving an
  A-algebra structure on A' compatible with F is equivalently giving this
  F-algebra map. Neither algebra is assumed reduced, a field, or finite type.
  Closedness makes the point map injective; equality of ranges therefore
  identifies the represented subfunctor, including its restriction maps, rather
  than only asserting an abstract bijection of sets or testing F-points.
- The scheme intersection B ×_G C is represented by the existential group
  scheme H and group homomorphisms `jB : H ⟶ B`, `jC : H ⟶ C` with
  `IsPullback jB.hom.hom.left jC.hom.hom.left iB.hom.hom.left iC.hom.hom.left`.
  This is Mathlib's full pullback property in Scheme, including commutativity
  and the limit property. It identifies H with the actual scheme-theoretic
  fibre product; it is not an intersection of sets of rational points. Its
  maps to G are already over F, so this also fixes the F-scheme structure.
- Being a Borel subgroup of C is `IsBorelGroupScheme jC.hom.hom`, which includes
  the closed subgroup inclusion, smoothness, connectedness, solvability and
  the full maximality assertion in C. The pullback and its Borel property imply
  that H is affine and finite type. Thus the standing convention that every
  group here is affine of finite type is respected for every quantified group.

Statement dependency declarations read and used:

1. `Field` in Mathlib.Algebra.Field.Defs (lines 169–180) and `IsAlgClosed` in
   Mathlib.FieldTheory.IsAlgClosed.Basic (lines 53–64).
2. `CategoryTheory.GrpObj` / bundled `CategoryTheory.Grp` in
   Mathlib.CategoryTheory.Monoidal.Grp; group laws are internal to
   `Over (Spec (.of F))` as documented in the existing group-scheme module.
3. `AlgebraicGeometry.IsClosedSubgroupScheme` and `IsSubgroupScheme` in
   WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (lines 70–103), imported
   through the existing Borel definition. The former includes the recorded
   pointwise injectivity, homomorphism and actual closed immersion.
4. `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, read in
   Mathlib.AlgebraicGeometry.Morphisms.FiniteType (lines 29–50) and
   Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact (lines 32–47).
5. `AlgebraicGeometry.Smooth`, read in
   Mathlib.AlgebraicGeometry.Morphisms.Smooth (lines 48–66), and
   `ConnectedSpace`, Mathlib.Topology.Connected.Basic (lines 697–710).
6. `StandardGroupSchemes.affine`, `map`, `multiplicative` and its group law in
   Sheaf.AlgebraicGeometry.StandardGroupSchemes (lines 45–93).
7. `IsBorelGroupScheme` in Sheaf.AlgebraicGeometry.GroupScheme.Borel, including
   `IsSolvableGroupScheme` and `GroupSchemeDerivedLength` in its Semisimple
   dependency. I read both full definitions. The Borel node already cites the
   scheme-theoretic solvability node, so no duplicate notion is introduced.
8. `MultiplicativeType.splitTorus` in
   Sheaf.AlgebraicGeometry.ToriMultiplicativeType (lines 35–39).
9. `ReductiveTorusCentralizer.centralizerPoints` in
   Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology (lines 50–59).
10. `CategoryTheory.IsPullback` in
    Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs (lines 48–65),
    giving the fibre product specified by def-pc-fibre-product.

The item's `stmt_deps` gains four already-landed nodes that carry exactly the
notions reused here: `def-sfb-borel-subgroup-scheme`,
`def-sfb-tori-multiplicative-type`,
`def-sfb-reductive-torus-centralizer-terminology`, and `def-pc-fibre-product`.
This is the existing-landed-nodes allowance in brief-stage2 §5. The original
eight dependencies remain. Other than these additions and `lean`, the node
copy is unchanged. No new node, dependency interface repair or source-based
statement correction is needed.

The module publicly imports the Borel and centralizer terminology modules,
which transitively publicly expose the original dependency definitions and the
split-torus construction, and Mathlib's pullback predicate. Already stated
proof dependencies are plain imports: algebraic-closure connectedness,
perfect-solvable structure, largest-subtorus, finite-type/Noetherian/fp/qcqs,
flat-lfp openness, scheme reduction, geometric connectedness, closed-point
residue fields, proper closed immersions, separated group schemes and the
reduced-source closed-factorization theorem. Proof nodes without a declaration
have no import yet; the eleven-step docstring names all of them explicitly.
In particular the unused general flag-variety route is not imported.

Edge cases checked against the source and definitions:

- Rank zero S = 1: centralizer is G and the pullback is B, so the assertion
  specializes to the given Borel property without excluding the trivial torus.
- Central S: centralizer is again G; B ×_G G is B.
- G = B smooth connected solvable: the intersection is the entire centralizer,
  consistent with solvability inherited from B.
- G a torus, including the trivial group: B = G and all centralizers are G.
- GL₂, upper-triangular B and full diagonal S: C is the diagonal torus and the
  intersection is C. Scalar S instead gives C = GL₂ and intersection B.
- Positive characteristic and nonreduced test algebras remain included. The
  all-extension condition is not replaced by commutation only over F, so no
  infinitesimal structure of an intersection or centralizer has been erased.

Searches actually run with the prescribed msearch.py wrapper for Q102/item:

- LeanFinder: "Intersecting a Borel subgroup with the centralizer of a subtorus
  is a Borel subgroup in a smooth connected affine algebraic group". Eight
  hits: topological closed centralizers, abstract subgroup centralizers, Cartan
  Lie-algebra results and an absolute Galois group. None states this result.
- Loogle: `"centralizer", "Borel"`. Zero hits.
- Mathlib grep: `BorelSubgroup|IsBorel|borel.*centralizer|centralizer.*borel`.
  Zero hits.
- LeanSearch: "A Borel subgroup intersected with the centralizer of a torus is
  a Borel subgroup of the centralizer". Eight abstract centralizer results;
  no algebraic group-scheme theorem or one-line specialization.
- Direct rg in lean/WeilConjectures/AlgebraicGeometry and
  lean/WeilConjectures/AlgebraicGeometry/GroupScheme for Borel, IsTorus,
  IsSolvable and centralizer found matrix-equation centralizers only.
- Direct rg for the item's exact blueprint id in lean/WeilConjectures had no
  hit. Direct rg in lean/Sheaf/AlgebraicGeometry found the Borel, split-torus,
  solvability and centralizer predicate modules used above, and related
  theorem statements, but no theorem asserting this intersection result.
- Checked dag/lean_names_upstream.json and lean/Sheaf for the expected theorem
  name and torus-centralizer-Borel combinations: no matching declaration.
  Read the current blueprint marker (latest main-20261024) and searched latest
  for the auxiliary source terminology; this auxiliary is sourced directly
  from the Milne PDF, as the DAG records.

There is no STATEMENT-DISPUTED finding. The accepted statement matches the
source. In particular Theorem 17.46 has an additional converse classifying
all Borels of the centralizer; that is not a clause of this node and is not
silently added to the Lean statement.

Validation: the prescribed `scompile.py Q102
lem-sfb-torus-centralizer-borel-intersection <module>` compiled both sandbox
and library forms cleanly (1.7 s and 1.5 s). No error or unexpected warning.

## Second reading by Q102

I made a separate reading pass with the node and final Lean signature open;
no other agent was started, as the dispatcher's brief requires. The node's
base field and characteristic generality match the binders. Its affine,
finite-type, smooth connected ambient group is exactly the five instances on
G. Borel smoothness, connectedness, scheme-derived solvability, closedness and
maximality are all supplied by the reused `IsBorelGroupScheme` definition.
The S-in-B hypothesis is a closed group inclusion plus an isomorphism to the
existing split torus of arbitrary natural rank, not a maximal-torus assumption.
All other affineness and finite-type conditions follow from the closed subgroup
embeddings, so no case is lost by leaving those redundant instances implicit.

I expanded `centralizerPoints` while reading the range equality: its further
algebra B and map A →ₐ[F] B encode exactly the commutation condition in the
node, including nonreduced extensions. The map whose range appears is the
actual closed inclusion of C; thus naturality and injectivity accompany the
pointwise image equality. I also checked the order of Mathlib's `IsPullback`
arguments against its source diagram: top H → B, left H → C, right B → G,
bottom C → G, in Scheme. Hence this is precisely B ×_G C, and the last
`IsBorelGroupScheme` is applied to H → C, not to H → G or H → B.

The edge cases S = 1 and scalar S in GL₂ would both detect accidental maximality
or self-centralizer hypotheses; neither is present. The full diagonal case
checks the orientation of the concluding Borel inclusion. I checked that all
original node fields outside the four added statement dependencies and `lean`
are preserved, including O2's reviewed eleven-step split. No mismatch requiring
a changed statement or dependency module was found. The only additions from
this reading are the explicit explanation that closed subgroups inherit affine
finite type and that representability is of the subfunctor, not merely a
set-level bijection.
