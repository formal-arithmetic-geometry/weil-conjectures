## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy`
states `AlgebraicGeometry.borel_contains_maximal_torus_and_conjugacy` with a
single `sorry` proof. It introduces no definitions. The node's mathematical
statement and proof plan are unchanged. Its statement dependencies gain the four
already landed definition nodes for the torus, derived-series, Borel and maximal-torus
predicates, so those existing notions are explicitly recorded and reused.

Clause-by-clause correspondence:

- The field F and its algebraic closedness are `{F : Type u} [Field F]
  [IsAlgClosed F]`. There is no characteristic restriction.
- A group scheme is `G : Grp (Over (Spec (.of F)))`, using the recorded internal
  group object and its homomorphisms. Affineness is `[IsAffine G.X.left]`.
  Finite type is `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Smoothness is `[Smooth G.X.hom]`; connectedness is
  `[ConnectedSpace G.X.left]`, including nonemptiness.
- A Borel inclusion is `iB : B ⟶ G` with
  `IsBorelGroupScheme iB.hom.hom`. This predicate includes the closed subgroup
  condition, smoothness, connectedness, solvability and maximality among such
  subgroups. Its solvability predicate is `IsSolvableGroupScheme`, whose actual
  recursion uses the smallest closed subgroup through which the commutator
  morphism factors. It is not solvability only on rational points.
- For every such Borel, the first conjunct gives `T` and `iT : T ⟶ G` with
  `ReductiveTorusCentralizer.IsMaximalTorus iT`. This includes that iT is closed,
  T is a torus and every inclusion in a larger torus over G is an isomorphism.
  The factorization `∃ j : T ⟶ B, j ≫ iB = iT` is containment in the prescribed
  Borel, with maximality in G, rather than just maximality in B.
- The reused `MultiplicativeType.IsTorus` means a finite product of G_m after
  algebraic closure. Since F is already algebraically closed, this is equivalent
  to the node's split-torus definition over F. The recorded `splitTorus` uses
  the standard Laurent-coordinate G_m and has the trivial group for rank zero.
- For arbitrary `T₁ T₂`, the second conjunct assumes exactly maximality of their
  closed torus inclusions i₁ and i₂, then gives
  `g : 𝟙_ (Over (Spec (.of F))) ⟶ G.X`, an F-rational point.
- For every `A : Type u` with `[CommRing A] [Algebra F A]` and every A-point z,
  membership in the image of T₂ is equivalent to being
  `(toUnit (StandardGroupSchemes.affine F A) ≫ g) * (t₁ ≫ i₁.hom.hom) *
  (toUnit (StandardGroupSchemes.affine F A) ≫ g)⁻¹`
  for some A-point t₁ of T₁. Thus the direction is exactly
  g T₁ g⁻¹ = T₂. The same g works for all algebras. These are equality of
  subgroup subfunctors, hence of the closed subgroup schemes. No reducedness
  assumption or restriction to fields is made on A. Algebra universes match F
  and the schemes, following the recorded subgroup-scheme convention, so in
  particular coordinate algebras that detect scheme structure are included.
- There is no reductivity hypothesis. Affineness and finite type for B and the
  tori follow from their closed inclusions into the affine finite-type G;
  unnecessary independent assumptions on these closed subgroups are absent.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (available through the imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the dependency's
  algebraic-closure construction is `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp` and group homomorphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.affine`, `multiplicative`, `multiplicativeGroup`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.IsTorus`, `splitTorus`, `baseChange`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `groupSchemeCommutator`, `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`,
  `IsSolvableGroupScheme`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`. Its namespace does not impose
  reductivity; the full definition was read.

The three currently stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus`,
`Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry` and
`Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup`.
The remaining proof dependencies have no recorded Lean statement yet, so their
modules cannot yet be imported. All five proof steps, including their node IDs,
are preserved in the theorem docstring for stage 3.

Sources read: Milne's local PDF, printed pp.354--355 (Theorem 17.10 and the
paragraph after Definition 17.12), and pp.336--337 (Theorem 16.33(d)). These give
exactly the two conclusions. The source's Borel conjugacy is an intermediate
proof step, not an additional conclusion. The current blueprint's stability
route is unchanged.

Edge cases checked before writing: the trivial group (rank zero); G a torus
(the unique maximal torus is G); connected unipotent groups (trivial maximal
torus); nonreductive upper triangular groups (B=G, conjugate maximal tori);
positive characteristic; nonreduced test algebras and the zero algebra. Empty
G cannot satisfy the group and connectedness hypotheses. No counterexample,
ambiguity or statement correction was found.

Searches made with `msearch.py Q19 lem-sfb-borel-maximal-torus-conjugacy`:

- LeanFinder: `Every Borel subgroup contains a maximal torus and maximal tori
  of connected affine algebraic groups are conjugate`. Eight hits about Cartan
  subalgebras, root systems and connected components, none about the stated
  group-scheme theorem.
- Loogle: `"torus", "conjugate"`. Zero hits.
- Mathlib grep: `maximal.tor(us|i)|BorelSubgroup|borel.subgroup`. Zero hits.
- LeanSearch: `Maximal tori of connected affine algebraic groups are conjugate`.
  Eight hits about abstract group conjugacy, Iwasawa structures and Lie modules;
  no group-scheme theorem.
- Project rg: `IsBorel|IsMaximalTorus|IsTorus|BorelSubgroup|borelMaximal|
  borel.*[Cc]onjug|[Cc]onjug.*[Tt]or` in Sheaf and WeilConjectures. Found the
  reusable predicates above and downstream results requiring reductivity;
  none states this general two-clause theorem. In particular the general Borel
  flag-variety theorem does not state maximal-torus conjugacy and is not used.
- Upstream rg for the exact node ID and maximal-torus/Borel theorem names:
  no existing matching theorem. Search of `dag/lean_names_upstream.json` for
  the chosen declaration name also found no clash. DAG search of the existing
  definition records identified all four predicate nodes added to stmt_deps.

Validation: `scompile.py` compiled both its sandbox view and the final library
module successfully (2.5 s and 2.2 s), with no errors or warnings. The initial
compile diagnosed missing scoped point-group instances; `open scoped MonObj`
resolved this without altering the statement. The only postponed proof is the
named theorem, with its source and complete proof plan in its docstring.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
