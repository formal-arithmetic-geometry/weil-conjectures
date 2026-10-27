## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricDiagonalizableSeparablyClosedSplit`
states `AlgebraicGeometry.geometric_diagonalizable_separably_closed_split` with
one `sorry`, without introducing definitions or changing the DAG statement.

Read the node, all eight statement dependencies and their full recorded
interfaces/docstrings. Read Conrad's online PDF, Appendix B.4 opening paragraph
(printed p.297) and Lemma B.1.5 and its proof (printed p.283). The first passage
makes multiplicative type independent of arbitrary extension fields using
spreading out and specialization; the second gives finite separable splitting,
including over imperfect fields and with torsion character groups. Together
they give exactly this separably closed specialization.

Hypothesis and clause correspondence:

- `k : Type u`, `[Field k]`, `[IsSepClosed k]` render the separably closed ground field.
- `E : Type u`, `[Field E]`, `[Algebra k E]`, `[IsAlgClosed E]` render an arbitrary
  algebraically closed extension. There is no algebraicity or separability assumption.
- `H : Grp (Over (Spec (.of k)))` is the actual group object in k-schemes. Its
  multiplication, unit, inverse and group laws are bundled. Isomorphisms below
  are in this group-object category, so they preserve the group operations.
- `[IsAffineHom H.X.hom]` is affineness over k (equivalently affineness of H,
  since Spec k is affine).
- `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]` are precisely finite type
  in the recorded finite-type dependency. Quasi-compactness also follows from
  affineness; it is written here as the source's finite-type conjunction.
- `N₀ : AddCommGrpCat.{u}` and `[AddGroup.FG N₀]` give the finitely generated
  additive abelian group of the hypothesis, without torsion restrictions.
- `ringDiagonalizableGroup E N₀` is the recorded D_E(N₀), with the actual
  group-algebra Hopf operations, rather than a new copy or abstract split object.
- `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))` forms scalar
  extension: its object is `Over.mk (pullback.snd H.X.hom (Spec.map ...))`.
  The functor's `.mapGrp` preserves the group object and all its operations.
  The hypothesis `h : Nonempty (... ≅ ringDiagonalizableGroup E N₀)` therefore
  says exactly that H ×_k E is group-isomorphic to D_E(N₀).
- `∃ N : AddCommGrpCat.{u}, AddGroup.FG N ∧ Nonempty (ringDiagonalizableGroup k N ≅ H)`
  gives the required finitely generated group N and the isomorphism in the stated
  D_k(N) to H direction. It does not require a chosen geometric isomorphism to descend.
- No smoothness, connectedness or reducedness is required. All variables and the
  sole universe are explicit; auto-implicits are disabled. The common scheme
  universe can be chosen large enough for any given extension and group. Finitely
  generated groups have small representatives, so the bundled group universe
  introduces no mathematical cardinality restriction.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its projections, used by `Over.pullback`.
  `Mathlib.AlgebraicGeometry.Pullbacks` gives scheme pullbacks and the Cartesian
  monoidal structure; `CategoryTheory.Functor.mapGrp` gives scalar extension on groups.
- `Mathlib.GroupTheory.Finiteness`: `AddGroup.FG`; `AddCommGrpCat` bundles the
  additive abelian group with no extra hypotheses.

Already stated proof dependencies are imported: the relative algebraic closure
in `Mathlib.FieldTheory.AlgebraicClosure`; affine coordinate Hopf operations and
`hopfSpec` through the public ring-diagonalizable-group import; affine tensor
pullbacks through `Mathlib.AlgebraicGeometry.Pullbacks`; finite-type composition
and base change through the public finite-type import; closed immersions through
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; embedding-existence descent
through `Sheaf.AlgebraicGeometry.AlgClosedGroupEmbeddingExistenceDescent`;
antiduality through `Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality`;
triviality of separable extensions through `Mathlib.FieldTheory.IsSepClosed`.
`lem-sfb-diagonalizable-group-geometric-criteria` has no recorded Lean declaration
at the time of reading; no proof-only missing interface is restated. The theorem
docstring carries all five accepted proof steps and their DAG references.

Edge cases checked: N₀=0 gives the trivial group and permits a rank-zero torus;
N₀=Z/pZ in characteristic p gives the nonreduced group mu_p and is allowed;
free groups of positive rank give tori; mixed free and finite torsion groups,
including disconnected groups, remain allowed. A separably closed imperfect k
is not replaced by an algebraically closed k. E/k may be transcendental or the
identity extension when k is algebraically closed. The empty scheme cannot be
a group over a field because there must be an identity section. No disputed
statement, missing notion, dependency repair or statement correction was found.

Searches actually run:

- `msearch.py leanfinder`, query "An affine finite type group scheme over a separably
  closed field which becomes diagonalizable over an algebraically closed extension
  is split diagonalizable": eight hits on affine diagonals and formally smooth/etale
  field algebras, no matching group-scheme statement.
- `msearch.py loogle`, query `ringDiagonalizableGroup, IsSepClosed`: zero hits;
  service reports unknown identifier `ringDiagonalizableGroup` (project name).
- `msearch.py grep`, query `diagonali[sz]able|multiplicativeType`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py leansearch`, query "An affine group of multiplicative type splits over
  a separably closed field": eight hits, including abstract group-extension
  splittings and separably-closed polynomial splitting, none the statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for geometric diagonalizability, diagonalizability and separably closed splitting:
  found the ring/group-algebra constructors, character antiduality and related
  rigidity/quotient statements; none states this theorem. Antiduality contains a
  finite separable splitting clause under its multiplicative-type predicate and
  is used as a proof dependency; it is not this geometric criterion itself.
- Exact item-id and proposed declaration-name searches in `lean/WeilConjectures`,
  `lean/Sheaf`, Mathlib and upstream names found no existing attachment or collision.

Validation: compile and delivery preflight results are recorded below after they run.

`scompile.py NO lem-sfb-geometric-diagonalizable-separably-closed-split <module>`
passed for the final module in both sandbox and library module modes (exit 0,
no compiler errors or warnings; library mode 6.7 seconds). Checked the Lean
line widths (all at most 100), exact signature inclusion, and that `lean` is the
only field changed from the live node.

`deliver2.py NO lem-sfb-geometric-diagonalizable-separably-closed-split --no-push`
returned `OK (dry run)`: commit `11497148a8a` passed preflight and per-file compilation.
No direct edits or Git commands were run in the read-only shared repository.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
