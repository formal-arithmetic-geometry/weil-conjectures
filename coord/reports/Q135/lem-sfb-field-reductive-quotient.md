## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FieldReductiveQuotient` states
`AlgebraicGeometry.isReductive_of_faithfullyFlat`. Its only theorem has proof `sorry`;
there are no new definitions. The statement and accepted six-step split are unchanged.
The statement dependencies gain the already landed
`def-sfb-reductive-torus-centralizer-terminology`, whose `IsReductive` is reused.

Clause-by-clause rendering:

- An algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- The two k-group schemes: `(H J : Grp (Over (Spec (.of k))))`. `Grp` bundles
  `GrpObj`; `GrpObj` is exactly the recorded `def-sc-group-scheme` group-object notion.
- Smoothness of each group: `[Smooth H.X.hom]`, `[Smooth J.X.hom]`.
- Connectedness: `[ConnectedSpace H.X.left]`, `[ConnectedSpace J.X.left]`.
  These classes include nonemptiness, as required by the node.
- Affineness: `[IsAffine H.X.left]`, `[IsAffine J.X.left]`.
- Finite type: `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, and
  the two corresponding classes for J. This is exactly the recorded finite-type
  convention, with no restriction on dimension or characteristic.
- A homomorphism q: `(q : H ⟶ J)` is a bundled group-object morphism, whose
  underlying over-map `q.hom.hom` carries `IsMonHom` automatically. There is no
  additional arbitrary action or choice of a kernel.
- Faithful flatness: `[Flat q.hom.hom.left] [Surjective q.hom.hom.left]`.
  This is scheme faithful flatness. Since both schemes are affine it is equivalent
  to faithful flatness of the coordinate-ring homomorphism by the existing
  `AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`
  in `Mathlib.AlgebraicGeometry.Morphisms.Flat` (lines 169--177).
- H reductive: `(hH : ReductiveTorusCentralizer.IsReductive H)`.
- Conclusion J reductive: `ReductiveTorusCentralizer.IsReductive J`.
  The reused predicate requires affine finite type, smoothness, geometric
  connectedness and triviality of every connected closed normal unipotent subgroup.
  Its `SolvableGroupStructure.IsUnipotent` includes smoothness and an actual faithful
  closed matrix representation, with unipotent matrices over all algebraically
  closed extension fields. Thus the subgroup quantifier is exactly over smooth
  connected normal unipotent closed subgroups. Requiring affine finite type for
  these subgroups adds no condition: closed subgroups of an affine finite-type
  group are affine finite type. The algebraic-closure formulation is equivalent
  over algebraically closed k, since its algebraic closure is isomorphic over k
  to k itself. This is already the convention used by the normal-subgroup
  reductivity dependency, not a new reductivity predicate.
- No condition on the scheme-theoretic kernel: no such binder occurs. In
  particular there is no smoothness, connectedness, centrality or finiteness
  assumption on it.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (via the field and scheme imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`;
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
  The item needs algebraic closedness, not the data of a specified closure.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, bundled `Grp`, `Grp.trivial`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`, `Mon.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`; its existing
  `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent` definitions were read in
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.

All recorded proof-dependency modules are imported non-publicly: pullbacks,
closed immersions, group-scheme subgroups and kernels, affine-hom rational points,
locally algebraic identity components, smooth-ambient normality, connected normal
subgroup reductivity, torus self-centralizers, neutral-component translates,
smooth geometric reducedness, reduced schemes, and the affine Nullstellensatz.
The `lem-wf-affine-nullstellensatz-vanishing` attachment omits a module field;
its actual declarations occur in
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`, which is imported.
The three proof nodes `lem-sfb-geometric-unipotence-unitriangular-embedding`,
`lem-sfb-diagonalizable-to-unipotent-trivial`, and
`lem-sfb-cartan-subgroups-generate` currently have no recorded Lean declarations;
no import is invented for them. They are future proof prerequisites, not missing
notions needed to type this theorem. The docstring includes all six accepted proof
steps, with the respective node ids, including the final algebraic-closure transport.

Source check: opened Conrad's actual PDF at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.10--11.
The paragraph preceding Definition 1.1.11 explicitly treats quotient maps with
nonsmooth kernel in positive characteristic; the paragraph after the definition
states inheritance of reductivity by images. No statement correction is needed.

Edge cases checked before writing: H = J = 1; identity q; H -> 1; projections
from products of reductive groups (positive-dimensional, possibly noncentral
kernels); Frobenius of SL2 in positive characteristic (infinitesimal nonsmooth
kernel); SL2 -> PGL2 in characteristic 2 (nonsmooth central kernel). Every case
is admitted by the signature. No characteristic-zero or perfectness hypothesis
is inserted; algebraic closedness already implies perfection. An empty scheme
cannot be a group scheme over the nonempty field spectrum. Rank zero and
zero-dimensional unipotent subgroup cases are retained. The universe `u` is
explicit; schemes, k, its closure, and test algebras in the reused predicates use
the established common universe, with no independently smaller test universe.

Searches performed through msearch.py (Q135, this item), supplemented by direct rg:

- LeanFinder: “A faithfully flat quotient of a smooth connected affine reductive
  algebraic group over an algebraically closed field is reductive”: 8 hits on
  smooth/flat algebras and geometric reducedness; no reductive-quotient theorem.
- Loogle: `IsReductive, IsUnipotent`: no hits, unknown `IsReductive`.
- Mathlib grep: `Reductive|reductive` in `AlgebraicGeometry`: 0 hits.
- LeanSearch: “A faithfully flat quotient of a connected reductive algebraic group
  over an algebraically closed field is reductive”: 8 hits on module/ring faithful
  flatness, none concerning reductive group schemes.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for reductive, unipotent,
  quotient, surjectivity and image: the existing terminology and normal-subgroup
  theorem were found and reused; no declaration states this quotient assertion.
  Direct search for the item id in `lean/WeilConjectures` found no match.
- The definition nodes `def-sfb-reductive-torus-centralizer-terminology` and
  `def-sfb-solvable-group-structure` and their full recorded definitions were read.
  No duplicate notion or helper node is introduced.

No STATEMENT-DISPUTED issue or dependency-interface defect was found.

## Second reading by Q135

This is the dispatcher's single-worker delivery; no second agent was started.
I separately reread the node and final file against each binder and conclusion.
The base field is algebraically closed, both groups have all four required
properties, and the bundled q is a group homomorphism with exactly faithful
flatness. The conclusion is the same existing reductivity predicate as the
hypothesis. Smoothness of the quantified unipotent subgroups is present inside
`IsUnipotent`, and geometric connectedness over the chosen algebraic closure
is equivalent to connectedness here. The nonreduced-kernel examples remain
available. No hypothesis or conclusion mismatch was found. The statement and
proof split have not been corrected or weakened. Only the recorded dependency
on the already landed reductivity definition was added; no definition was copied.
