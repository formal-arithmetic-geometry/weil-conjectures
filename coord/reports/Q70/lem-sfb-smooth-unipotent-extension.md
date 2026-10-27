## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothUnipotentExtension` states
`AlgebraicGeometry.SolvableGroupStructure.isUnipotent_of_isFppfQuotient`, with `sorry`
as its entire proof. The node changes only in `lean`. No new notions, dependency
repairs, or statement corrections are needed.

The previous ending concerned the stage-1 prohibition against splitting a reviewed
node. The current stage-2 brief §0 explicitly permits recording its Lean statement.
The live node is split and reviewed by NW but has no Lean record. Its queue row is
stale stage-1 metadata; this assigned stage-2 delivery preserves its accepted split.
No released repair note exists, and `coord/returns/Q70.md` is empty. The example
CompactObject module is now withdrawn; the delivered header follows the current
module conventions and the existing SolvableGroupStructure module.

Hypothesis and conclusion correspondence:

- An algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- The three k-group schemes: `(N E Q : Grp (Over (Spec (.of k))))`.
  The bundled groups carry their multiplication, inverse and identity diagrams.
- Smoothness of each structure map: `[Smooth N.X.hom]`, `[Smooth E.X.hom]`,
  and `[Smooth Q.X.hom]`.
- Affineness of each scheme: `[IsAffine N.X.left]`, `[IsAffine E.X.left]`,
  and `[IsAffine Q.X.left]`.
- Finite type of each structure map: `[LocallyOfFiniteType G.X.hom]` and
  `[QuasiCompact G.X.hom]` for each of N, E and Q, exactly the recorded convention
  of def-weil-finite-type-morphism.
- The subgroup inclusion and quotient homomorphism: `(i : N ⟶ E) (q : E ⟶ Q)`.
  These are morphisms of bundled group objects, hence group-scheme homomorphisms.
- Closed normal subgroup: `[IsClosedSubgroupScheme i.hom.hom]` and
  `[IsNormalSubgroupScheme i.hom.hom]`. These are the upstream classes, including
  injectivity and normality on all commutative k-algebra points.
- The represented fppf quotient E/N: `(hq : IsFppfQuotient i.hom.hom q)`.
  Unfolding the existing definition gives Flat, Surjective and
  LocallyOfFinitePresentation for q, and an isomorphism from N to the
  scheme-theoretic kernel whose composite with the kernel inclusion equals i.
- Unipotence of N and Q: `(hN : IsUnipotent N) (hQ : IsUnipotent Q)`.
  The existing predicate requires smoothness and a representation into GL_n,
  a closed subgroup immersion, and for each point over every algebraically
  closed extension a positive power of its matrix minus identity equal to zero.
- Unipotence of E: conclusion `IsUnipotent E`, using exactly the same predicate.
- There is no connectedness, commutativity, centrality or characteristic-zero
  binder. In particular noncommutative and disconnected positive-characteristic
  extensions remain covered.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (via the public statement import).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the algebraic-closure
  node's match explicitly records this component as well as AlgebraicClosure.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`,
  `CategoryTheory.GrpObj`, for group objects in the category over Spec k.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, with their common
  `IsSubgroupScheme` parent.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsUnipotent`,
  `IsFppfQuotient`. Its public import exposes all the statement dependencies.
  `IsAlgebraic` was read: its conjunction is the three explicit affine and
  finite-type binders used here.

The already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary` and
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`. The other five
proof-dependency nodes currently have no Lean record or Mathlib match, so there
is no module to import. Their full seven-step proof plan is retained in the
new theorem's docstring; none is an added hypothesis of the statement.

Source checked directly in the local PDF: Milne, Algebraic Groups (2017), §6.45,
printed p.135, including its footnote; Proposition 14.3, Theorem 14.5,
Corollaries 14.6--14.7 and 14.12, printed pp.280--283. The source proves closure
under extensions by the nonzero N-invariant space and its descended Q-action.
Its smooth geometric-matrix formulation is exactly the existing predicate.

Edge cases checked before writing: N = 1, Q = 1 (N = E), and all three groups
trivial; characteristic zero and positive characteristic; disconnected constant
finite p-groups (including nonabelian extensions); matrix rank zero for the
trivial representation, which the recorded predicate permits, and positive
nilpotence exponent (required within that predicate). No positive-dimensional
or connectedness restriction appears in the theorem. Universe `u` is explicit
for the field and all schemes; the imported predicate quantifies over extension
fields in that same universe, rather than an independent smaller test universe.
Its definition and its matrix interface are reused without modification.

Searches made (all 2026-10-24):

- `msearch.py ... leanfinder "An extension of smooth unipotent affine algebraic
  groups is unipotent"`: eight unrelated abstract nilpotent group and Lie group
  hits, including `isNilpotent_prod`; no match.
- `msearch.py ... loogle "IsUnipotent, IsFppfQuotient"`: zero hits, unknown
  identifier IsUnipotent in the Mathlib search index.
- `msearch.py ... leansearch "If kernel and quotient of an affine algebraic group
  are unipotent then the group is unipotent"`: eight abstract nilpotent quotient
  and group-kernel hits; no algebraic-group extension theorem.
- `msearch.py ... grep "unipotent|Unipotent" AlgebraicGeometry`: zero Mathlib hits.
- `rg` on Mathlib, upstream WeilConjectures and `dag/lean_names_upstream.json`
  for unipotent and the proposed name: no matching extension statement.
- `grep -rn "lem-sfb-smooth-unipotent-extension" lean/WeilConjectures`: no hits.
- `rg` on `lean/Sheaf` for unipotent extension phrases, IsUnipotent and
  IsFppfQuotient: found the recorded definitions and consumers, including the
  proof-plan citation in SplitReductiveAffineSpaceQuotient; no existing theorem.

Validation: the prescribed `scompile.py Q70 lem-sfb-smooth-unipotent-extension`
compiled both its sandbox probe and actual module successfully (4.1 s and 2.5 s),
with no error or unexpected warning. All variables and universe levels are bound;
`autoImplicit` is false. Every theorem body in the delivery is exactly `sorry`.

## Second reading by Q70

A separate final rereading by this worker opened the node, imported definitions
and complete delivered file together; the maintainer supplies the independent
review, as specified in the assignment. No other agent was started.

The field and three bundled groups match the objects in the first two sentences.
All nine smooth/affine/finite-type conditions are present (finite type uses two
classes). Both maps preserve the group structures. The closed and normal
subgroup binders use the exact recorded upstream classes. The quotient binder
uses the actual q and i, not an arbitrary isomorphic quotient or a pointwise-only
kernel. The two hypotheses and conclusion use one existing geometric-matrix
unipotence predicate, so neither faithful immersion nor algebraically closed
extension testing nor the positive exponent was omitted. No connectedness,
commutativity, centrality or characteristic hypothesis was introduced. The
explicit smoothness binders match the node even though IsUnipotent also carries
smoothness. The proof docstring matches all seven unchanged DAG proof steps,
including the zero-dimensional flag case and the final faithful matrix embedding.
No mismatch was found and no source statement was changed.
