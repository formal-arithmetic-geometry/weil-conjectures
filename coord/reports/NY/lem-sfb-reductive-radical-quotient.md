## Worker report

The module `Sheaf.AlgebraicGeometry.ReductiveRadicalQuotient` states
`AlgebraicGeometry.reductive_radical_quotient`, with its proof `sorry`. It introduces
no definitions, axioms, chosen objects, or helper theorems. All mathematical
predicates and constructions are existing published declarations. The only node
changes are its Lean record and addition of the five existing statement interfaces
listed below to `stmt_deps`. The mathematical statement is unchanged.

I read Milne's Corollary 17.62 and proof on printed pp.372--373 directly from the
PDF (PDF pages 384--385). The statement matches (b), (c) restricted to the asserted
algebraic closure, and (d), with the definitions and quotient geometry specified
in the node. The module docstring gives all seven steps of the node's proof and
names the corresponding DAG prerequisites. The example Sheaf CompactObject module
is now withdrawn; I also read its recorded replacement,
`WeilConjectures.CategoryTheory.CompactObject`, for the current module conventions.

Hypotheses, one by one:

- The field is `{k : Type u} [Field k]`; no characteristic or perfectness restriction.
- The group scheme is `G : Grp (Over (Spec (.of k)))`. This bundles the existing
  `GrpObj` operations and axioms, and its arrows are group-scheme homomorphisms.
- `hG : ReductiveTorusCentralizer.IsReductive G` is exactly the package specified
  in the node: `IsAlgebraic G` (affine, locally finite type, quasi-compact),
  `Smooth G.X.hom`, connectedness of the actual pullback to `AlgebraicClosure k`,
  and triviality of every connected closed normal smooth unipotent geometric
  subgroup. Its `IsUnipotent` includes smoothness and a faithful closed matrix
  representation with `(u - 1)^N = 0`, `0 < N`, at all algebraically closed
  extension points. I read the complete definitions, not just their names.

Conclusions, one by one:

- `∃ R i` supplies the radical with its actual inclusion `i : R ⟶ G`.
  `IsAlgebraic R`, `Smooth R.X.hom`, `ConnectedSpace R.X.left`,
  `IsClosedSubgroupScheme i.hom.hom`, `IsNormalSubgroupScheme i.hom.hom`, and
  `IsSolvable R` give every required property.
- The first `∀ N j` says every smooth connected normal solvable closed subgroup
  factors as `f ≫ i = j`. This is *largest*, not merely maximal. The affine
  finite-type condition on competitors is automatic for closed subgroups of the
  given affine finite-type group. This therefore excludes no subgroup in the node.
- Solvability is the existing `SolvableGroupStructure.IsSolvable`: a finite
  closed normal series from the group to the trivial group, with all commutators
  factoring through the next subgroup on all commutative algebras. This is the
  exact scheme-theoretic commutative-quotient criterion, not solvability of an
  abstract group of rational points.
- `MultiplicativeType.IsTorus R` uses the actual algebraic-closure pullback and a
  finite product of the recorded multiplicative group, including the empty
  product at rank zero.
- The `∀ A r` clause places every R(A)-point in
  `centralizerPoints (𝟙 G) A`. Unfolding that recorded definition quantifies
  over every k-algebra map A → B and every G(B)-point, so it is exactly membership
  in the node's centre functor. It tests nonreduced algebras too.
- The `∀ T j` clause quantifies over every closed torus inclusion whose points
  satisfy that same universal centre condition. The equation `f ≫ i = j`
  gives its containment in R. Together with R being a central torus, this is
  precisely the largest subtorus of Z(G); no choice of a representing centre is
  necessary to state it, and no second centre definition is introduced.
- The next six conjuncts assert that the *actual pulled-back* inclusion
  `(MultiplicativeType.baseChange (K := AlgebraicClosure k)).map i` is affine of
  finite type, smooth, connected, closed, normal, and solvable. The second
  `∀ N j` supplies its largest-subgroup property among all geometric smooth
  connected normal solvable closed subgroups. This is equality with the geometric
  radical as a closed subgroup, independent of representatives. Closed
  monomorphisms make each factorization unique; applying the property to any
  other radical inclusion yields inverse isomorphisms commuting with inclusions.
  No equality of points over fields is substituted for scheme-theoretic equality.
- `∃ Q q` retains the quotient group and quotient homomorphism. The existing
  `IsFppfGroupQuotient i q` specifies its scheme-theoretic kernel, fppf local
  surjectivity, represented sheaf, canonical torsor map, and coset-presheaf
  sheafification universal property. This represents exactly the stated fppf
  sheaf quotient, rather than an arbitrary quotient on rational points.
- `ReductiveTorusCentralizer.IsReductive Q` includes smoothness, affineness,
  finite type, geometric connectedness, and the required geometric unipotent
  subgroup triviality.
- `IsSemisimpleGroupScheme` of the actual geometric Q is the existing definition
  from `def-sfb-semisimple-group-scheme`: smooth connected affine finite type,
  with all smooth connected solvable normal closed subgroups trivial. Its
  solvability is stated by termination of the scheme-theoretic derived series
  (Milne 6.30), equivalently existence of the finite subnormal series in this
  node: each derived subgroup factors through the next term of any such series,
  while the terminating derived series itself is such a series. Its triviality
  is terminality of the underlying scheme over the field, equivalent to the
  trivial group scheme, not merely trivial rational points. No definition is
  duplicated. Thus this clause is geometric semisimplicity exactly as requested.

Dependency interfaces read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`,
  `multiplicative`, and `multiplicativeGroup` (the latter underlies the torus).
- Existing added dependency `def-sfb-solvable-group-structure`, module
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsSolvable`,
  `IsUnipotent` (through reductivity).
- Existing added dependency `def-sfb-tori-multiplicative-type`, module
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `baseChange`, `IsTorus`,
  and `splitTorus` (through `IsTorus`).
- Existing added dependency `def-sfb-reductive-torus-centralizer-terminology`,
  module `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `IsReductive` and `centralizerPoints`.
- Existing added dependency `def-sfb-semisimple-group-scheme`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSemisimpleGroupScheme`,
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`.
- Existing added dependency `def-sfb-fppf-group-quotient-presentation`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`. This existing:true definition node owns the plain
  Prop-valued quotient-presentation interface. The theorem node
  `lem-sfb-affine-normal-quotient-geometry` remains only in `proof_deps`.

Proof dependencies with Lean records are imported: PerfectSolvableUnipotentTorus,
MultiplicativeTypeLargestSubtorus, AffineGroupCentreBaseChange, and
GroupScheme.AffineNormalQuotientGeometry (public because also used in the statement).
The other four proof dependencies have no Lean records yet, so there is no module
to import for them: lem-sfb-solvable-normal-subgroup-products,
lem-sfb-connected-action-torus-rigidity,
lem-sfb-reductive-centre-multiplicative-type, and
lem-sfb-smooth-unipotent-solvable. These are future proof inputs, not missing
notions needed to type the present statement.

Edge cases checked mathematically before writing:

- G = 1: R = 1, rank-zero torus, Q = 1, and both universal properties hold.
- G a torus: R = G and Q = 1. The torus definition admits every finite rank.
- GL_n: R is the scalar torus and Q is PGL_n (including the trivial n = 1 quotient).
- SL_p in characteristic p: its non-smooth centre μ_p is not incorrectly declared
  to be a torus or the radical. R is trivial; Q = SL_p is semisimple and reductive.
- Imperfect fields and positive characteristic are retained; only the geometric
  reductivity test uses an algebraic closure. There is no claim about radical
  base change for arbitrary nonreductive groups.
- Group schemes have an identity section and are nonempty. `ConnectedSpace`
  correctly excludes the empty scheme. All group schemes and test algebras use
  the common universe u; there is no smaller independent test universe that
  would make universal conditions vacuous.

Searches for existing declarations (2026-10-24):

- msearch.py leanfinder: “The radical of a reductive algebraic group is its largest
  central torus and the quotient is semisimple” returned eight Lie-algebra/root
  system results, no group-scheme theorem.
- msearch.py leansearch: “radical of reductive group scheme largest central torus
  semisimple quotient” returned Lie radicals and scheme ideal radicals, no match.
- msearch.py loogle: `AlgebraicGeometry.IsReductive, AlgebraicGeometry.radical`
  returned no hits (unknown global `AlgebraicGeometry.IsReductive`). The actual
  project predicate was then found by source search in its recorded namespace.
- msearch.py grep: `radical|IsReductive|IsSemisimple` in Mathlib AlgebraicGeometry
  returned 21 ideal/graded ring hits, no group-scheme radical theorem.
- rg of `radical|Reductive|Semisimple|Solvable|IsTorus|Unipotent`, and later
  `IsReductive|IsSemisimple|IsSolvable|IsTorus|IsUnipotent`, in the project sources
  found the existing interfaces above. The source signature and docstring of
  each were opened. The older semisimple interface uses scheme-theoretic derived
  series; the solvable-structure interface uses the normal series required here.
- rg of this item's id and `radical.*quotient|radical.*torus` across
  lean/WeilConjectures and lean/Sheaf found no declaration of this theorem.
  rg of `reductive_radical_quotient` in dag/lean_names_upstream.json and both
  source trees found no name collision. Blueprint latest search similarly found
  no competing group-scheme radical statement; this node is a supporting input
  under the six-functor-stability unit, not the unit's own statement.

Validation: scompile.py compiled this single module on the server against the live
published build in 3.0 s (sandbox) and 3.6 s (library), with no errors or warnings.
The added explicit imports of already transitive statement interfaces are checked
again by the prescribed deliver2.py preflight. All binders/universes are explicit,
`autoImplicit` is false, and every Lean line has at most 100 characters.

No STATEMENT-DISPUTED finding, statement correction, dependency repair, or new node.

## Returned-delivery repair

H2, returned immutable head c2919f1b2c9f: replaced the added statement dependency
`lem-sfb-affine-normal-quotient-geometry` with the existing definition node
`def-sfb-fppf-group-quotient-presentation` (Q95). I read that node's statement and
Lean record and reopened its recorded definition, `AlgebraicGeometry.IsFppfGroupQuotient`,
in `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`, lines 60 onward.
It is exactly the plain Prop-valued kernel/torsor/sheafification interface used
in the theorem's statement. The quotient-geometry theorem remains in `proof_deps`;
its module remains a public import because it also provides this definition.
The other four added definition dependencies are retained.

Compared the retained sandbox node with current main: every field except the
authorized `lean` and `stmt_deps` agrees. No mathematical statement, proof plan,
proof dependency, Lean signature, or Lean source byte was changed by this repair.
The delivery wrapper rebases the corrected packet onto current main. The prior
independent clause-by-clause mathematics review remains applicable.

Lean module SHA-256 before and after the metadata repair: `c67714d52e55353025a5b7c50bd4f8392c89366d857a1bbc246d5eaf26e941e9`.
Compilation, dry-run preflight, and delivery are rerun using the prescribed wrappers.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
