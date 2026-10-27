## Worker report

The sole delivered module,
`Sheaf.AlgebraicGeometry.SemisimpleCentralIsogenyMultiplicative`, states
`AlgebraicGeometry.semisimpleCentralIsogeny_multiplicative`. Its only theorem
proof is `by sorry`, and its docstring retains every accepted DAG proof step.
The item statement, proof, proof dependencies and Lean signature are unchanged.
The item adds the already landed definition nodes
`def-sfb-semisimple-group-scheme` and
`def-sfb-finite-diagonalizable-group-scheme` to its statement dependencies.
No new definition or dependency module is delivered.

### Returned-delivery repair (H4/H13)

The return concerns immutable head `4f822e210a48`. Q102's delivery
`c6f7f6183` landed the semisimplicity node after that head's base.
The first resumed dry run refreshed the base and passed mechanically, but still
included our superseded definition; that packet was not pushed.

Removed from this packet both
`lean/Sheaf/AlgebraicGeometry/SemisimpleGroupScheme.lean` and
`dag/nodes/sec-six-functors-basics/def-sfb-semisimple-group-scheme.json`.
The item now publicly imports
`Sheaf.AlgebraicGeometry.GroupScheme.Semisimple` and uses Q102's existing
`AlgebraicGeometry.IsSemisimpleGroupScheme`. Its full signature and docstring,
and its derived-series helpers, were read in the current shared source.
The declaration name and argument signature remain compatible, so the item's
`lean.statement` is verbatim unchanged. Removed
`def-sfb-solvable-group-structure` from the item's `stmt_deps`: no declaration
from that node is used directly. The delivery wrapper rebases the remaining
packet on current main; Q102's landed node is cited without being overwritten.

The maintainer's note about equivalence of Q102's `IsSolvableGroupScheme` and
Q116's `SolvableGroupStructure.IsSolvable` is an upstream consolidation issue.
This delivery defines neither predicate and uses only the former, through the
landed semisimplicity definition. It introduces no additional solvability API.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| F-group schemes and their homomorphism | `(G1 G0 : Over (Spec (.of F))) [GrpObj G1] [GrpObj G0]`, `(f : G1 ⟶ G0) [IsMonHom f]` |
| Semisimple G1 and G0 | `hG1 : IsSemisimpleGroupScheme G1`, `hG0 : IsSemisimpleGroupScheme G0` |
| Smooth, connected, affine, finite type | The predicate includes `Smooth G.hom ∧ ConnectedSpace G.left ∧ IsAffine G.left ∧ LocallyOfFiniteType G.hom ∧ QuasiCompact G.hom` |
| No nontrivial smooth connected solvable normal closed subgroup | For every N and inclusion i, its remaining clause is `IsClosedSubgroupScheme i → IsNormalSubgroupScheme i → Smooth N.hom → ConnectedSpace N.left → IsSolvableGroupScheme N → Nonempty (IsTerminal N)` |
| Solvability by terminating scheme-theoretic derived series | The landed `IsSolvableGroupScheme N` is `∃ n, GroupSchemeDerivedLength N n`. Each successor uses `IsDerivedGroupScheme`, the smallest closed subgroup through which `groupSchemeCommutator` factors; length zero is terminality over F. |
| Surjective on underlying schemes | `[Surjective f.left]` |
| Scheme-theoretic kernel | `GrpObj.ker f`, the upstream pullback along the identity section, with inclusion `GrpObj.kerι f` |
| Finite kernel, equivalently finite-dimensional coordinate algebra | `[IsFinite (GrpObj.ker f).hom]` |
| Central after every commutative F-algebra extension | `hcentral : ∀ T x g, (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)` |
| Faithfully flat coordinate map F[G0] → F[G1] | `f.left.appTop.hom.FaithfullyFlat` |
| Kernel D(M) for a finite abelian group M | `IsFiniteDiagonalizableGroupScheme (GrpObj.ker f)` |
| Multiplicative isogeny | The conjunction of the preceding faithful-flat and diagonalizable conclusions, together with kernel finiteness already in the hypotheses |
| No separability or prime-to-characteristic restriction | There is no characteristic, order, reducedness, smoothness or etaleness hypothesis on the kernel. |

Centrality quantifies over every F-scheme T. On affine tests this is exactly
centrality after every algebra extension, including nonreduced extensions;
affine-local equality and gluing give the equivalent arbitrary-scheme form.
Terminality of a subgroup is its triviality as a group scheme, rather than
triviality of just its rational points. A closed subgroup of an affine
finite-type F-group is itself affine and finite type, so these need not be
repeated as hypotheses in the semisimplicity predicate.

The existing finite-diagonalizable predicate supplies a natural group
isomorphism on all test schemes with `Hom(M, Γ(T, O_T)ˣ)` for a finite abelian
group M. Milne Proposition 12.3 identifies this represented functor with Spec
F[M] with the node's multiplication, comultiplication, counit and antipode.
`RingHom.FaithfullyFlat` expresses flat extension of scalars detecting zero
modules. For a scheme over a field, `IsFinite` means affine with coordinate
algebra finite-dimensional. Thus every clause retains scheme structure.

### Dependency declarations

The original statement dependencies were read with their source declarations:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic; no selected algebraic closure is needed.
- `def-sc-group-scheme`: `GrpObj` and `IsMonHom`, with upstream `GrpObj.ker`
  and `GrpObj.kerι` through
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs and
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- `def-sbc-smooth-morphisms`: `Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-sc-gm-ga`: `StandardGroupSchemes.multiplicative`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes. Its original public import is
  retained; the diagonalizable predicate packages the final conclusion.
- `def-sfb-semisimple-group-scheme`: `IsSemisimpleGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple, including its real-data
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`
  and `groupSchemeCommutator` helpers. This is the Q102 landed declaration.
- `def-sfb-finite-diagonalizable-group-scheme`:
  `IsFiniteDiagonalizableGroupScheme`,
  Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme.

The coordinate-map conclusion also uses `RingHom.FaithfullyFlat` from
Mathlib.RingTheory.RingHom.FaithfullyFlat. Plain proof imports remain
Mathlib.AlgebraicGeometry.Pullbacks (`pullbackSpecIso`),
Mathlib.RingTheory.Spectrum.Maximal.Basic (maximal ideal existence),
WeilConjectures.Mathlib.RingTheory.Nullstellensatz
(`exists_algHom_ker_eq_of_isMaximal`), and
Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
(`affine_normal_quotient_geometry`). Kernel and closed-immersion interfaces are
available through the public imports.

The saved investigation found no recorded Lean interface for these proof-only
nodes: lem-sfb-affine-group-homomorphism-image,
lem-sfb-smooth-unipotent-solvable,
lem-sfb-reductive-centre-multiplicative-type,
lem-sfb-affine-group-centre-base-change,
lem-sfb-split-torus-subgroups-diagonalizable. They are not needed to type the
statement. Their proof roles remain explicit in the docstring.

### Source and edge cases

The original investigation read Milne, Algebraic Groups (2017), Definition
18.1 and following paragraph, printed p.387; Chapter 19(a), pp.397–398;
reductivity and Proposition 19.15 and proof, pp.400–401; Propositions 6.18 and
6.30, pp.129 and 132. Central implies multiplicative for reductive source,
including the semisimple case. The landed derived-series predicate now directly
renders the item's solvability convention. No statement correction or dispute
is needed.

Checked trivial groups and identity maps: the trivial finite character group
and trivial kernel are allowed. Derived length zero means a terminal group,
not arbitrary G. Taking N = G excludes nontrivial smooth connected commutative
groups from semisimplicity. The map SL_p → PGL_p in characteristic p remains
allowed with its nonreduced kernel μ_p. Noncentral Frobenius kernels fail the
centrality hypothesis. Disconnected smooth central subgroups and connected
nonsmooth central subgroups do not violate the smooth AND connected normal
subgroup condition. Empty test schemes have singleton points groups.

Every variable and universe is explicitly bound. Test schemes are in the same
universe as G, sufficient for Yoneda and affine localization; no smaller-test
vacuity or extra universe equality is imposed.

### Searches

The saved investigation used the prescribed msearch.py wrapper:

- LeanFinder, central isogenies of semisimple affine group schemes with faithful
  flatness and finite diagonalizable kernels: no exact theorem.
- Loogle, `"Isogeny", "central"`: no hits.
- LeanSearch, semisimple affine group schemes without nontrivial smooth connected
  solvable normal subgroups and scheme-theoretic derived series: abstract-group,
  Lie and module results, no group-scheme definition.
- LeanFinder, smallest closed commutator subgroup: abstract-group results only.
- Loogle, `"IsSolvable", "GrpObj"`: no hits.
- Mathlib grep, `IsSemisimpleGroupScheme|IsSolvableGroupScheme|IsDerivedClosedSubgroupScheme|ContainsCommutators`,
  and `semisimple|solvable|derived.*subgroup` in AlgebraicGeometry: no matches.
- Direct rg in lean/WeilConjectures and lean/Sheaf and exact item-id search:
  no theorem matching this item. Found commutator factorization and derived
  ideals for fixed GL_n presentations, not a general semisimplicity definition.
- DAG scan and tools/blueprint_refs.py search semisimple: no such definition
  at the original base. This finding was superseded by Q102's landing.

During repair, inspected the current landed semisimplicity node and its full
module. Found the exact predicate already supplied by Q102, as stated in the
return, and removed our duplicate. The historical searches explain the earlier
draft; the final packet uses the existing node. Saved raw search outputs remain
in the sandbox as research material and are not delivered.

### Validation

All compilation uses scompile.py against the live server build. The repaired
single item module is compiled with the landed Q102 import. The prescribed
deliver2.py dry run and delivery compile the one remaining module and run the
server preflight. Only the theorem proof contains `sorry`. No direct git
mutation, local Lean invocation, global build or shared-source edit is used.

## Second reading by Q61

Read the final item node and theorem against the current Q102 semisimplicity
source. Matched the field and both group objects, both semisimplicity premises,
homomorphism, scheme-surjectivity, kernel finiteness and centrality on all test
schemes. Matched the two conclusions to coordinate faithful flatness and finite
diagonalizability, retaining infinitesimal tests. Read the derived-series
helpers: the commutator has the correct `xyx⁻¹y⁻¹` order, minimality is among
closed subgroup schemes containing its factorization, and length zero is
terminality. This directly matches the node's solvability convention.

The mismatch found was the stale duplicate semisimplicity module/node. Both
were removed and the landed import substituted. The unused direct solvability
node dependency was removed. The theorem signature is unchanged and its saved
`lean.statement` matches verbatim. The final packet has one module and one item
node, with no definition or dependency-node overwrite. The dispatcher forbids
other agents, so this is an in-thread second reading; the maintainer supplies
the independent review.
