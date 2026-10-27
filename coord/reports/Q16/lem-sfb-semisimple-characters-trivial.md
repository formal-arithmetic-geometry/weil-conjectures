## Worker report

Stage 2 statement delivery for lem-sfb-semisimple-characters-trivial. The accepted stage-1
split and all its proof steps are preserved. The inherited BLOCKED ending referred to
stage-1 re-splitting, not this stage-2 task; coord/brief-stage2.md §0 explicitly permits
this handoff, and coord/queue.tsv lists the item at stage 2. There is no repair note.

The theorem in Sheaf.AlgebraicGeometry.SemisimpleCharactersTrivial states equality of
scheme morphisms χ = 1, with one expected sorry. The new definition module
Sheaf.AlgebraicGeometry.SemisimpleGroupScheme contains real Prop-valued data and no sorry.

Hypothesis and clause correspondence:

- An algebraically closed field F: `{k : Type u} [Field k] [IsAlgClosed k]`.
- An affine F-group scheme H of finite type: `H : Grp (Over (Spec (.of k)))` and
  `hH : SolvableGroupStructure.IsSemisimple H`. The first conjunct unfolds to
  `IsAlgebraic H`, the already recorded conjunction `IsAffine H.X.left ∧
  LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom`.
- Smoothness: `Smooth H.X.hom`, the second semisimplicity conjunct.
- Connectedness, including nonemptiness: `ConnectedSpace H.X.left`, the third conjunct.
- No nontrivial smooth connected solvable normal closed subgroup scheme: the final
  conjunct quantifies every `N : Grp (Over (Spec (.of k))))` and inclusion
  `i : N.X ⟶ H.X`, with `IsClosedSubgroupScheme i`, `IsNormalSubgroupScheme i`,
  `Smooth N.X.hom`, `ConnectedSpace N.X.left`, and `IsSolvable N`, and concludes
  `Nonempty (N ≅ Grp.trivial (Over (Spec (.of k))))`. For a subgroup the unique map
  from the trivial group is its identity section, so this is precisely triviality.
- Solvability: reuse `SolvableGroupStructure.IsSolvable`, the finite closed subnormal
  series with commutative quotients. This is equivalent to the node's terminating
  closed derived series: each derived subgroup lies in the next term of any such
  series, and the derived series itself is such a series. No rational-point substitute
  or characteristic-zero Lie algebra criterion is introduced.
- X*(H) = Hom of F-group schemes H to G_m: quantify the actual Over morphism
  `χ : H.X ⟶ StandardGroupSchemes.multiplicative k` with `[IsMonHom χ]`. The target
  is exactly the dependency's Laurent affine group, using its canonical group instance.
- Every character is the identity-valued homomorphism: `χ = 1`. Here
  `CategoryTheory.Hom.one_def` identifies `1` with `toUnit H.X ≫ η`, the structure
  map followed by the identity section; it is not an identity endomorphism. The
  scoped Hom group operation is multiplication of values, so the same equation
  says that the additively written character group is zero. Quantifying all characters
  avoids creating a redundant definition of its carrier or group structure.
- After every scalar extension: the conclusion is equality in the category of schemes
  over Spec k, not equality on k-points. Applying `Over.pullback f` to this equality
  for any scheme map f into Spec k gives equality with the pulled-back identity-valued
  map. Precomposition with any point over any algebra then gives value one. Thus this
  single morphism equality includes every scalar extension and nilpotent test algebra;
  the final clause is a consequence of equality, not an omitted pointwise assertion.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (Mathlib leaf def-weil-field).
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`; the algebraic-closure node's
  recorded match also names AlgebraicClosure and IsAlgClosure, but here the clause is
  algebraically closed, not a chosen algebraic closure.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` and `Grp`;
  Mathlib.CategoryTheory.Monoidal.Mon: `IsMonHom`. The recorded group-scheme node
  specializes them to `Over (Spec (.of k))`, as documented in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType` and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace` (Mathlib match, no lean record).
- Sheaf.AlgebraicGeometry.StandardGroupSchemes:
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and `multiplicativeGroup`.
- Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic` and `IsSolvable`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.

All statement dependencies' full node statements and recorded signatures/docstrings
were read. The dependency modules are publicly imported through the new definition
module and SolvableGroupStructure. The two proof-only nodes
lem-sfb-semisimple-group-perfect and lem-sfb-smooth-connected-derived-subgroup have no
Lean records, so their modules cannot yet be imported; their exact uses are preserved
in the theorem's proof docstring. No additional theorem is postponed.

Edge cases: H = 1 satisfies the definition and has only the identity-valued map. G_m
is excluded because it is itself a nontrivial smooth connected solvable normal subgroup.
No restriction on the characteristic, simply connectedness or dimension is imposed.
Infinitesimal central subgroups (such as μ_p) are not incorrectly prohibited: only
smooth connected solvable normal subgroups must vanish. Nonreduced test algebras and
arbitrary scalar extension are covered by equality of scheme morphisms. An empty
scheme cannot be a group scheme over a nonempty field base and is also excluded by
ConnectedSpace, exactly as in the node. The universe u is explicit; no unbound implicit
variables and no independent small test universe have been introduced.

Searches: preserved searches.jsonl records leanfinder for character vanishing (8
unrelated FDRep/MulChar results), Loogle `"Semisimple", "Character"` (0), Mathlib grep
`[Ss]emisimple.*[Cc]haracter|[Cc]haracter.*[Ss]emisimple` (Lie/linear algebra only),
LeanSearch for character triviality (MulChar/AddChar only), and the new notion searches
listed in the new node. Direct rg searches of lean/WeilConjectures and lean/Sheaf found
no group-scheme semisimplicity or character-triviality declaration. Searching the item
id in lean/WeilConjectures found none. DAG definition search found only semisimple
modules and Lie algebras; blueprint_refs.py search semisimple returned 30 blueprint
matches, none defining this notion. The existing solvability API was found and read
in full, and is reused. All searches for the new notion are recorded in its node.

Source checked directly in Milne's PDF: 6.44 defines semisimplicity by trivial radical;
12.45 defines perfectness by equality with the derived group; 21.50 proves semisimple
groups perfect; 6.19(d) supplies triviality of maps to commutative groups even after
arbitrary algebra extension. The latest blueprint direct-images proof paragraph (3)
was read and agrees with the inherited supporting-chain location. No statement
correction, dependency-interface repair or STATEMENT-DISPUTED issue is required.

## New nodes

def-sfb-semisimple-group-scheme owns the missing definition
`AlgebraicGeometry.SolvableGroupStructure.IsSemisimple`, over algebraically closed
fields. It packages exactly the semisimplicity hypotheses already written in the item.
Its source is Milne 6.44 with the existing solvability terminology of 6.26. The searches
in its mathlib_searches distinguish this from semisimple modules, Lie algebras and
representations. No existing DAG definition or project declaration owns this notion.
Its definition reuses IsAlgebraic, IsSolvable and the recorded subgroup-scheme classes;
the item gains this node in stmt_deps. No pre-existing dependency node is changed.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
