## Worker report

The module `Sheaf.AlgebraicGeometry.CharZeroSemisimpleGroupLie` states
`AlgebraicGeometry.semisimpleGroupScheme_lie_hasTrivialRadical` with one `sorry`.
No definition or proof is introduced. The mathematical statement is unchanged.
The sole non-lean node change adds the already landed definition node
`def-sfb-semisimple-group-scheme` to `stmt_deps`, so the existing definition is used.

Hypothesis and clause correspondence:

- The field F is `(F : Type u) [Field F]`; algebraic closedness is `[IsAlgClosed F]`,
  and characteristic zero is `[CharZero F]`.
- The F-scheme is `(G : Scheme.{u}) [G.Over (Spec (.of F))]`, with its group
  operations supplied by `[GrpObj (G.asOver (Spec (.of F)))]`.
- `hG : IsSemisimpleGroupScheme (G.asOver (Spec (.of F)))` unfolds to
  `Smooth G.hom`, `ConnectedSpace G.left`, `IsAffine G.left`,
  `LocallyOfFiniteType G.hom`, `QuasiCompact G.hom`, and the subgroup condition
  (here G in these projection expressions denotes the bundled over-scheme).
  Thus the five geometric conditions are hypotheses within hG, not omitted.
- The subgroup condition quantifies over every group scheme N and inclusion i,
  with `IsClosedSubgroupScheme i`, `IsNormalSubgroupScheme i`, `Smooth N.hom`,
  `ConnectedSpace N.left`, and `IsSolvableGroupScheme N`, and concludes
  `Nonempty (IsTerminal N)`. Terminality over Spec F means precisely the trivial
  group scheme; it does not merely assert triviality of F-valued points.
- `IsSolvableGroupScheme` is the existing scheme-theoretic derived-length
  predicate. `IsDerivedGroupScheme` requires a smallest closed subgroup through
  which the commutator morphism factors, so the node's commutator convention is
  retained, including scheme structure and nonreduced test algebras.
- The canonical g = T_e G is `GrpObj.Lie (G.asOver (Spec (.of F)))`, with its
  upstream scalar, additive, bracket, LieRing and LieAlgebra instances. It is
  exactly the object and bracket of the recorded differentiation theorem; no
  arbitrary Lie structure is an argument. Its finite dimensionality follows
  from the first clause of that theorem using the geometric clauses of hG.
- The conclusion is `LieAlgebra.HasTrivialRadical F (GrpObj.Lie ...)`, precisely
  the predicate recorded on `def-wf-semisimple-lie-algebra`.
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` identifies it with
  `∀ I : LieIdeal F (GrpObj.Lie ...), LieAlgebra.IsSolvable I → I = ⊥`.
  This expresses the final clause, every solvable Lie ideal is zero.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the node's algebraically-closed clause, rather than a chosen closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, as specialized
  and documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, retaining all algebra points.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSemisimpleGroupScheme`,
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`,
  and `groupSchemeCommutator`, read in full.
- `Sheaf.RepresentationTheory.CharZeroDifferentiationHom`:
  `AlgebraicGeometry.charZero_differentiation_hom`, read with its full signature
  and docstring; its canonical Lie object and bracket are used directly.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic`: `GrpObj.Lie` and its
  additive/global-scalar instances; `Lie.Ring`: the base-field module instance;
  `Lie.Bracket`: `lieEquivTangent`, bracket, LieRing and LieAlgebra instances.
- `Mathlib.Algebra.Lie.Semisimple.Defs`: `LieAlgebra.HasTrivialRadical`;
  `Mathlib.Algebra.Lie.Semisimple.Basic`:
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`.

Plain imports preserve the recorded proof plan: `Lie.Bracket` for
`def-wf-lie-algebra-derivation`; `GroupScheme.Cartier` for
`smooth_of_grpObj_of_charZero`; `GroupNeutralComponentTranslates` for
`GrpObj.finiteTypeGroup_neutralComponent_translates`; `AffineGroupCentreBaseChange`
for `exists_affine_group_centre_baseChange`; `SmoothAmbientNormalityGeometric`
for `isNormalSubgroupScheme_of_geometric_conjugations`.
The proof-only nodes `lem-sfb-central-torus-faithful-weight-blocks` and
`sk-p-comparison` currently have no recorded Lean module, so no import is possible
for those two; their exact role remains in the seven-step proof docstring.
The abstract Lie derived-series definitions are available through the semisimple
Lie import. No proof dependency was added as a hypothesis.

Source and edge checks: read Milne's actual PDF, §22c printed p.476 and
Theorem 22.53 printed p.481. The proof docstring expands its centralizer argument
with the node's scheme-theoretic normality and last-derived-term argument.
Read the current blueprint unit under `literature/blueprint/latest/`.
The trivial group is allowed and has zero Lie algebra; `HasTrivialRadical` accepts
zero-dimensional Lie algebras. No nontriviality or positive dimension is imposed.
A positive-dimensional torus or additive group fails hG, as each is its own
nontrivial smooth connected solvable normal subgroup. Positive characteristic
is excluded exactly as in the node and source. Nonconnected groups are excluded
by hG. The group scheme has its identity section, and connectedness includes
nonemptiness. Kernels used in the proof need not be assumed reduced: Cartier
supplies their smoothness. No replacement by geometric-point groups is made.

Searches (2026-10-24):

- `msearch.py ... leansearch "semisimple algebraic group Lie algebra characteristic zero"`:
  eight hits on abstract semisimple Lie algebras, Killing forms and Geck's
  construction; none is the group-to-tangent-Lie theorem.
- `msearch.py ... leanfinder "The tangent Lie algebra of a connected semisimple
  algebraic group in characteristic zero has no nonzero solvable ideal"`:
  eight hits, including `hasTrivialRadical_iff_no_solvable_ideals`, abstract Lie
  criteria and Geck's construction; none proves the item's statement.
- `msearch.py ... loogle "LieAlgebra.HasTrivialRadical, GrpObj.Lie"`:
  zero hits, with `GrpObj.Lie` unknown to the Mathlib-only search service.
- `msearch.py ... grep "semisimple|HasTrivialRadical" AlgebraicGeometry`: zero hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf`, with
  `IsSemisimple|semisimple|IsSolvable|derivedSeries`, found the reusable
  `GroupScheme.Semisimple` definitions and representation semisimplicity results,
  but no theorem of the item's conclusion. Further searches for
  `semisimple.*Lie|charZero_semisimple|semisimple_group_lie` and the item id
  found no existing item theorem. The chosen full declaration name was searched
  in Mathlib, both project source trees, and `dag/lean_names_upstream.json`:
  no collision. The item-id search in `lean/WeilConjectures` also found no match.

Validation: `scompile.py Q102 lem-sfb-char-zero-semisimple-group-lie <module>`
compiled the sandbox and library-path forms on the server, in 9.3 s and 7.7 s,
with exit code 0 and no diagnostics. Every variable and universe is explicitly
bound, and `autoImplicit` is false. The only postponed proof is the named item
itself. No statement dispute or correction is needed.

## Second reading by Q102

This is a second pass by the same dispatcher-started worker, with the node,
module and definition source reopened; the brief prohibits starting other agents.
The maintainer's independent review is still required.

I checked every binder against the node: Field, IsAlgClosed and CharZero match F;
G is an arbitrary F-scheme with a group object; hG expands to exactly smooth,
connected, affine, finite type and the stated semisimplicity condition. The
solvability recursion uses scheme-theoretic commutator subgroups and terminality,
so it does not silently switch to solvability of rational-point groups. I checked
the canonical Lie object against the full differentiation signature and bracket
source. Finite dimensionality is already a consequence there, not an extra
assumption or an omitted requirement to choose a different Lie object. The final
HasTrivialRadical matches the dependency's specified definition and the node's
explicit solvable-ideal clause. Zero Lie algebra and trivial G are included.

One bookkeeping mismatch was found and repaired before delivery: reuse of
`IsSemisimpleGroupScheme` requires citing its owning landed definition node;
`def-sfb-semisimple-group-scheme` was added to stmt_deps. No mathematical node
text, proof, proof_deps, dependency record, or existing definition was changed.
The declaration signature in lean.statement is copied verbatim from the module,
including its line breaks. The seven proof steps, source places, blueprint tags,
module mode and public visibility were checked. No further mismatch was found.
