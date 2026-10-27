## Worker report

The module `Sheaf.AlgebraicGeometry.NilpotentUnipotentCentre` states
`AlgebraicGeometry.unipotent_of_nilpotent_of_unipotent_centre`, with `sorry` as its
entire proof. It renders Milne, Algebraic Groups (2017), Lemma 16.46, printed
pp.340–341, using the unitriangular characterization in Theorem 14.5 and
Corollary 14.9, pp.281–282. These source passages were read from the local PDF.
No definition or theorem is proved, and no node statement is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`. The arbitrary explicit universe u
  is shared by schemes and test algebras, as required by the existing group-scheme API.
- The affine finite-type k-group G is `G : Grp (Over (Spec (.of k)))` and
  `hG : IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`.
  Bundled `Grp` supplies the multiplication, identity, inverse and group laws.
- Connectedness is `hconn : ConnectedSpace G.X.left`, including nonemptiness.
- Nilpotence is `hseries`. Its finite length is s; `H : Fin (s+1) → Grp ...`
  lists the terms; `i j : H j ⟶ G` fixes each term inside the same ambient G.
  Every inclusion is a closed normal subgroup by `IsClosedSubgroupScheme` and
  `IsNormalSubgroupScheme`. `IsIso (i 0)` makes H_0 the whole G as a subgroup;
  `Nonempty (H (Fin.last s) ≅ Grp.trivial _)` makes H_s trivial. For each j,
  `l ≫ i j.castSucc = i j.succ` is the inclusion H_(j+1) into H_j.
  For every commutative k-algebra A, every g in G(A), and h in H_j(A), the
  displayed existential z in H_(j+1)(A) gives exactly
  `[g,i_j(h)] = i_(j+1)(z)`. Containment of the generated commutator subgroup
  is equivalent to these containments for its generators, since the target
  is a subgroup. The closed terms are automatically affine and finite type:
  they are closed subschemes of the affine finite-type G. No smoothness,
  connectedness or reducedness of the terms is assumed.
- The centre is a specified `Z : Grp ...` and group homomorphism `iZ : Z ⟶ G`.
  `hiZ` makes it a closed subgroup. `hZ` identifies its image on every A with
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A`, precisely the functor
  represented in `exists_affine_group_centre_baseChange`. This definition tests
  commutation after every k-algebra map A to B and against every point in G(B).
  Such maps are exactly commutative A-algebra extensions with their induced
  k-structure. Thus this is the scheme-theoretic centre including nilpotents.
  Its normality, commutativity, affineness and finite type follow from that
  identification and closedness; they are not extra input choices.
- Unipotence of Z is `hunitriangular`: there is a positive natural number n and
  `r : Z.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k` with
  `IsClosedSubgroupScheme r`. For all commutative k-algebras A and all Z(A)
  points, `GeneralLinearGroup.homMulEquiv` gives the corresponding invertible
  matrix. Its diagonal entries are 1 and its entries at (a,b) for b<a are 0.
  These are exactly the equations of U_n. A closed immersion into GL_n
  satisfying these equations on all algebras factors as a closed immersion
  into their closed subscheme U_n; conversely composition with U_n → GL_n
  gives precisely this condition. No separate choice of a U_n model is needed.
- The conclusion repeats exactly this positive-size closed unitriangular
  representation condition for G itself.
- There is no smoothness, perfectness, characteristic, or algebraic-closedness
  hypothesis. In particular the existing smooth-only
  `SolvableGroupStructure.IsUnipotent` is deliberately not used as a rendering
  of this node's broader definition. The formula is written directly using
  the dependency's existing GL and closed subgroup declarations.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `Grp.trivial`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` gives the recorded
  specialization to group schemes and the full signatures/docstrings of
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`
  (`def-sc-group-scheme`, `def-sc-group-scheme-subgroup`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  together with `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.QuasiCompact`
  (`def-weil-finite-type-morphism`).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, inherited by `IsClosedSubgroupScheme`
  (`def-weil-closed-immersion`).
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` is the module recorded by
  `def-sc-general-linear-group`; it publicly imports and reuses the actual
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`. Their full
  definitions/docstrings and the recorded `specialLinear` declaration were read.
- `Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange`:
  `exists_affine_group_centre_baseChange` supplies the centre's recorded
  interface; the statement uses precisely its universal subfunctor equality,
  with `ReductiveTorusCentralizer.centralizerPoints` and
  `StandardGroupSchemes.affine` from its public imports. The full signatures
  and docstrings of these declarations were read.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`
  (`def-weil-connected-scheme`).

The stated proof dependencies are imported as plain proof imports:
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`,
`Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`.
The centre dependency is already a public statement import. The other proof
nodes currently have no recorded Lean module: unipotence-field-extension,
commutative-multiplicative-part, multiplicative-unipotent-base-algebra-vanishing,
commutative-diagonalizable-unipotent-product, unipotent-to-multiplicative-trivial,
normal-multiplicative-layers-central, unipotent-extension-arbitrary (all with
prefix `lem-sfb-`). Their proofs are not necessary to type this statement;
the complete five-step DAG proof plan, naming every proof dependency, is in
the declaration docstring.

Edge cases checked before writing:

- s=0 is permitted: the sole term is both G and the trivial group; `Fin 0`
  has no successor or commutator conditions. The conclusion allows n=1.
- s=1 makes G commutative by the last commutator condition, so its centre
  is all of G. Repeated terms and non-strict series are permitted.
- The trivial group embeds into U_1; matrix size zero is excluded exactly
  as the node requires, without excluding the trivial group.
- Arbitrary characteristic and imperfect fields remain allowed. Nonreduced
  finite group schemes, e.g. alpha_p, are not excluded by a smoothness condition.
- All algebra-valued point clauses quantify over commutative rings, including
  nonreduced rings and the zero algebra, rather than only geometric fields.
- The centre is tested after further algebra extension; it is not replaced
  by the abstract centre of G(k). The same universe as the coordinate algebra
  suffices to detect the defining equations and closed subfunctors.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A connected nilpotent affine group scheme with
  unipotent centre is unipotent"`: eight hits concerning abstract nilpotent
  groups, including `Group.IsNilpotent`; no group-scheme theorem.
- `msearch.py ... loogle "IsNilpotent, IsUnipotent"`: zero hits;
  `IsUnipotent` is unknown in Mathlib.
- `msearch.py ... grep "Unipotent|[Cc]entral[Ss]eries|Nilpotent"
  AlgebraicGeometry`: thirteen hits about nilpotent ring sections and ideals,
  none about this group-scheme statement.
- `msearch.py ... leansearch "closed central series of affine group schemes
  nilpotent and unitriangular embedding unipotent"`: eight hits including
  `upperCentralSeries`, `IsAscendingCentralSeries`, `Group.IsNilpotent`;
  these describe abstract groups, not closed subgroup schemes.
- `rg` in `lean/WeilConjectures` for the item id, central-series names,
  unitriangular, and `IsUnipotent`: no matching theorem or general definition.
  `dag/lean_names_upstream.json` was searched too.
- `rg` in `lean/Sheaf` found the smooth-only `SolvableGroupStructure.IsUnipotent`
  and existing statements with explicit closed unitriangular embeddings and
  central series, including `NilpotentConnectedCentralSeries`,
  `CentralMaximalTorusNilpotent`, `CharZeroCommutativeUnipotentVectorGroup`,
  and `AdjointKernelCentralQuotientUnipotent`. Those signatures were read;
  none states the present implication. We follow their use of the existing
  GL and subgroup APIs with the conditions spelled out.
- DAG definition searches and `tools/blueprint_refs.py search` for
  `unipotent` and `nilpotent` found no missing independent notion needed for
  this formula. Both notions are already defined explicitly in the item's
  statement, and here are expanded into its existing dependency primitives.

No new nodes, dependency repairs, statement correction or disputed assertion.
The initial server compile passed both sandbox and library contexts in about
2 seconds each; the final signature is recompiled before delivery.

## Second reading by O4

Author's second reading, not an independent review (the dispatcher brief
reserves the independent review to the maintainer and prohibits subagents).
I reopened the node and module and checked the clause correspondence above.
The important distinction found is that the smooth-only existing unipotence
predicate would omit the nonsmooth cases; the delivered formula uses the exact
all-algebra unitriangular equations instead. Closedness and normality of every
series term are explicit, its inclusions refer to the same ambient embeddings,
and the centre equality is the recorded universal centre condition. The first
series inclusion is an isomorphism, and the final group is trivial, including
s=0. The positive-size representation in the conclusion matches exactly the
one in the centre hypothesis. The final adjustment expands affine finite type
into the recorded primitive declarations so that no additional definition node
or change to stmt_deps is needed. No mathematical mismatch remains.
