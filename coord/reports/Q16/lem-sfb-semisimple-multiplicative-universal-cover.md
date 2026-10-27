## Worker report

The module `Sheaf.AlgebraicGeometry.SemisimpleMultiplicativeUniversalCover` states
`AlgebraicGeometry.exists_semisimple_multiplicative_universalCover`. Its only declaration
is the item's theorem, with the whole proof `sorry`. There are no new definitions,
new nodes, dependency repairs, or corrections of the natural-language statement.
The proof docstring reproduces all six DAG proof steps and their cited nodes.

The statement was checked against Milne, Algebraic Groups (2017), printed pp.387–393
and 400–401: Definitions 18.1, 18.5, 18.7, Theorem 18.25, Remark 18.27,
Lemma 19.14 and Proposition 19.15. The PDF was read directly with pdftotext.
The semisimple specialization is exactly the final sentence of Remark 18.27,
with semisimplicity of the source furnished by Lemma 19.14 and simple connectedness
expressed in the central-isogeny form of Proposition 19.15.

Clause-by-clause correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  No characteristic hypothesis is imposed.
- H is an F-group scheme: `H : Over (Spec (.of F))` with `[GrpObj H]`.
  Its semisimplicity is `hH : IsSemisimpleGroupScheme H`.
- The existing semisimple predicate unfolds into `Smooth G.hom`,
  `ConnectedSpace G.left`, `IsAffine G.left`, `LocallyOfFiniteType G.hom`,
  `QuasiCompact G.hom`, and terminality of every smooth connected solvable
  normal closed subgroup. Its `IsSolvableGroupScheme` means that the
  scheme-theoretic derived series reaches a terminal group in finitely many steps.
  `IsDerivedGroupScheme` specifies the smallest closed subgroup through which
  the actual commutator morphism factors. Thus all explanatory semisimplicity
  and solvability clauses use the already landed definitions without copies.
- Existence of the F-group scheme Htilde is
  `∃ (Htilde : Over (Spec (.of F))) (_ : GrpObj Htilde), ...`.
  Its semisimplicity is the first conjunct `IsSemisimpleGroupScheme Htilde`.
- Simple connectedness is the second conjunct, quantified over every F-group
  scheme H1 with `[GrpObj H1]` and `IsSemisimpleGroupScheme H1`, and every
  `q : H1 ⟶ Htilde` with `[IsMonHom q]`. Its premises are `Surjective q.left`,
  `IsFinite (GrpObj.ker q).hom`, and centrality of that kernel. Its conclusion
  `IsIso q` says q is an isomorphism over F. The inverse of a homomorphism
  that is an isomorphism is automatically a homomorphism.
- The covering homomorphism is `∃ (pi : Htilde ⟶ H) (_ : IsMonHom pi), ...`.
  Faithful flatness is `pi.left.appTop.hom.FaithfullyFlat` on the actual
  contravariant coordinate-ring map. The standard ring-map predicate means
  flat extension of scalars detecting zero modules, as requested.
- Its finite scheme-theoretic kernel is `IsFinite (GrpObj.ker pi).hom`.
  The existing kernel construction is the pullback along the target identity.
  For an affine group over a field this finiteness is precisely finite-dimensional
  coordinate algebra. It does not require a reduced kernel.
- Multiplicative type of this finite kernel is
  `IsFiniteDiagonalizableGroupScheme (GrpObj.ker pi)`. The field is already
  algebraically closed, so no further base change is necessary. This predicate
  gives a finite commutative group M and a natural group isomorphism on every
  test scheme with `Hom(M, Γ(T, O_T)ˣ)`. Milne 12.3 identifies that functor
  with Spec F[M] with the group-like basis comultiplication e_m ↦ e_m ⊗ e_m.
  The finite abelian group is written multiplicatively, an equivalent convention.
- Centrality, both for pi and in the test condition for q, is
  `(x ≫ GrpObj.kerι pi) * g = g * (x ≫ GrpObj.kerι pi)` for every test
  F-scheme T, every kernel T-point x, and every source T-point g. Taking
  affine T includes every scalar-extension algebra, including nonreduced ones;
  the all-scheme version is equivalent by gluing over affine opens.
- The trivial semisimple group is not excluded: no positive rank, nontriviality,
  nonempty finite-character index, or positive dimension premise occurs.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs (def-weil-field).
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic
  (def-weil-algebraic-closure's recorded match explicitly includes this predicate).
- `AlgebraicGeometry.Scheme`, `Spec`, Mathlib.AlgebraicGeometry.Scheme
  (def-pc-scheme and proof dependency def-weil-affine-spectrum).
- `CategoryTheory.GrpObj`, `IsMonHom`, Mathlib.CategoryTheory.Monoidal.Grp / Mon;
  `GrpObj.ker`, `GrpObj.kerι`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, as exposed by
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (def-sc-group-scheme).
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `ConnectedSpace`, Mathlib.Topology.Connected.Basic;
  `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
  These are retained through the existing semisimple predicate.
- `AlgebraicGeometry.IsSemisimpleGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
  (def-sfb-semisimple-group-scheme).
- `AlgebraicGeometry.IsFiniteDiagonalizableGroupScheme`,
  Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
  (def-sfb-finite-diagonalizable-group-scheme).
- `RingHom.FaithfullyFlat`, Mathlib.RingTheory.RingHom.FaithfullyFlat;
  `AlgebraicGeometry.IsFinite`, Mathlib.AlgebraicGeometry.Morphisms.Finite.

The two landed definition nodes for semisimplicity and finite diagonalizability
are appended to stmt_deps under the standing permission to cite already landed
notions. No existing dependency is removed, and all other node fields are unchanged
except `lean`.

The recorded proof modules are imported privately:
StandardGroupSchemes (`StandardGroupSchemes.multiplicative`),
SemisimpleCharactersTrivial (`semisimpleGroupScheme_characters_trivial`),
CharacterPicardIsogenySequence (`characterPicard_isogeny_sequence`),
ConnectedGroupCharactersTorsionFree (`character_eq_one_of_pow_eq_one`),
SemisimpleCentralIsogenyMultiplicative (`semisimpleCentralIsogeny_multiplicative`),
and MultiplicativeIsogenyComposition (`multiplicativeIsogeny_comp`), all under
Sheaf.AlgebraicGeometry. Mathlib.RingTheory.Bialgebra.MonoidAlgebra contains
`AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`, and
Mathlib.AlgebraicGeometry.Morphisms.FlatDescent contains
`descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`.
The proof dependencies lem-sfb-picard-trivial-multiplicative-cover and
lem-sfb-semisimple-isogeny-invariance have no recorded Lean declaration yet;
they are named in the full proof plan but have no module to import.
Neither is needed to TYPE this statement, so no prerequisite statement is duplicated.

Edge cases checked before writing:

- H = 1: its identity is a multiplicative cover, with kernel D(0). A finite smooth
  connected group over an algebraically closed field is trivial, so its universal
  simple-connectedness test gives the expected condition.
- Characteristic p, including p = 2: a kernel such as μ_p is permitted because
  finite diagonalizable is not finite étale or reduced. Centrality is tested
  on all scheme-valued points, not just F-points.
- A nontrivial torus or G_a is not made semisimple accidentally: the group itself
  is a nontrivial smooth connected solvable normal closed subgroup.
- Noncentral isogenies in positive characteristic do not enter the universal
  condition because centrality is an explicit premise; no separability is assumed.
- The universe u is explicitly bound and shared by the field and the category
  of F-schemes. All test schemes in that category are quantified; there is no
  independent smaller test-algebra universe that could make a condition vacuous.

Searches for reuse:

- msearch.py leanfinder: “Every semisimple algebraic group has a simply connected
  semisimple covering by a multiplicative central isogeny”. Eight hits, all Lie
  algebra statements; no algebraic-group covering theorem.
- msearch.py loogle: `"Isogeny", "SimplyConnected"`. Zero hits.
- msearch.py grep: `semisimple.*[Cc]over|[Ss]implyConnected.*[Gg]roup|multiplicativeIsogeny`.
  Three unrelated topological simply connected-space hits, no theorem match.
- rg on lean/WeilConjectures for that pattern and for this item's blueprint id:
  no matching declaration.
- rg on lean/Sheaf for semisimplicity, solvability, diagonalizability and covering
  names found the existing semisimple and finite diagonalizable predicates and
  the proof modules listed above, but no universal-cover theorem.
- The DAG definitions were searched by id and statement content; the two exact
  landed definition nodes above were found and reused.

Validation: scompile.py Q16 compiled the module in both its sandbox context and
its actual library module context cleanly (1.7 s and 1.6 s respectively).
No errors or non-sorry warnings. No statement dispute or node fault was found.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
