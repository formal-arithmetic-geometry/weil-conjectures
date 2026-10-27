## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SolvableSemisimpleCentralizerConnected`
states `AlgebraicGeometry.solvable_semisimple_centralizer_connected`, with its sole
mathematical proof postponed by `sorry`. No new definition or auxiliary theorem is added.
The source was read directly: Milne, Algebraic Groups (2017), printed pp.338–339,
Lemma 16.39 and Theorem 16.40. The latest blueprint direct-image proof (3) was also read;
this is an inherited algebraic-group prerequisite, not the unit's statement.

Hypotheses and conclusion, clause by clause:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A group scheme over k: `G : Over (Spec (.of k))` and `[GrpObj G]`.
- Affine: `[IsAffine G.left]`.
- Finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Smooth and connected: `[Smooth G.hom] [ConnectedSpace G.left]`.
- Solvable in the successive scheme-theoretic derived-subgroup sense:
  `hsolv : IsSolvableGroupScheme G`. This is the existing recursive derived-length
  definition, not solvability of the abstract rational-point group.
- The specified rational point: `s : StandardGroupSchemes.affine k k ⟶ G`.
- Semisimplicity in every finite-dimensional algebraic representation:
  `hs : IsSemisimpleGroupSchemePoint G s`. The existing predicate tests every finite
  matrix index type and every algebraic homomorphism to GL, including dimension zero.
- The centralizer is exactly `equalizer (𝟙 G * c) (c * 𝟙 G)` in schemes over k,
  where the displayed expression `c = Over.homMk G.hom … ≫ s` is the constant
  morphism with value s. Pointwise multiplication of morphisms into a group object
  makes these two maps g ↦ gs and g ↦ sg. No arbitrary representing map is supplied.
  The equalizer universal property on Spec A gives precisely gs_A = s_Ag for every
  commutative k-algebra, with no reducedness assumption. Its inclusion is closed
  because G is affine and therefore separated, so its diagonal is closed; the
  equalizer is the pullback of that diagonal. This is an explanation of the object,
  not an additional conclusion or hypothesis.
- Conclusion: `ConnectedSpace (equalizer … …).left`. This includes nonemptiness,
  exactly as the connected-scheme dependency requires.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, and its group law on
  morphisms; `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (available through public imports).
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact;
  `Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion;
  `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback. The centralizer's closed
  subscheme is expressed directly with Mathlib's `Limits.equalizer`
  (Mathlib.CategoryTheory.Limits.Shapes.Equalizers).
- `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: derived length zero is terminality;
  the successor is the smallest closed subgroup containing the commutator morphism.
- `IsSemisimpleGroupSchemePoint`, Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint;
  `StandardGroupSchemes.affine`, Sheaf.AlgebraicGeometry.StandardGroupSchemes.
  The two corresponding already-landed definition nodes were added to stmt_deps,
  as expressly allowed by brief-stage2 §5. No existing definition was copied.

The already-stated proof dependencies are imported privately:
`exists_smooth_connected_derived_subgroup` from SmoothConnectedDerivedSubgroup,
`isNormalSubgroupScheme_of_geometric_conjugations` from SmoothAmbientNormalityGeometric,
`affine_normal_quotient_geometry` from AffineNormalQuotientGeometry, and
`affineGroupHom_faithfullyFlat_iff_surjective_points` from AffineHomRationalPoints.
Their full signatures and docstrings were read. The remaining five proof nodes have
no recorded Lean declaration in the read clone and are not needed to type the
statement; their identifiers and exact role remain in the eight-step proof docstring.

Edge cases checked before stating: trivial G (derived length zero), commutative G,
s = identity, characteristic p, empty matrix index types, zero and nonreduced test
algebras. In the first three cases the centralizer is the whole connected G. The
identity point lies in every centralizer, so nonemptiness is correct. No characteristic
restriction occurs. The field, schemes, and representation indices use the existing
shared universe u; a larger finite-dimensional vector space can be represented by
a finite index type in u, so none is omitted. The scheme equalizer retains nilpotents.
There is no STATEMENT-DISPUTED issue and no statement correction.

Searches for an existing theorem:

- msearch.py leanfinder: “Centralizer of a semisimple element in a smooth connected
  solvable affine algebraic group is connected”: 8 hits, including
  LieAlgebra.exists_isCartanSubalgebra_engel and Module.End.IsSemisimple.of_mem_adjoin_pair;
  read the returned signatures, none concern this scheme-theoretic assertion.
- msearch.py loogle: `"centralizer", "connected"`: 0 hits.
- msearch.py grep: `semisimple|centralizer|solvable` in AlgebraicGeometry: 0 hits.
- rg in lean/WeilConjectures and lean/Sheaf for semisimple, centralizer, IsSolvable,
  derivedSubgroup, equalizer, and the item's exact blueprint id: no existing theorem;
  found and reused the two landed definition modules above. Other centralizer
  theorems concern tori, reductive groups, or matrix Lie algebras.
- The whole-DAG definition search found def-sfb-semisimple-group-scheme and
  def-sfb-semisimple-group-scheme-point, whose full statements and records were read.

Validation uses scompile.py only, then deliver2.py --no-push and deliver2.py.

## Second reading by Q31

I reopened the node and module for a separate clause-by-clause self-check; the dispatch
brief forbids starting another agent, and the maintainer supplies independent review.
Field/algebraic closure, affine finite type, smoothness, connectedness, derived-series
solvability, rational s, and all-representations semisimplicity match the listed binders.
The order in the two equalizer arrows is gs versus sg, because multiplication is the
group-object law on G ⟶ G. The constant arrow composes the structural map with s;
its compatibility proof only verifies that the structural map of Spec k is identity.
ConnectedSpace is applied to the underlying scheme of that exact equalizer. No
reduced centralizer or rational-point topology has replaced it. No extra smoothness
or finite type of the centralizer was assumed. The existing semisimple-point and
derived-series nodes were added to the statement dependencies after this reading.
All eight proof steps of the node are retained in the docstring. The only elaboration
repair concerns the structural compatibility of the canonical constant arrow.
