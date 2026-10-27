## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleRootSubgroupsGenerate states
AlgebraicGeometry.TorusCharacterTangent.semisimple_rootSubgroups_generate, with its
entire proof postponed by sorry. There are no new definitions or auxiliary theorems.
Read Milne, Algebraic Groups (2017), printed pp.428--430 (Theorem 21.11(c),(f)) and
pp.439--440 (Proposition 21.49(a), its proof and Corollary 21.50), from the local PDF.
The source proves generation by the root groups, including the rank-zero case.

Hypothesis and clause correspondence:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
- G and T are bundled `Grp (Over (Spec (.of F)))` objects; their arrows are actual
  homomorphisms of group schemes. The underlying scheme of G is G.X.left.
- `hG : ReductiveTorusCentralizer.IsReductive G` retains the reductivity assumption.
  The recorded definition includes affine finite type (IsAffine, LocallyOfFiniteType
  and QuasiCompact), smoothness and geometric connectedness, and triviality of every
  smooth connected normal unipotent subgroup after algebraic closure. Its unipotence
  predicate uses a faithful closed linear representation and nilpotence of g-1 on
  geometric points. Over algebraically closed F this is precisely the node's meaning.
- `hsemisimple : IsSemisimpleGroupScheme G.X` uses the already landed definition:
  smooth, connected, affine, finite type and every smooth connected solvable normal
  closed subgroup is terminal. `IsSolvableGroupScheme` is finite scheme-theoretic
  derived length; `IsDerivedGroupScheme` is the smallest closed subgroup through
  which the commutator morphism factors. This is the node's stated solvability,
  without replacing it by pointwise abstract solvability.
- `i : T ⟶ G` and `hT : ReductiveTorusCentralizer.IsMaximalTorus i` give a closed
  torus inclusion maximal under inclusion. `r : ℕ` and `hsplit : Nonempty
  (T ≅ MultiplicativeType.splitTorus F r)` give the specified splitting, with r=0
  permitted. They match the root-parametrization dependency's exact interface.
- `[ModObj T.X G.X]` is the conjugation action, specified rather than assumed
  arbitrary: hconj equates its morphism γ with `(t,g) ↦ i(t) g i(t)⁻¹`.
  This introduces the action that the node describes, without a new group hypothesis.
- The subtype indexing U consists exactly of the group-scheme characters α : T → Gm
  with `α.hom.hom ≠ 1` and `weightSpace T G α ≠ ⊥`. The recorded weightSpace is the
  character eigenspace on actual dual-number tangent vectors, not a weight of the
  differential of α. Thus it remains the actual character in positive characteristic.
- `U` and `j : ∀ α, U α ⟶ G` are the family of root subgroups. The five conjuncts of
  hU are closed subgroup, smoothness, connectedness, stability under T and equality
  of the differential's range with the α-weight space. These are precisely the
  characterization and uniqueness of the root-subgroup dependency, not a newly
  defined predicate. That theorem supplies an isomorphism Ga ≅ U α and uniqueness
  over G for every such root; no choice of parametrization is imposed here.
- `K` and `k : K ⟶ G`, with hK, give an arbitrary closed subgroup scheme. There is
  no smoothness, connectedness, reducedness or normality hypothesis on K.
- `hcontains : ∀ α, ∃ f : U α ⟶ K, f ≫ k = j α` says every root inclusion factors
  through K as a group-scheme morphism. For subgroup inclusions this is equivalent
  to scheme-morphism factorization, since the induced group law makes the factor
  automatically a homomorphism; there is no condition only on field-valued points.
- The conclusion `IsIso k` means equality K=G as closed subgroup schemes, without
  requiring a literal equality between two chosen representatives of a subobject.
- No `Nonempty` or `Finite` assumption is imposed on the root subtype. If Φ is empty,
  U and j are empty families and hcontains is vacuous; the conclusion is unchanged.

Dependency declarations used, after reading their full definitions and docstrings:

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Mathlib.CategoryTheory.Monoidal.Grp: GrpObj and Grp.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsSubgroupScheme,
  IsClosedSubgroupScheme and IsNormalSubgroupScheme.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth.
- Mathlib.Topology.Connected.Basic: ConnectedSpace (includes nonemptiness).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  LocallyOfFiniteType and QuasiCompact, as used by the recorded algebraic predicates.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: multiplicative, additive, affine.
- Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights: weightSpace and IsStable;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential: GrpObj.differential.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology: IsReductive,
  IsMaximalTorus; Sheaf.AlgebraicGeometry.ToriMultiplicativeType: splitTorus.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations:
  reductive_root_subgroup_parametrizations, fixing the interpretation of U and hU.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: IsSemisimpleGroupScheme,
  IsSolvableGroupScheme, GroupSchemeDerivedLength, IsDerivedGroupScheme.

The existing landed definition node def-sfb-semisimple-group-scheme is added to
stmt_deps so the module uses its canonical semisimplicity definition. No statement
correction, new node or dependency repair is necessary. The item's statement, proof
and proof_deps remain unchanged.

Already stated proof dependencies are imported privately:
AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections,
AlgebraicGeometry.MultiplicativeType.multiplicative_character_antiduality and
AlgebraicGeometry.MultiplicativeType.multiplicativeType_largestSubtorus. The subgroup and root-parametrization imports are already public
statement dependencies. The proof-only nodes semisimple-roots-span,
opposite-root-sl2-parametrizations, split-torus-subgroups-diagonalizable and
smooth-subgroup-tangent-generation have no Lean records in the read clone, so there
are no modules to import yet. Their full five-step proof route remains in the docstring.

Edge cases checked: Φ empty and rank r=0 (trivial semisimple G); K=G; the trivial
subgroup in a positive-rank semisimple group (fails hcontains); SL2 and PGL2 in
characteristic 2 (actual character weights, no restriction on coroot primitivity);
nonreduced K and nonreduced test algebras (scheme factorization retained). The same
universe u covers arbitrary F and all of its finite-type affine subgroup schemes.

Searches actually run with msearch.py, Q20 and this item:

- leanfinder: "A closed subgroup scheme of a semisimple algebraic group containing
  every root subgroup is the whole group"; eight hits, including RootPairing.coe_top,
  frattini, MulAction.IwasawaStructure.is_generator and LieAlgebra.cartan_sup_iSup_rootSpace_eq_top.
  None is a group-scheme generation statement.
- loogle: `"root", "generate"`; six nondegeneracy lemmas for RootPairing, no match.
- leansearch: "A semisimple algebraic group scheme is generated by its root subgroups";
  eight hits for Lie algebras, abstract simple groups and adjoining polynomial roots,
  no group-scheme statement.
- grep: `root.*[Gg]enerat|[Gg]enerat.*root`, Mathlib/AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for root generation, IsSemisimple,
  rootSubgroup and IsSolvable: existing semisimplicity and root-parametrization
  interfaces found and reused; no existing theorem for this item. The matching
  occurrence in SemisimplePerfect.lean is a proof-plan citation, not a declaration.
- grep -rn of the item id in lean/WeilConjectures: no hits. The upstream names
  inventory dag/lean_names_upstream.json also has no root-generation match.

Validation: scompile.py compiled this module in both sandbox and library modes with
no diagnostics. Every variable and universe is explicitly bound, autoImplicit is false.
The theorem has only sorry, and the module defines no data.

## Second reading by Q20

I reread the node and the delivered signature in this worker session. This is the
author's self-check; the dispatcher explicitly forbids starting another agent, and
independent review belongs to the maintainer. F, G, T and reductivity match the root
parametrization dependency's exact interface. Semisimplicity reuses the landed
scheme-theoretic definition, including all five ambient finiteness/geometry conditions.
The hconj equality fixes the action, so an arbitrary action cannot change Φ. The root
index is exactly the nontrivial character/nonzero weight condition; hU is exactly the
unique smooth connected closed normalized subgroup with that tangent space. Ga is
not an additional assumption because the dependency proves it for these subgroups.
Every inclusion factors through the same K by hcontains; IsIso of that specific
inclusion is equality of subgroup schemes. No K-smoothness, characteristic condition,
nonempty-root assumption or tangent-space spanning hypothesis was added. The empty
family remains valid. No mismatch or statement dispute was found, and no statement
change was made. Private proof imports correspond exactly to already stated proof
nodes; no new definitions duplicate the existing objects.
