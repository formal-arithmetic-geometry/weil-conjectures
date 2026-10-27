## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveNormalSubgroupTorusFiniteness`
states `AlgebraicGeometry.reductive_normal_subgroup_finite_of_torus_intersection_finite`
with its sole proof `sorry`. No definitions or other theorems are introduced. The node
is unchanged except for its `lean` record. No statement correction or dispute is needed.

Clause-by-clause reading:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- H, S, N are actual group schemes over F: `Grp (Over (Spec (.of F)))`; the group
  objects carry their multiplication, inverse and identity, and their morphisms are
  group homomorphisms over F.
- H is reductive affine finite type: `hH : ReductiveTorusCentralizer.IsReductive H`.
  Its definition includes `SolvableGroupStructure.IsAlgebraic H`, whose three conjuncts
  are `IsAffine H.X.left`, `LocallyOfFiniteType H.X.hom`, `QuasiCompact H.X.hom`.
  The remaining clauses give smoothness, geometric connectedness and absence of
  nontrivial connected normal unipotent algebraic subgroups over the algebraic closure.
  Over the algebraically closed F this is the source's reductivity predicate.
- S is a maximal torus included in H: `iS : S ⟶ H` and
  `hS : ReductiveTorusCentralizer.IsMaximalTorus iS`. This definition includes
  closed subgroup, torus, and maximality under any larger torus inclusion.
- S is split: `hSplit : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)`.
  This is an isomorphism of group schemes, including rank zero.
- N is a closed normal subgroup of H: `iN : N ⟶ H`,
  `[IsClosedSubgroupScheme iN.hom.hom]`, `[IsNormalSubgroupScheme iN.hom.hom]`.
  The former includes the closed immersion; the latter says the image on A-points
  is a normal subgroup for every commutative F-algebra A. Its quantifiers use
  `A : Type u`, the universe of F and the schemes, as the recorded interface does.
  Affine test algebras in this universe detect the full closed subscheme condition;
  it is not a condition only on F-valued points.
- The scheme-theoretic intersection is finite over F:
  `hFinite : IsFinite (pullback iN.hom.hom iS.hom.hom).hom`.
  The pullback is in `Over (Spec (.of F))`; `.hom` is its structure morphism to Spec F.
  This retains the intersection scheme structure, not just the intersection of points.
- The conclusion N is finite: `IsFinite N.X.hom`. Mathlib's predicate means affine
  preimages and finite ring maps, hence over a field finite-dimensional coordinates.
  It agrees with the finiteness terminology already recorded on def-sc-group-scheme.
- There is no assumption on smoothness, connectedness or reducedness of N.
  No dimension, characteristic, torus rank or nontriviality restriction was inserted.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraic-closedness
  component of the mathlib_match on def-weil-algebraic-closure.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `CategoryTheory.GrpObj`,
  the group-object interface on def-sc-group-scheme, available through public imports.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `AlgebraicGeometry.IsNormalSubgroupScheme`,
  and the documented finite-group-scheme convention (def-sc-group-scheme-subgroup).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`, used inside the recorded reductivity predicate.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`; its public terminology is
  `ReductiveTorusCentralizer.IsReductive`, `ReductiveTorusCentralizer.IsMaximalTorus`
  from `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`, using
  `SolvableGroupStructure.IsAlgebraic` and `MultiplicativeType.splitTorus` from the
  existing terminology modules. No local definitions replace them.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.

All recorded proof-dependency modules are plain imports (including the Mathlib modules
of the closed-immersion leaves). The currently unstated
`lem-sfb-normal-subgroup-maximal-torus-intersection` has no module to import; its proof
step remains documented. This is only a proof dependency, not a missing statement notion.
The docstring transcribes all six proof steps and their named inputs, including the final
finiteness argument for the original nonreduced N.

Source reading: Milne iAG2017 PDF, printed pp.379--380 (Corollaries 17.84--17.85),
p.441 (Corollary 21.53), p.492 (23.24). The reduced connected normal subgroup argument
supports the node's formulation for arbitrary closed normal subgroup schemes. No external
source or newer statement was substituted.

Edge cases checked before writing:

- H=S a torus: the intersection N ×_H H is N, so the implication is the stated
  tautological special case. No semisimplicity assumption excludes it.
- H trivial and torus rank zero: `splitTorus F 0` is the trivial group, and both
  maps and the pullback remain well-typed. There is no positive-rank binder.
- N trivial or N finite: the theorem permits both; finite subgroup schemes may
  carry nilpotents or multiple components.
- Characteristic p: central μ_p in GL_n is allowed although nonreduced; a Frobenius
  kernel is allowed although not smooth. Pullback and `IsFinite` retain nilpotents.
- Positive-dimensional normal subgroup SL_2 in GL_2: its intersection with the
  diagonal maximal torus has dimension one and fails the hypothesis, as required.
- N=H with H of positive rank likewise fails the finite-intersection hypothesis.
- Empty schemes are not group schemes over a nonempty field base: the unit section
  already excludes them. No new nonempty hypothesis was added.
- All universe and term variables are explicit; `set_option autoImplicit false`.

Searches for an existing statement (msearch.py, group NW, this item):

- LeanFinder: “A closed normal subgroup scheme of a reductive group with finite
  intersection with a maximal torus is finite” returned eight abstract/topological
  group quotient results, no group-scheme theorem.
- Loogle: `"torus", "finite"` returned zero hits.
- Mathlib grep: `reductive|IsMaximalTorus|normalSubgroup` in AlgebraicGeometry returned
  zero hits.
- LeanSearch: “A normal subgroup scheme of a reductive algebraic group intersecting
  a maximal torus in a finite scheme is finite” returned eight results about Artinian
  schemes and abstract groups; none states this theorem. IsArtinianScheme.finite
  concerns finiteness of the point type, not finiteness over F.
- Repository rg: `reductive.*[Ff]inite|[Ff]inite.*[Tt]orus|` followed by this node ID
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found
  only unrelated torus modules and existing terminology, no statement match.
- Targeted rg over the group-scheme sources located the existing reductivity and
  torus predicates and the analogous pullback-finiteness form in
  `central_diagonalizable_derived_intersection_finite`; that theorem concerns a central
  diagonalizable subgroup and the derived group and is not this statement.

Validation: scompile.py compiled the sandbox module and its exact library path cleanly
(2.7 s and 2.6 s respectively), with no reported errors or non-sorry warnings.

## Second reading by NW

I reopened the node and completed module for a separate reading; no second agent was
started, in accordance with the dispatcher's explicit instruction. I checked each binder
against the node: F is algebraically closed; H's reductivity predicate already includes
its affine finite-type hypotheses; iS is maximal and separately split; iN is closed and
normal on all algebra points; hFinite applies to the pullback's map to Spec F; the conclusion
applies to N's structure map. In particular, finiteness is not `Finite N.X.left` or a
finite-set statement about F-points. The implicit class hypotheses concern only iN;
none imposes smoothness, reducedness, connectedness, or finite type independently on N.
All six proof steps are in the theorem docstring. Rank zero, H=S, μ_p and disconnected
finite subgroups remain included. I found no mismatch and made no statement change.
