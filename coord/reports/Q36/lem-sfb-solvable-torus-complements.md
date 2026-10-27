## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SolvableTorusComplements` states
`AlgebraicGeometry.solvable_torus_complements`, with its whole proof `sorry`.
It defines no objects and postpones no unnamed proofs. The node's statement is unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ground field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The groups over F and all homomorphisms are `Grp (Over (Spec (.of F)))` and its
  categorical morphisms. These carry `GrpObj` on their underlying F-schemes.
- Affine and finite type for each of H, U, D and T are respectively `hH`, `hU`,
  `hD`, `hT : SolvableGroupStructure.IsAlgebraic ...`. This predicate is precisely
  `IsAffine ... ∧ LocallyOfFiniteType ... ∧ QuasiCompact ...`.
- H smooth and connected are `[Smooth H.X.hom] [ConnectedSpace H.X.left]`.
- Its successive scheme-theoretic commutator subgroups eventually become trivial:
  `hsolv : IsSolvableGroupScheme H.X`. This recursively uses the smallest closed
  subgroup through which the commutator morphism factors; termination is terminality
  over Spec F. It does not replace the hypothesis by solvability of F-valued points.
- U is included by the specified group homomorphism `iU : U ⟶ H`.
  `[IsClosedSubgroupScheme iU.hom.hom]` gives the closed subgroup, and
  `[IsNormalSubgroupScheme iU.hom.hom]` gives normality on all F-algebras.
- U connected is `[ConnectedSpace U.X.left]`. Its smoothness and unipotence are
  together `hunip : SolvableGroupStructure.IsUnipotent U`: its first conjunct is
  `Smooth U.X.hom`, followed by a faithful closed matrix representation and the
  condition `(matrix - 1)^N = 0` with `0 < N`, over every algebraically closed
  extension field. Thus smoothness is present without a second redundant binder.
- The actual quotient map is `q : H ⟶ D`. The condition
  `hquot : IsFppfGroupQuotient iU q` retains the scheme-theoretic kernel square,
  local surjectivity in the fppf topology, representable sheaf condition, canonical
  torsor coordinates, and the coset-presheaf sheafification universal property.
  On affine tests this is exactly the node's sheafification of A ↦ H(A)/U(A).
  Big-site formulation and affine-algebra formulation agree by affine fppf refinement;
  it does not substitute a quotient of F-points or an unspecified quotient map.
- D is a torus by `htorus : MultiplicativeType.IsTorus D`. Over the algebraically
  closed ground field this existing geometric torus predicate is equivalent to
  being a product of G_m over F: an algebraic closure of F is F-isomorphic to F.
  The recorded `splitTorus` uses the standard Laurent-polynomial G_m, with A-points
  Aˣ, and includes rank zero as the empty product.
- An arbitrary maximal torus is `(T ...) (iT : T ⟶ H)` with
  `hmax : ReductiveTorusCentralizer.IsMaximalTorus iT`. The predicate includes
  closedness, the torus condition, and maximality: every factorization into a
  larger closed torus is an isomorphism, so there is no strict torus overgroup.
- The conclusion `IsIso (iT ≫ q)` says the restriction of this very quotient map
  to this very torus is an isomorphism in group schemes over F. It is stronger than
  a bijection of rational points and is exactly the requested conclusion.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` / `.AlgebraicClosure`: `IsAlgClosed`,
  `AlgebraicClosure` (through the existing torus construction).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp` and group homomorphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme` and their `IsSubgroupScheme` parent.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (includes nonemptiness).
- The morphism-conventions dependency is a convention-only record: finite type
  is its named locally-finite-type plus quasi-compact convention inside `IsAlgebraic`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `groupSchemeCommutator`,
  `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`, `IsSolvableGroupScheme`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsUnipotent`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `IsTorus`, `splitTorus`, `baseChange`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`: `IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`; this same module also supplies the already stated proof
  dependency `affine_normal_quotient_geometry`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization` is a plain proof
  import for `algebraicGroup_homomorphism_factorization`.

The five extra statement dependencies are already landed definition nodes, not new
nodes or repairs. They expose notions the original statement spells out inline:
`def-sfb-semisimple-group-scheme`, `def-sfb-solvable-group-structure`,
`def-sfb-tori-multiplicative-type`, `def-sfb-reductive-torus-centralizer-terminology`,
`def-sfb-fppf-group-quotient-presentation`. Their source declarations and full docstrings
were read. Other proof dependencies currently lack a usable recorded module, so there
is no import to add for them; their five-step argument is retained in the theorem docstring.

Source check: read Milne's actual PDF at printed pp.332--336, Theorems 16.26(a),
16.27(b), and 16.33(d). The last proof explicitly identifies the restriction of the
quotient map with an isomorphism from the maximal torus. The specified U is identified
with the triangular unipotent kernel as in the node's proof, before invoking maximality.
No source-based statement correction is needed.

Edge cases checked before writing: the trivial group and rank-zero tori are included;
U = 1 gives the torus case; D = 1 gives the unipotent case with trivial maximal torus;
H = 1 is allowed. Empty schemes are excluded by the group identity and by connectedness,
as required, not accidentally by a size binder. No characteristic-zero hypothesis or
reducedness restriction on test algebras is imposed. Every universe and variable is
explicitly bound, and `autoImplicit` is false. The common universe u covers affine
coordinate algebras and algebraic closures of F; no lower independent test universe
makes a quantifier vacuous. The conclusion is in `Grp`, retaining the group law and base.

Searches performed on 2026-10-24:

- `msearch.py ... leanfinder "Maximal tori in a smooth connected solvable algebraic
  group map isomorphically to its torus quotient by a connected unipotent subgroup"`:
  8 results, concerning Galois-category lifts, Cartan subalgebras, abstract quotient
  groups, and number-field units; no group-scheme theorem match.
- `msearch.py ... leansearch "Maximal tori of smooth connected solvable affine group
  schemes complement a normal unipotent subgroup with torus quotient"`: 8 results,
  abstract `IsSolvable`, abstract quotient and subgroup solvability, Lie radicals;
  no theorem match.
- `msearch.py ... loogle "IsSolvable, IsTorus, IsUnipotent"`: no hits; Mathlib has no
  identifier `IsTorus`.
- `msearch.py ... grep "IsTorus|MaximalTorus|IsUnipotent|GroupScheme.*[Ss]olvable"`:
  no Mathlib hits.
- `rg` in `lean/WeilConjectures` for the group-scheme notions and
  `grep -rn "lem-sfb-solvable-torus-complements" .../lean/WeilConjectures` found
  no exact theorem; upstream group-scheme basic and GL modules provide the reused
  group and faithful-matrix interfaces, not this complement theorem.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for solvability, tori, unipotence and
  fppf quotients located the definitions listed above. In particular the Semisimple
  module supplies the exact derived-series predicate; the subnormal-series predicate
  in SolvableGroupStructure is not used in place of it.
- Searches in `dag/nodes` found the five existing definition nodes named above;
  `dag/lean_names_upstream.json` has no matching complement declaration.
- `rg "solvable_torus_complements" lean/Sheaf lean/WeilConjectures`: no collision.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q36

A separate rereading pass by this worker opened the unchanged node, the final module,
and the definitions used by every binder. No additional agent was started, as the
brief prohibits it; independent review remains the maintainer's delivery review.
The pass checked F, the four affine finite-type groups, H smooth/connected, exact
scheme-theoretic derived-series solvability, the closed normal inclusion U, U's
smoothness inside `IsUnipotent`, U connected, the specified fppf quotient q, the torus
condition on D, and arbitrary maximal T. Each matches the corresponding binder
listed above. In particular `IsMaximalTorus` includes its closedness and torus clauses,
and the conclusion is `IsIso (iT ≫ q)` rather than existence of an unrelated isomorphism.
The exact derived-series predicate was selected after finding that published definition;
no statement clause was weakened or strengthened. Rank zero and positive characteristic
remain admitted. There are no new definition nodes or dependency-module changes.
