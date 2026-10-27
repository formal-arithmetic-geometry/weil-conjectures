## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.ProperHomogeneousTorusBorelStabilizer
states AlgebraicGeometry.exists_borel_stabilizer_containing_maximal_torus, with one
`sorry` and no new definitions. The mathematical statement and proof plan are unchanged.
Two already-landed definition nodes are added to stmt_deps:
def-sfb-borel-subgroup-scheme and def-sfb-reductive-torus-centralizer-terminology.
Their definitions are reused, rather than copied. No repair note exists for this item.

Source read: Milne, Algebraic Groups (2017), printed pp.354--356 (Theorem 17.10,
the paragraph following Definition 17.12, Theorem 17.16 and its converse proof),
and printed p.374 (proof of Theorem 17.65, the Borel between T and P).
The node's reduced-identity-stabilizer argument extends the usual smooth subgroup
form of Theorem 17.16 without assuming that the full stabilizer is smooth.

Hypotheses and conclusions, clause by clause:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group scheme G is `G : Grp (Over (Spec (.of k)))`. Its affine and finite-type
  conditions are `IsAffine G.X.left`, `LocallyOfFiniteType G.X.hom`, and
  `QuasiCompact G.X.hom`. Its smoothness and connectedness are `Smooth G.X.hom`
  and `ConnectedSpace G.X.left`.
- The k-scheme Y is `Y : Over (Spec (.of k))`. `Smooth Y.hom`, `ConnectedSpace Y.left`, and
  `IsProper Y.hom` give exactly smooth, nonempty connected, proper finite type.
  Properness supplies local finite type and quasi-compactness, so no extra finite-type
  binder is needed. ConnectedSpace explicitly includes nonemptiness.
- The action with its unit and multiplication identities is `[ModObj G.X Y]`.
  Mathlib's action on point morphisms is the `•` appearing in the statement;
  it is composition of the pairing with the actual action morphism.
- Transitivity on Y(k) is `htrans`: for every two maps from the cartesian tensor unit
  (Spec k) into Y, some map into G carries the first to the second.
- T is a group scheme, with group homomorphism `iT : T ⟶ G`.
  `hT : ReductiveTorusCentralizer.IsMaximalTorus iT` includes closed subgroup,
  torus and maximality under closed torus inclusions. Over the algebraically closed
  base its recorded geometric torus notion equals the node's split torus notion.
  The splitTorus construction uses the standard multiplicative group and includes rank zero.
- The rational point y is a morphism from the same unit into Y.
- Scheme-theoretic T-fixedness is `hy`: for every `A : Type u`, `[CommRing A]`,
  `[Algebra k A]`, and point t of T over Spec A, the composite `t ≫ iT.hom.hom`
  acts trivially on `toUnit (StandardGroupSchemes.affine k A) ≫ y`.
- The existential Borel is a bundled group scheme B₀ with `iB : B₀ ⟶ G` and
  `IsBorelGroupScheme iB.hom.hom`. This is a closed smooth connected solvable
  subgroup maximal among such subgroups; its solvability is termination of the
  scheme-theoretic derived series, not merely solvability of rational points.
- Containment of T is `∃ j : T ⟶ B₀, j ≫ iB = iT`, a factorization by a
  group-scheme homomorphism. As the inclusions are closed embeddings, this is
  precisely subgroup containment.
- Scheme-theoretic B₀-fixedness is the final universal clause, identical to hy with
  B₀ and iB in place of T and iT. There is no condition on the full stabilizer.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Mathlib.AlgebraicGeometry.Scheme: Scheme and morphisms; Mathlib.CategoryTheory.Monoidal.Grp:
  GrpObj and Grp, specialized to schemes over Spec k.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsSubgroupScheme,
  IsClosedSubgroupScheme, and IsNormalSubgroupScheme (full definitions read).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth;
  Mathlib.Topology.Connected.Basic: ConnectedSpace (includes Nonempty).
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: affine, multiplicative,
  multiplicativeGroup; Sheaf.AlgebraicGeometry.ToriMultiplicativeType:
  splitTorus and IsTorus; Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  IsAlgebraic, IsTorus, IsSolvable (the last is not substituted for the derived series).
- Sheaf.AlgebraicGeometry.GroupScheme.Borel: IsBorelGroupScheme, using
  IsSolvableGroupScheme and GroupSchemeDerivedLength from
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology: IsMaximalTorus.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper;
  Mathlib.CategoryTheory.Monoidal.Mod: ModObj;
  Mathlib.CategoryTheory.Monoidal.Cartesian.Mod: Hom.smul and Hom.mulAction.

All recorded proof dependencies that currently have modules are plain imports:
BorelConjugationCover, HomogeneousOrbitQuotientGeometry,
LocallyAlgebraicGroupIdentityComponent, geometrically reduced smooth schemes,
IdealSheaf.Subscheme for the nilradical reduction, and BorelMaximalTorusConjugacy.
Their signatures and proof docstrings were read. The two proof dependencies
lem-sfb-solvable-proper-fixed-point and lem-trf-split-lattice-torus-projection
currently have no recorded Lean modules; they supply no statement notion needed here,
so no proof-dependency module is invented for them. The theorem docstring records
all five proof steps and their node references for stage 3.

Edge cases checked: rank-zero T is permitted (splitTorus k 0 is the trivial group);
G trivial and Y = Spec k has the expected trivial Borel; connected Y excludes the
empty scheme as explicitly required; positive characteristic is unrestricted;
nonreduced A, including dual numbers and the zero algebra, are included by CommRing
and Algebra without a reducedness, field, or nontriviality assumption. No smoothness
of the stabilizer is inferred or requested. Field, schemes, and test algebras share
universe u, matching the existing group-scheme interfaces; no smaller independent
test universe is introduced. No node fault or statement dispute was found.

Searches actually run using msearch.py (Q104, this item):

- leanfinder: "A torus fixed point of a proper homogeneous algebraic group space is
  fixed by a Borel subgroup containing that maximal torus". Eight hits, concerning
  abstract fixed subgroups/Iwasawa structures and proper discontinuity; no match.
- leansearch: "For a proper homogeneous variety under a smooth connected affine
  algebraic group every torus fixed point is fixed by a Borel containing the torus".
  Eight hits about abstract fixedPoints and conjugation, no algebraic-group theorem.
- loogle: "IsBorel, IsMaximalTorus". Zero hits and diagnostic "unknown identifier
  'IsBorel'"; this query did not provide a usable declaration.
- grep: "BorelSubgroup|IsMaximalTorus|proper.*homogeneous". Two unrelated graded-ring
  docstring hits, no match.
- rg over lean/WeilConjectures and lean/Sheaf for Borel, maximal torus, actions,
  proper homogeneous spaces and stabilizers found the existing terminology and
  the stated proof dependencies; no existing theorem has this conclusion.
  Searches by the item id in WeilConjectures and for the proposed declaration in
  both libraries, Mathlib and dag/lean_names_upstream.json found no declaration.

Validation: scompile.py compiled the module both as sandbox and library module in
1.7 seconds each, with no errors or unexpected warnings. No local/global build was run.

## Second reading by Q104

I reread the source statement and the completed Lean signature after compiling.
The independent maintainer review is supplied by the delivery workflow; no second
agent was started, as required by the dispatcher brief.

The rereading checked each binder and conclusion above. In particular ConnectedSpace
contains the required nonempty clause, IsProper includes finite type, htrans quantifies
over all rational points rather than just the orbit of a chosen y, and both fixedness
clauses quantify over every commutative algebra rather than just k-points. The existential
j is a group homomorphism commuting with the ambient embeddings. The existing Borel
definition includes closedness, smoothness, connectedness, derived-series solvability,
and maximality. No reductivity of G and no smoothness of the full stabilizer appears.
No mismatch was found and no statement correction was needed. The only metadata change
besides lean is adding the two already-landed definition nodes used in the signature.
