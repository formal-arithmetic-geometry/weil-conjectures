## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NeutralTorusCentralizerCartanStructure`
states `AlgebraicGeometry.neutral_torus_centralizer_cartan_structure`. Its only theorem
has proof `sorry`. There are no new definitions and no dependency-interface repairs.
The node's statement and proof are unchanged. Six already landed definition nodes
are added to `stmt_deps` to cite the existing terminology actually used.

Source read: Milne, Algebraic Groups (2017), printed p.341 (Theorem 16.47 and
Corollary 16.48), p.360 (Proposition 17.28 and proof), and p.362 (Theorem 17.33(a)
and proof). The statement does not use Theorem 17.38 or assert connectedness of the
full centralizer. The current blueprint and unit record were consulted for context;
this is an auxiliary Milne prerequisite, not the unit's own statement.

Clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The group schemes are bundled `Grp (Over (Spec (.of k)))`, so all displayed
  morphisms between them preserve the group law. Affineness and finite type of G
  are the three instances `IsAffine G.X.left`, `LocallyOfFiniteType G.X.hom`, and
  `QuasiCompact G.X.hom`. Smoothness and connectedness are their explicit instances.
- The maximal closed torus inclusion is `iT` with
  `ReductiveTorusCentralizer.IsMaximalTorus iT`. This predicate includes closedness,
  the torus condition and maximality under every larger closed torus inclusion.
  Over algebraically closed k the recorded geometric-torus definition is equivalent
  to being a split torus over k. Rank zero is included.
- Representation of the centralizer is the existential closed subgroup `iF : F ⟶ G`
  with, for every commutative k-algebra A, its image set equal to
  `ReductiveTorusCentralizer.centralizerPoints iT A`. That existing definition tests
  commutation with all T(B)-points for every algebra map A → B. It does not only
  test rational points, and does not require algebras to be reduced. Finite type
  witnesses for F bind the instances needed to form its open identity component.
- `C` is identified with that precise open identity component by the group-scheme
  isomorphism `eC : C ≅ Grp.mk (GrpObj.identityComponent F.X)`. The equation involving
  `eC.hom.hom.hom`, `GrpObj.identityComponentι F.X`, and `iF.hom.hom` fixes its inclusion
  in G to be `iC`; thus C is not an unrelated group with an abstract isomorphism.
  Closedness and `IsAlgebraic C` express the statement's global subgroup and
  affine finite-type conventions, without any added input hypotheses.
- C is smooth and connected by `Smooth C.X.hom ∧ ConnectedSpace C.X.left`.
  `IsSolvableGroupScheme C.X` is exactly termination of successive scheme-theoretic
  commutator subgroups, rather than solvability of the abstract rational-point group.
- Containment of the given T is the group-scheme factorization `jT ≫ iC = iT`.
  Its inclusion is automatically closed since its composite is the given closed
  inclusion in G. No pointwise replacement of this containment is made.
- The existential U and jU give a closed affine finite-type subgroup of C, smooth
  and connected, with `SolvableGroupStructure.IsUnipotent U`. That predicate gives
  an actual faithful closed finite-dimensional matrix representation and unipotence
  at every geometric point with a positive nilpotence exponent.
- `e : U ⊗ T ≅ C` is an isomorphism in the category of group objects: its tensor
  here is the cartesian direct product group scheme. The equation for its underlying
  map is `(fst ... ≫ jU.hom.hom) * (snd ... ≫ jT.hom.hom)`. This forces e to be the
  multiplication map specified by the node, rather than any product isomorphism.
- For each closed torus inclusion `jS : S ⟶ C`, the existential `f : S ⟶ T`
  with `f ≫ jT = jS` is containment as subgroup schemes.
- For each `s : StandardGroupSchemes.affine k k ⟶ G.X`, the predicate
  `IsSemisimpleGroupSchemePoint G.X s` quantifies over every finite-dimensional
  algebraic representation. Membership in the image of C(k) implies membership
  in the image of the original T(k) inclusion. This uses semisimplicity in G,
  not only in C or a single selected representation.
- `Finite (RankOneRoots.Weyl iC)` is finiteness of the actual rational normalizer
  quotient. Despite its name, this existing definition takes any group-scheme map;
  it does not require its source to be a torus. `RankOneRoots.normalizer iC` tests
  preservation of the image subgroup after every commutative k-algebra extension.
  Its extra terminal-test factor is redundant with the test A = k, since both
  terminal test schemes are canonically Spec k. Every C(k)-point normalizes every
  C(A) by inner conjugation; hence `torusInNormalizer iC`, defined as the image
  subgroup intersected with the normalizer, is precisely C(k) inside N. The
  quotient therefore is N/C(k), not a quotient by a smaller denominator. This
  normal denominator has identical left and right coset sets (and inversion also
  gives a bijection), so the node's right-coset convention is respected.

Dependency declarations used, read in their source modules:

- `Field` and `IsAlgClosed`, Mathlib.Algebra.Field.Defs and
  Mathlib.FieldTheory.IsAlgClosed.Basic (field and closure nodes).
- `CategoryTheory.GrpObj`, `Grp`, and their homomorphisms,
  Mathlib.CategoryTheory.Monoidal.Grp; specialization to `Over (Spec (.of k))`.
- `IsSubgroupScheme`, `IsClosedSubgroupScheme`, and `IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `LocallyOfFiniteType`, `QuasiCompact`, and `Smooth`, Mathlib's corresponding
  AlgebraicGeometry.Morphisms modules; `ConnectedSpace`, Topology.Connected.Basic.
- `StandardGroupSchemes.affine`, `map`, and `multiplicative`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes (def-sc-gm-ga).
- `GrpObj.identityComponent`, `identityComponentι`, and their group structure,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic;
  `GrpObj.finiteTypeGroup_neutralComponent_translates`,
  Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates.
- `ReductiveTorusCentralizer.IsMaximalTorus` and `centralizerPoints`,
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology.
- `MultiplicativeType.IsTorus` and `splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType.
- `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure.
- `IsSolvableGroupScheme` and `GroupSchemeDerivedLength`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.
- `IsSemisimpleGroupSchemePoint`, Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint.
- `RankOneRoots.normalizer`, `pointImage`, `torusInNormalizer`, and `Weyl`,
  Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces.

All recorded proof-dependency modules available are imported, including the closed
factorization locus, torus-fixed smoothness, central-maximal-torus nilpotence,
perfect solvable structure, affine normal quotient, faithful weight blocks,
G_m weight basis, locally algebraic identity component, geometric reducedness,
and Nullstellensatz modules. Mathlib supplies affine separatedness, smooth open
restriction, and open-immersion factorization imports. The following proof nodes
have no recorded declaration yet and therefore no module to import:
`lem-sfb-solvable-torus-complements`,
`lem-sfb-geometric-unipotence-unitriangular-embedding`,
`lem-sfb-diagonalizable-to-unipotent-trivial`,
`lem-sfb-rational-representation-unipotent-point`,
`lem-sfb-multiplicative-jordan-linear-compatibility`, and
`lem-sfb-connected-action-torus-rigidity`. None is needed to elaborate this statement;
they remain the named steps of its complete proof docstring.

Edge cases checked: trivial G and rank-zero T allow trivial U and C; for a torus G
one obtains U trivial and C = T = G; for a connected unipotent G the maximal torus
has rank zero, C = G and its normalizer quotient is trivial. No characteristic
restriction is imposed, no smoothness of intermediate derived groups is assumed,
and no nonempty matrix-index hypothesis drops the dimension-zero representation.
Empty schemes cannot be group schemes over a field because of the identity section.
Test-algebra universes are the same u as the schemes and base, as in the recorded
centralizer and normalizer definitions; they are not a smaller independent universe.
There are no local notations or instances or implicitly introduced variables.

Searches performed on 2026-10-24:

- msearch.py leanfinder: "The neutral centralizer of a maximal torus is a direct
  product of a unipotent group and the torus with finite normalizer quotient".
  Eight hits: Sylow normalizer results, upper central series, and Lie Cartan lemmas;
  none is this algebraic-group statement.
- msearch.py loogle: `"centralizer", "torus"`: OK, zero hits.
- msearch.py grep: `torus.*centralizer|centralizer.*torus`: OK, zero Mathlib hits.
- msearch.py leansearch: "Identity component of a maximal torus centralizer is a
  product of a unipotent group and the torus": eight hits, abstract subgroup and
  topological connected-component definitions, no scheme statement.
- rg over lean/WeilConjectures and lean/Sheaf for centralizers, maximal tori,
  unipotence, solvability and semisimple points: found the shared terminology above,
  but no theorem with this statement. The node-id search in WeilConjectures has no
  hit; Sheaf only cites the node in BorelConjugationCover's proof docstring.
- rg of dag/lean_names_upstream.json, Mathlib, WeilConjectures, and Sheaf for
  `neutral_torus_centralizer_cartan_structure`: no existing declaration.

No statement dispute or correction was needed. The required server scompile.py
completed both sandbox and target-module compilations, with no warnings or errors.

## Second reading by Q111

This is a separate self-review pass; no other agent was started, as the dispatch
brief forbids that. I reopened the node and final module and checked every clause
against the correspondences above. Particular checks were the algebra-extension
quantifier in centralizerPoints, the embedding-compatible identity-component
isomorphism, scheme-theoretic derived solvability, multiplication rather than an
unspecified product equivalence, semisimplicity in the ambient G, and the precise
normalizer denominator. The generic RankOneRoots.Weyl interface applies to C as
well as to tori; its defining normalizer and denominator were read in full.
No mathematical mismatch was found. A surplus closing parenthesis in the initial
draft was removed before the successful compile. The maintainer's independent
statement review remains the independent reading requested in the dispatch brief.
