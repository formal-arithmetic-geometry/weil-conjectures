## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ParabolicSimpleRootExhaustion`
states `AlgebraicGeometry.parabolic_simple_root_exhaustion` with its whole proof
`sorry`. It defines no new notion. The node is unchanged except for `lean`.

I read the node's statement, source and seven proof steps; every statement dependency's
statement and Lean/mathlib record; and the actual interfaces and docstrings in the
source files. I read Milne, Algebraic Groups (2017), printed pp.354--356 and
452--454, by `pdftotext` (PDF pages 366--368 and 464--466). They give the Borel
existence, torus conjugacy inside P, reductive-to-semisimple reduction, and the
simple-root classification. There is no statement correction or disputed statement.

Hypotheses and their renderings:

- `F : Type u`, `[Field F]`, `[IsAlgClosed F]` render the arbitrary algebraically
  closed field. The universe `u` is declared explicitly.
- `G T P : Grp (Over (Spec (.of F)))` are group schemes over that same field,
  with actual group laws and group-scheme homomorphisms, not abstract point groups.
- `hG : ReductiveTorusCentralizer.IsReductive G` is the recorded reductive
  predicate used in `lem-sfb-reductive-borel-pair-structure`. Its `IsAlgebraic`
  component gives affineness, locally finite type and quasi-compactness; it also
  includes smoothness and geometric connectedness, and excludes nontrivial smooth
  connected normal unipotent subgroups after algebraic closure. Over algebraically
  closed F this is exactly the node's convention, with no extra restriction.
- `iT`, `hT : ReductiveTorusCentralizer.IsMaximalTorus iT` supply the closed
  maximal torus subgroup. `hsplit : ∃ r : ℕ, Nonempty (T ≅
  MultiplicativeType.splitTorus F r)` says it is split, including rank zero.
- `iP` and `hP : IsClosedSubgroupScheme iP.hom.hom` give the closed subgroup P;
  `hPsmooth` and `hPconnected` give its smoothness and connectedness.
- `jTP` and `hjTP : jTP ≫ iP = iT` express T contained in P, as a factorization
  of subgroup-scheme inclusions.
- `Q : Over (Spec (.of F))` and `q : G.X ⟶ Q` give the represented quotient
  and its canonical projection. `hQproper` is properness; `hQfinite` is locally
  finite type together with quasi-compactness, the recorded finite-type convention.
- `hQsheaf` says the representable presheaf of Q is a sheaf for
  `Scheme.fppfTopology.over (Spec (.of F))`. `hquot` gives an arrow from the
  coequalizer of `yoneda.map (fst G.X P.X)` and right multiplication
  `yoneda.map (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom))`, compatible with q,
  that induces bijections into every Type-u-valued fppf sheaf. This is exactly
  sheafification's universal property. Evaluated on an affine test scheme, the
  coequalizer is G(A)/P(A), the set of right P(A)-cosets; normality is never used.
  Its formulation on all F-schemes agrees with the algebra version in the node:
  affines are a basis, and affine fppf covers refine to flat finitely presented
  affine covers. Quasi-compactness on affine refinements turns locally finite
  presentation into finite presentation. This is the same quotient encoding as
  the published `exists_homogeneous_fppf_quotient` statement.

Conclusions and the root-data objects they use:

- The first conjunct existentially supplies B, `iB`, `jTB` and `jBP` with
  `IsBorelGroupScheme iB.hom.hom`, `jTB ≫ iB = iT` and `jBP ≫ iP = iB`.
  These are exactly Borel existence and both required containments. The Borel
  predicate is maximality among smooth connected solvable closed subgroup
  schemes; its solvability uses the scheme-theoretic derived series.
- The second conjunct quantifies over *every* B, iB, jTB and jBP with those
  properties, so classification is not limited to the Borel constructed first.
- The commutativity witnesses and actions `aG`, `aB`, `aP` expose the actual
  character Hom group's additive structure and torus actions. The next three
  equalities pin the actions to conjugation by iT, jTB and jTP. These are
  presentations of the actions named in the node, not arbitrary representations.
  Such actions are the canonical restrictions of the group conjugation actions.
- The character lattice X is `Additive (T ⟶ Grp.mk
  (StandardGroupSchemes.multiplicative F))`; the cocharacter lattice is its
  actual opposite Hom group. `Φ` is a finite subset of this X; its membership
  equivalence says exactly nonzero character weights of `Lie(G)`.
- `D : RootDatum Φ ... ...`, `D.IsReduced`, `D.root α = α.val`, and the
  character/cocharacter composition-power formula expose precisely the recorded
  root datum, rather than an unrelated root system. `b : D.Base` supplies the
  simple roots and their independence with signed integral expansions. The
  integral independence gives the stated rational independence by localization;
  no requirement that roots span the entire character lattice is imposed.
- `b.IsPos α ↔ weightSpace ... B ... α.val.toMul ≠ ⊥` identifies the positive
  system with the roots occurring in Lie(B). Here `weightSpace` is the recorded
  character-weight submodule of the tangent space, not a differential weight.
- `I : Set Φ` and `I ⊆ (b.support : Set Φ)` are a subset of the simple roots.
  Using indices in Φ is equivalent to using the characters themselves, since
  Φ is a finset of characters and D.root is their subtype inclusion.
- The displayed equality of subsets of Φ renders
  Φ_P = Φ⁺ ∪ (Φ ∩ ZI). Its left side is precisely the nonzero P-weight spaces;
  its right side uses `b.IsPos` and `Submodule.span ℤ (D.root '' I)`.
  An integer submodule's span is exactly the additive subgroup generated by I.
  Intersecting with Φ is implicit in both sides' index type Φ.
- The universally quantified J clause states uniqueness among all subsets of
  the simple roots satisfying the displayed equality.
- The final equality identifies I with simple α having nonzero P-weight space
  at `(-α.val).toMul`, exactly the equivalent formula in the node. The inverse
  character is negation in the additive character lattice.

Recorded dependency declarations used (all are publicly available through the
Borel-pair module except the additional explicit site and colimit imports):

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; only algebraic closedness is needed,
  not a newly chosen algebraic closure.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; the Over specialization is documented
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme`: `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.multiplicative` with
  its `multiplicativeGroup`, `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- `lem-sfb-reductive-borel-pair-structure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`,
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`. Its exact
  actual Hom lattices, ModObj conjugation equalities, RootDatum, Base and
  TorusCharacterTangent.weightSpace interfaces are reused.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.

The available proof-only dependency modules are imported without `public`:
HomogeneousOrbitQuotientGeometry, BorelMaximalTorusConjugacy,
ReductiveRootSubgroupParametrizations and ReductiveRankOneReflections. The
Borel-pair dependency is already public. The other five proof dependencies have
no usable recorded declaration in the local DAG at writing time and are not
imports: solvable-proper-fixed-point, maximal-torus-overgroup-root-generation,
split-rank-one-classification, bruhat-simple-letter-specialization and
root-subsystem-simple-orbits (all with prefix `lem-sfb-`). They are only proof
inputs, so their absence does not obstruct stating this item. The docstring
retains all seven proof steps and their named inputs.

Edge cases checked before writing:

- G=T (including the trivial group): Φ and b.support are empty; I=∅ is the
  unique subset, and both sides of the root equality are empty. The Borel is G.
- P=G: the subset is the entire base, because every negative simple root occurs.
- P=B: the subset is empty, and Φ_P is exactly the positive system.
- A reductive group with positive-dimensional central torus: no spanning of X
  by the roots is required, so it is included.
- Characteristics two and three and arbitrary positive characteristic: there is
  no `CharZero` or characteristic bound. The weight spaces use characters.
- Empty schemes are not inadvertently allowed as P: `ConnectedSpace` includes
  nonemptiness, as in the source. Rank zero is allowed by the natural-number
  split-torus binder. All variables/universes are explicitly bound.

Searches made on 2026-10-24:

- msearch LeanFinder: “Parabolics through a maximal torus have roots the positive
  roots union the root subsystem generated by a unique subset of simple roots”:
  8 hits, including LieSubalgebra.root, abstract RootPairing base and G2 results,
  and characteristic-zero Lie-algebra root-system declarations. None states the
  algebraic-group theorem in arbitrary characteristic.
- msearch Loogle: `"parabolic", "root"`: 0 hits.
- msearch grep: `parabolic|Parabolic`, Mathlib/AlgebraicGeometry: 0 hits.
- msearch LeanSearch: “Every parabolic subgroup containing a maximal torus contains
  a Borel through that torus and is determined by the negative simple roots it
  contains”: 8 hits, involving parabolic 2x2 matrices, Weyl groups, Coxeter
  generators and positivity. None is this statement.
- `rg` of `parabolic|Parabolic|BorelPair|IsReductive|simpleRoot` in the project's
  Sheaf and upstream WeilConjectures algebraic geometry trees located the
  recorded Borel-pair, StandardParabolicLeviCharts and cocharacter modules.
  StandardParabolicLeviCharts constructs parabolics from subsets for semisimple G;
  it does not exhaust all given P for reductive G, so is not an existing match.
- `rg` for `parabolic.*root|root.*parabolic`, the exact item id, and the proposed
  declaration name in WeilConjectures/ found no match; `rg` of Sheaf/ and
  dag/lean_names_upstream.json found no duplicate declaration. The actual
  character tangent weights, maximal tori, reductivity, Borel definition and
  split tori were found and reused. Quotient searches found only existing
  group-quotient predicates requiring a group Q or normality; the direct
  coequalizer/sheafification pattern in HomogeneousOrbitQuotientGeometry and
  StandardParabolicLeviCharts applies to arbitrary P without a new definition.

Validation: `scompile.py ND lem-sfb-parabolic-simple-root-exhaustion <module>`
compiled the actual module cleanly in sandbox and library mode (2.1 s and 2.3 s
for the final signature). No non-sorry warnings, definitions or auxiliary proofs.

## Second reading by ND

This is the author's second reading; the maintainer supplies the independent
review, as required by the dispatch brief. No other agent was started.

I reopened the node and module and matched every binder and conclusion above.
The universal Borel clause follows the existence clause and therefore covers
all allowed Borels. The equality is over the root subtype, so the subsystem
intersection with Φ is retained. Both subset membership in the simple base and
uniqueness within that base are present. The last formula uses the *negative
character* on P and not a negative differential. The quotient is for right
cosets, with no normality assumption. Its sheafification bijection ranges over
all sheaves on the stated site, rather than only represented targets.

On this reading I made the root-datum identification fully explicit by including
reducedness and the composition-power normalization of the pairing, following
the recorded dependency. The compile was repeated after that change and passed.
I also checked that there is no root-span-of-X assumption and no semisimple,
simply connected or characteristic-zero binder. The report and node signature
match the final module. No new definition node, dependency repair or statement
correction is needed.
