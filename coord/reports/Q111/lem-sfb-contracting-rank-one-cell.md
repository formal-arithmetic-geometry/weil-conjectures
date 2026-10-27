## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ContractingRankOneCell` states
`AlgebraicGeometry.contracting_rankOne_cell`, with its entire proof `sorry`.
The item statement and proof are unchanged. Its statement dependencies gain the
new contraction-definition node and five landed terminology nodes used directly.
The auxiliary module defines the punctured-line inclusion and the orbit-extension
predicate with real morphism data; it contains no postponed theorem.

Hypothesis-by-hypothesis correspondence:

- Algebraically closed field: `(F : Type u) [Field F] [IsAlgClosed F]`.
- Group schemes: `Grp (Over (Spec (.of F)))`, whose bundled arrows are group
  homomorphisms. `hG : SolvableGroupStructure.IsAlgebraic G` is affine finite type;
  `hGsmooth`, `hGconnected` are precisely smoothness and connectedness.
- Split maximal torus: `iT`, `hT : IsMaximalTorus iT`, `r`, `hsplit` use the
  recorded torus definition and actual finite product of the recorded Gm.
  The commutative-object witnesses make the ordinary character/cocharacter Hom
  groups available; these express commutativity already inherent in a torus/Gm.
- Actual characters: `Additive (RankOneRoots.Character T)`. The finite subset is
  `D : Finset ...`; `hne`, `hnonzero`, `hindep` say nonempty, excludes zero, and
  Z-linear independence of its inclusion. No abstract replacement lattice is used.
- Rank-one subgroups: `J`, inclusions `iJ`, `hJclosed`, `hJred`; `tJ`, `hJT`,
  `hJTcomp` give the same maximal torus and its commuting inclusion diagram.
  `hsplit` splits this torus also in every J. `aJ`, `haJ` pin the adjoint action
  to actual conjugation; `hroots` says its roots are exactly the two signed
  characters. This expresses the split rank-one reductive condition without
  assuming anything about reductivity of G.
- Root groups: `Ua`, `Va`, `jUa`, `jVa`, `hUa`, `hVa` give the recorded unique
  smooth connected closed normalized subgroup with tangent image exactly the
  positive/negative character weight space in J. The recorded root subgroup
  theorem identifies these with the node's root groups; no parametrization or
  extra choice of Ga isomorphism is assumed.
- Generation of G: `hgenerate` says every closed subgroup containing all J has
  the ambient identity factor through its inclusion, exactly smallest generation.
- Mixed scheme commutation: `hmixed` quantifies all test schemes and their
  root-group points; the comparison uses the composites into G.
- Generated U,V: `hUclosed`, `hVclosed`, `hUcontains`, `hVcontains`, `hUmin`,
  `hVmin` express closedness, containment, and the smallest-subgroup universal
  properties using morphisms commuting with inclusions.
- `aG`, `haG` expose conjugation for the normalization conclusion. This is
  prescribed data, not an arbitrary action/hypothesis on G.
- Cocharacter and positive equal weight: `lam : RankOneRoots.Cocharacter T`,
  `n : ℕ`, `hn : 0 < n`, `hpair` identify character composition with the actual
  nth power endomorphism of Gm. Negative lam is `lam⁻¹`, the pointwise inverse
  homomorphism into the commutative torus.
- The normalizer named in the prose setup is not used in any hypothesis or
  conclusion, so it is not given an unused binder; its functor convention is
  already implemented in the recorded rank-one interfaces.

Conclusion clause-by-clause correspondence:

- `Smooth U.X.hom`, `ConnectedSpace U.X.left`, `IsUnipotent U`, and the three
  corresponding V terms give both smooth connected unipotent subgroups.
  `IsUnipotent` is the existing faithful matrix representation predicate,
  testing every algebraically closed extension field and `(matrix - 1)^N = 0`.
- The two `@TorusCharacterTangent.IsStable ... aG ...` clauses say that T
  normalizes U,V scheme-theoretically under the specified conjugation action.
- The explicit morphism out of `(V.X ⊗ T.X) ⊗ U.X` is multiplication vtu.
  `IsOpenImmersion ... .left` and `DenseRange ... .left` are exactly the open
  immersion and dense image, not just a rational-point multiplication result.
- The two point-image equalities with `CocharacterContraction.Contracts`, for
  every W, are equality with U_G(lam) and U_G(-lam) as represented subgroup
  functors. `Contracts` demands an actual extension on A1 × W whose zero-section
  restriction is 1, including for nonreduced test schemes.
- The equality with `ReductiveTorusCentralizer.centralizerPoints (lam ≫ iT) A`
  identifies Z_G(lam) with T on every test algebra. That existing definition
  quantifies every A-algebra extension and all cocharacter-source points.
- Existential `P Q p q tP uP tQ vQ` are the products TU,TV. Their closed
  inclusions commute with the specified factor inclusions; the two multiplication
  `IsIso` clauses identify their underlying schemes with T × U and T × V.
  Smoothness, connectedness, and `IsSolvableGroupScheme` give exactly the three
  claimed properties. This solvability predicate is termination of successive
  scheme-theoretic commutator subgroups, not only rational group solvability.
- `IsPullback tP.hom.hom tQ.hom.hom p.hom.hom q.hom.hom` identifies the
  scheme-theoretic intersection P ∩ Q with the given torus inclusions.

Dependency declarations read and reused:

- Mathlib: `Field`, `IsAlgClosed` (Algebra.Field.Defs and
  FieldTheory.IsAlgClosed.Basic), `CategoryTheory.Grp`, `GrpObj`, `IsCommMonObj`
  (CategoryTheory.Monoidal.Grp); `Smooth`, `LocallyOfFiniteType`, `QuasiCompact`
  (AlgebraicGeometry.Morphisms.Smooth/FiniteType/QuasiCompact), `ConnectedSpace`
  (Topology.Connected.Basic), `LinearIndependent`, `IsPullback`, `DenseRange`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, and bundled homomorphism conventions.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`,
  `multiplicative`, `multiplicativeGroup`, `additive`, `additiveGroup`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`; its actual character-lattice/root conventions.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  `TorusCharacterTangent.reductive_root_subgroup_parametrizations`; the defining
  closed/smooth/connected/stable/tangent-space root-group interface.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `IsMaximalTorus`, `IsReductive`, `centralizerPoints`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: `weightSpace`, `IsStable`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsUnipotent`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSolvableGroupScheme`,
  `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`: `Character`,
  `Cocharacter`, `roots`, `weight`, `adjointMap`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `splitTorus`, `IsTorus`.

All available proof-only modules are imported privately: GmRepresentationWeightBasis,
TransverseSubgroupProductOpen, AffinePointedMapGeneratedSubgroup,
ReductiveRankOneReflections, and upstream Geometrically.Reduced and Nullstellensatz.
The cocharacter-limit, faithful-weight-block, geometrically-reduced-group-smooth,
tangent-generation, opposite-root-SL2, and smooth-unipotent-solvable proof nodes
have no recorded modules and are omitted as proof imports. They are not needed
to type the statement. The docstring retains every proof step and dependency.

Edge cases checked: D is explicitly nonempty, so the zero-root/trivial case is
excluded exactly as in the node. Rank zero cannot support the stated nonzero
independent characters; no separate positive-rank assumption was added. Arbitrary
positive n is retained even when divisible by the characteristic. No characteristic
restriction appears; weights are characters, not their differentials. Nonreduced
algebras/schemes are included in commutation, contraction and centralizer tests.
Zero-section evaluation uses the additive group's actual identity (coordinate zero).
The generated groups are closed subgroups of the finite-type affine G, so no
extra finite-type hypothesis on U,V is necessary. Empty schemes cannot be connected
and group schemes have their identity section. The explicit products are over F.
The source Gauss identity is used only on 1+ab invertible; its exceptional locus is
handled in the proof plan by localization/density, never dropped from the theorem.

Searches made through msearch.py, with receipts in searches.jsonl:
LeanFinder: full rank-one triangular-cell statement (8 unrelated hits);
LeanFinder: `algebraic group cocharacter contracting subgroup triangular open cell`
(8 root-pairing/Lie-algebra hits, no group-scheme theorem);
Loogle: `LinearIndependent, IsOpenImmersion, DenseRange` (unknown unqualified
IsOpenImmersion, zero hits);
grep Mathlib/AlgebraicGeometry: `contracting|cocharacter|triangular.*cell` (zero hits);
LeanSearch: `The contracting subgroup of a cocharacter consists of points whose
conjugation orbit extends to the affine line with value the identity at zero`
(8 unrelated abstract/topological subgroup hits);
LeanFinder: `Contracting subgroup of an algebraic group under conjugation by a
cocharacter, extending to zero with value one` (8 unrelated subgroup hits);
grep Mathlib/AlgebraicGeometry: `contractingPoints|cocharacterLimit|CocharacterLimit`
(zero hits). The same name/concept searches of lean/WeilConjectures and lean/Sheaf
find no existing contraction predicate or triangular-cell declaration.
`blueprint_refs.py search cocharacter` returns zero blueprint nodes; search
`contracting` returns eight unrelated trace-formula blueprint nodes. Searching
DAG node titles finds the unstated cocharacter-limit structure THEOREM, which
introduces and proves representability/structure for the condition, but no existing
DEFINITION node or recorded declaration supplying the orbit-extension predicate.

Preflight required the current new-node key `import_flags`; supplied its empty list.
No statement dispute or correction. Both delivered modules compile cleanly through
scompile.py; the theorem has its expected sorry proof and the definition has none.

## New nodes

`def-sfb-cocharacter-contracting-points` defines the orbit-extension predicate for
an actual cocharacter on all test schemes, with the punctured-line inclusion given
by polynomial substitution into the Laurent ring. Source: Milne, Definition 13.21
and Proposition 13.24, pp.261--262; Section 13d and Theorem 13.33, pp.265--266.
The searches above found no definition node, Mathlib definition, or project
interface for this notion. It is the literal point condition appearing in the
item and the unstated cocharacter-limit structure theorem; it chooses no subgroup
representative and postpones no definition data.

## Second reading by Q111

Reread the node and both final files against the hypothesis/conclusion mapping
above. The fixed action witnesses are pinned to actual conjugation; root groups
are specified in each J, and their composites into G appear in every generation
and commutation condition. Checked the order V,T,U and the sign of the inverse
cocharacter; centralizer equality uses all extension algebras, intersection is a
pullback, and solvability is the recorded derived-series predicate. The helper
uses the additive identity only as the affine-line zero section, with no claim
that the punctured-line inclusion is a group homomorphism. No mismatch remained.
This was a second pass by this worker: the dispatcher explicitly forbids starting
other agents; the maintainer's independent review reads the delivered result.
