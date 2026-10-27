## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleStabilizerPreservingAffineModuli` states the
assigned node in three named theorems, all with proof `sorry`:
`AlgebraicGeometry.exists_etale_stabilizerPreserving_affine_moduli`,
`AlgebraicGeometry.etale_stabilizerPreserving_comp`, and
`AlgebraicGeometry.etale_stabilizerPreserving_baseChange`. It defines nothing.
There is no statement correction, disputed assertion, new node or dependency repair.

The exact hypothesis and clause correspondence is:

- The field is `(k : Type u) [Field k]`; all schemes and tests are over
  `Spec (.of k)`. No characteristic, Noetherian, reduced, finite-type, or DM assumption
  is added.
- The chosen affine finite locally free groupoid is encoded by the coordinate algebras
  `E`, `L`, the `k`-algebra maps `σ`, `τ`, the specified `e`, `i`, `c`, and the two
  `IsFiniteLocallyFree` instances. `SchemeGroupoidQuotientPresentation ... F a` is
  the existing definition of `[U/R]`: the original scheme groupoid laws, fppf descent,
  local lifts of objects, and the original arrows and their composition. Thus this
  states the result for any chosen presentation of the kind the node instructs us to
  choose, and does not assume a new arbitrary quotient or an unrelated equivalence.
  Its locally surjective atlas is the finite flat finitely presented surjective cover
  in the node. Arbitrary such affine covers give these presentations.
- `hF : IsAlgebraicModuliStack F` and `hG : IsAlgebraicModuliStack G` render the two
  algebraic stacks, including their smooth atlases and algebraic-space diagonals.
- `affineGroupoidModuliBase σ τ` is literally `Spec (AlgHom.equalizer σ τ)` with its
  inherited field structure. The binder `f`, with `hf`, characterizes the canonical
  invariant-spectrum morphism by its pullback to the chosen atlas, which is the
  recorded `affineGroupoidModuliAtlasMap σ τ`. This is the same normalization as
  `finiteFlatAffineGroupoid_moduli`; its existence and properties are not added as
  independent hypotheses. The atlas is locally surjective, so this normalization
  determines the morphism into the discrete represented scheme.
- The given map is `h : BasedFunctor G F`.
  `hrep : IsRepresentableByAlgebraicSpaces h` is representability on every scheme
  2-base change. `het : IsEtaleModuliMap h` gives an actual algebraic-space
  presentation with its projection étale on every étale scheme chart.
- `hsep : ModuliSchemeTest @IsProper (moduliRelativeDiagonal h)` is properness of
  the relative diagonal. For a representable étale map this diagonal is a
  representable monomorphism of algebraic spaces, hence representable by schemes;
  thus the existing scheme-test predicate expresses the stated separatedness
  exactly. It is not a properness test on the original map or on source charts.
- `hst` tests bijectivity of the actual induced map on `x ≅ x` for every object
  of every scheme fibre. It includes nonreduced tests and restriction of every
  object. By Yoneda on the automorphism sheaves this is precisely the canonical
  inertia isomorphism specified in the node; it is stronger than testing geometric
  stabilizer points alone, and exactly the node's scheme-theoretic condition.
- The descended scheme and map are existential `M' : Over (Spec (.of k))` and
  `u : M' ⟶ affineGroupoidModuliBase σ τ`; their two clauses are
  `IsSeparated u.left ∧ Etale u.left`.
- The vertical map is `f'`. Its first conjunct is uniform categoricality: for
  every algebraic space `B`, every chartwise flat `b : B → M'`, and every space
  `Y`, precomposition by the actual first projection of `B ×_M' G` is bijective
  on the set of maps into `Y`. All algebraic-space bases and targets are tested,
  not just affine schemes or schemes.
- The next two conjuncts are the recorded
  `IsQuasiCompactAlgebraicModuliMap` and `IsQuasiSeparatedAlgebraicModuliMap`.
  Quasi-compactness is at the full testing size including the site and source
  universes, with independent enlargement parameters `v₃`, `w₃`. The
  quasi-separated predicate tests the actual relative diagonal and actual
  algebraic-space projections.
- The next conjunct quantifies over every algebraic-stack base `Z` mapping to
  `M'` (in the explicitly enlarged testing universes), and asserts
  `IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f'))`. It is the node's
  universal homeomorphism, using the recorded smooth-atlas point topology.
- For every algebraically closed field `Ω` and field-extension homomorphism
  `j : k →+* Ω`, `mapSkeleton.obj` of the actual `moduliFiberMap f'` is
  bijective. The skeleton identifies objects precisely up to isomorphism, so
  this is the geometric-point clause, with no arbitrary point-set bijection.
- `η : f'.comp (discreteModuliMap (yoneda.map u)) ≅ h.comp f` is an isomorphism
  in the category of based functors. It supplies the required square equation
  over the base. The canonical `moduliTwoFiberLift f' h η` retains both
  projections and this very isomorphism. `IsEquivalence` is exactly cartesianness.
- Uniqueness tests any second separated étale uniform categorical cartesian
  square `M'', u', f'', η'`, and asserts `∃! q : M' ≅ M''` such that
  `q.hom ≫ u' = u` and `f'` composed with `q.hom` is 2-isomorphic to `f''`.
  These are the two required compatibilities. Since the lower target is discrete,
  the 2-isomorphism and its coherence with `η,η'` are unique. The canonical
  comparisons with the 2-fibre products are consequently compatible as well.
  The second candidate need not repeat qcqs and point clauses: categoricality
  already proves uniqueness for this larger set of candidates, equivalently
  proving the stated unique-square assertion.
- The second theorem gives all four properties for `h.comp g`, from the same
  four properties of both maps, over the same arbitrary field base. It has no
  finite-affine-cover hypothesis: permanence is the unrestricted clause.
- The third theorem tests every algebraic stack `H` and map `g : H → G`.
  Its four conclusions apply to the actual `moduliTwoFiberFst g h`.
  Its fibre automorphism tests use the actual 2-fibre product, including the
  specified object isomorphism. No representability or separation is required
  of the base-change map `g`.

Dependency declarations read and used (the imported declaration docstrings and full
signatures were inspected):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace` and its
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, and scheme-test interface.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`, through
  the presentation's `groupoid` field.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` (finite, flat, locally finitely presented).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, through
  `SchemeGroupoidQuotientPresentation.stack` and local surjectivity.
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`: `IsAdequateModuliSpace` was
  read as requested; this node references it for stack/sheaf conventions and
  does not assert that its map is adequate or add that as a hypothesis. Its
  imported algebraic-stack and qcqs notions are the ones used here.
- `Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli`:
  `affineGroupoidModuliBase`, `affineGroupoidModuliAtlasMap`, and
  `finiteFlatAffineGroupoid_moduli`. The latter's exact atlas normalization is
  used to specify the chosen `f`; its properties are used in the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Etale`, `.Flat`:
  `IsProper`, `IsSeparated`, `Etale`, `Flat`.
- The five already recorded nodes added to `stmt_deps` expose exactly the
  owning interfaces used in the statement, without changing their records:
  `def-sfb-scheme-groupoid-quotient-presentation` supplies
  `SchemeGroupoidQuotientPresentation`;
  `def-sfb-stack-qcqs-morphism` supplies both algebraic qcqs predicates;
  `def-sfb-moduli-chart-normalization` supplies `IsEtaleModuliMap` and
  `moduliTwoFiberLift` (module `ModuliChartNormalization`);
  `def-sfb-dm-stack-morphism-properties` supplies `ModuliSchemeTest`,
  `moduliRelativeDiagonal`, and the field-object point classes (module
  `DmStackMorphismProperties`; these declarations themselves impose no DM
  hypotheses);
  `def-sfb-stack-point-topological-space` owns `moduliPointTopologicalSpace`,
  the smooth-atlas topology instance in `StackPointTopologyFlatLfpOpen`.

All proof dependencies with recorded modules are imported; Mathlib-matched proof
nodes are imported through Affine, Separated, UniversallyClosed, QuasiFinite,
Integral, Proper and Gluing. Unstated proof nodes have no module to import and
are named step by step in the theorem docstrings; none is replaced by an axiom.

Edge cases checked before writing: empty atlas and zero invariant ring (no
`Nontrivial E` or `Nontrivial L`); variable rank and nonreduced finite flat
covers; the empty source and empty descended scheme; identity maps and arbitrary
stack base-change maps; non-DM stacks with non-étale inertia; positive
characteristic; non-quasi-compact separated étale maps (the descended `u` is
not assumed quasi-compact); arbitrary size parameters of source and testing
stacks. All coefficient algebras and test fields belong to the fixed scheme
universe `u`, as in the supplied affine-groupoid dependency and size convention;
no smaller independent field-test universe is introduced.

Searches for an existing statement:

- `msearch.py ... leanfinder "Stabilizer preserving separated etale morphisms of
  algebraic stacks descend to etale morphisms of their coarse moduli schemes"`
  returned eight scheme-level hits: étale composition/base-change properties,
  `AlgebraicGeometry.IsEtale` (the search index uses the old name), and the
  category of étale schemes. No stack moduli descent theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsEtale, AlgebraicGeometry.IsSeparated"`
  returned zero hits / unknown old `IsEtale` identifier. The local Mathlib
  source confirms the current class is `Etale` and `IsEtale` is deprecated.
- `msearch.py ... grep "stabilizer|moduli" AlgebraicGeometry` returned only the
  bibliographic Katz--Mazur moduli reference, no relevant declaration.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  stabilizer-preserving terminology, inertia, and affine groupoid moduli found
  `AffineGroupoidEtaleInvariantComparison` (local affine-ring theorem),
  `FiniteFlatAffineGroupoidModuli` (the vertical-map dependency), and
  `AffineStackStabilizerEtaleComparison` (a related theorem, read in full).
  The last assumes `IsDeligneMumfordModuliStack` on both stacks and gives only
  existence of a separated étale cartesian comparison. It does not state the
  algebraic-stack theorem, uniform categorical and qcqs/point conclusions,
  uniqueness or permanence required here, so it is not an existing match.
- The inertia and normalization interfaces were also searched and read, so
  no second definition of étaleness, inertia, quotient, canonical map or
  point topology is introduced. The current blueprint unit and its direct-image
  proof were read from `literature/blueprint/latest/`; the node is a supporting
  Stacks lemma, not the blueprint unit's own statement.

Validation: `scompile.py Q03 lem-sfb-etale-stabilizer-preserving-affine-moduli`
compiled the module in module mode, with explicit universes and `autoImplicit false`,
cleanly in both sandbox and library namespaces. Only the three named theorem
proofs are postponed. The prescribed dry-run and delivery results follow below.

## Second reading by Q03

A second in-thread reading compared the final node copy and module clause by
clause, including the full signatures of the imported stack interfaces. No
independent worker was started: the dispatcher expressly prohibits subagents
and assigns the maintainer the independent review.

This pass checked that algebraic stacks were not narrowed to DM stacks; that
separatedness tests properness of the diagonal rather than properness of source
charts; that stabilizer preservation tests all schemes, not just closed points;
that the invariant map is normalized on its actual atlas; and that the point
map and the cartesian comparison are the actual induced maps. It verified that
uniqueness retains both projections, and that permanence is stated in two
separate theorems over the same field-base setting. The three declarations have
source and full natural-language proof docstrings matching their clauses of the
single owning DAG node. No mathematical mismatch or node fault remains.

## Returned delivery repair: H2

Replaced `lem-sfb-stack-point-topology-flat-lfp-open` in `stmt_deps` with
`def-sfb-stack-point-topological-space`, the recorded `existing: true` owner of
`CategoryTheory.moduliPointTopologicalSpace` in the same imported module. The
statement uses this plain instance implicitly in `IsHomeomorph`; it takes no
`.choose` from `stackPointTopology_flat_lfp_open`. Read the definition node's
statement and Lean record and the instance's full signature and construction.
The Lean file and all other node fields are byte-identical to the returned
delivery; the report's ownership entry is corrected. The retained module SHA256
is `cb8765b707795240ded5dca43426147f170dc0e09034b679b1ade11beb4192f2`.
Current main differs from the retained delivery only in `lean` and `stmt_deps`;
the prescribed delivery wrapper rebases those changes on current main.
