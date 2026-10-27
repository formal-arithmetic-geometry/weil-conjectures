## Worker report

The delivery states `AlgebraicGeometry.exists_splitCharZero_lieGroup_integration` in
`Sheaf.AlgebraicGeometry.GroupScheme.SplitCharZeroLieIntegration`. The only theorem proof is
`sorry`. No definition, instance, axiom, or auxiliary postponed theorem is introduced.
The natural-language statement is unchanged. The node gains only its Lean record and statement
links to six already landed definition nodes supplying the notions actually used.

Source read: Milne, Algebraic Groups (2017), Theorem 22.53, printed p.481, and the construction,
statement and proof of Theorem 23.70(a)--(e), printed pp.507--508. The latter constructs the
split torus from the integral weight grading and specifies diagram (V,Phi,P(Phi)).
The current blueprint unit is the constructible-stability unit; this item is a supporting
lemma, not that unit's own statement. There is no statement correction or disputed assertion.

Hypotheses, clause by clause:

- A finite-dimensional rational Lie algebra is `(g : Type u) [LieRing g] [LieAlgebra ℚ g]
  [FiniteDimensional ℚ g]`. Semisimplicity is `[LieAlgebra.HasTrivialRadical ℚ g]`, exactly
  the no-nonzero-solvable-ideal predicate recorded by def-wf-semisimple-lie-algebra.
- The specified maximal abelian subalgebra is `(H : LieSubalgebra ℚ g) [IsLieAbelian H]`.
  `hmax` says any abelian Lie subalgebra containing H equals H; it does not ask H to be a
  separately supplied Cartan subalgebra.
- `hsplit` says that for every h in H the supremum of the rational eigenspaces of
  `LieAlgebra.ad ℚ g (h : g)` is top. In finite dimension this is diagonalizability over Q.
  No chosen basis or extra root-system hypothesis is imposed.
- `R` is the set Phi, and `hR` defines membership as nonzero ordinary adjoint weight with
  nonzero `LieModule.weightSpace g`. Thus R cannot be an arbitrary subset of the roots.
- `c : R → H` is the given h_alpha; `hc` places it in the linear span of brackets of the
  alpha and negative-alpha spaces and fixes alpha(c alpha)=2. This renders precisely
  the bracket-subspace convention in def-wf-lie-algebra.
- `P : Submodule ℤ (Module.Dual ℚ H)` is fixed by `hP`: every evaluation on c alpha is
  the rational image of an integer. This is the actual specified lattice, not a free
  abstract replacement. Naming its submodule and giving its membership iff adds no
  assumption: the integral-evaluation set is closed under addition and integer scaling.

Conclusions, clause by clause:

- `R.Finite` records the finite root system. The existential G and T are bundled
  group objects in `Over (Spec (.of ℚ))`, with the actual inclusion `i : T ⟶ G` and
  Lie isomorphism `j : g ≃ₗ⁅ℚ⁆ GrpObj.Lie G.X`.
- `IsAffine G.X.left`, `Smooth G.X.hom` and `ConnectedSpace G.X.left` state the
  corresponding three properties. `IsSemisimpleGroupScheme` is applied to the actual
  pullback to `AlgebraicClosure ℚ`. Its definition includes finite type and the absence
  of nontrivial smooth connected solvable normal closed subgroup schemes. Solvability
  there is termination of the scheme-theoretic commutator derived series, not just a
  condition on rational points.
- The next universal clause is geometric simple connectedness: for any semisimple G'
  over that closure and group homomorphism f onto the pulled-back G, surjectivity,
  finite scheme-theoretic kernel, and centrality on every algebra imply `IsIso f`.
  This is the central-isogeny definition in the node; in particular it implies the
  same assertion for central isogenies over Q by faithful scalar-extension descent.
- `IsClosedSubgroupScheme i.hom.hom` makes T a subgroup, and
  `∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus ℚ r)` is the finite-product
  splitness condition, including r=0. `IsMaximalTorus` is imposed on the pulled-back
  inclusion over the algebraic closure, exactly geometric maximality.
- The existential commutativity witnesses give the actual additive Hom lattices
  `Additive (T ⟶ Grp.mk G_m)` and `Additive (Grp.mk G_m ⟶ T)`, not unrelated groups.
  The chosen `aG : ModObj T.X G.X` is fixed by its equation to conjugation through i.
- `jH : H ≃ₗ[ℚ] GrpObj.Lie T.X` with `differential i (jH h) = j h` says exactly that
  j carries H onto Lie(T) within Lie(G).
- `e : Lie(G_m) ≃ₗ[ℚ] ℚ` is fixed by the epsilon coefficient of the Laurent coordinate
  of its actual dual-number tangent point. In that clause `(A := DualNumber ℚ)` is
  explicit to prevent inference of the different product-ring multiplication on the
  underlying pair type. This specifies the standard tangent scalar, including 1.
- `d : X ≃ₗ[ℤ] P` is fixed by `d χ h = e (differential χ (jH h))` for every character
  and h. Therefore it is differentiation, not an arbitrary lattice isomorphism.
- `Module.Finite ℤ` and `Module.Free ℤ` for X and Y render finite-rank free abelian.
  `D : RootDatum R X Y` includes the perfect integer pairing, injective roots and
  coroots, root-coroot evaluation 2, and simultaneous root and dual reflection
  permutation identities. Its pairing is fixed by the equality of actual morphisms
  `eta ≫ χ = (𝟙 G_m) ^ (D.toLinearMap χ eta)`.
- `d (D.root α) = α.1` gives the root correspondence. The next iff specifies all
  roots as exactly the nonzero character weights of the conjugation action on Lie(G).
  The submodule-map equality identifies j(g_alpha) with that exact character space,
  rather than merely comparing its dimension or its differential weight.
- `differential (D.coroot α) (e.symm 1) = jH (c α)` is the asserted coroot differential
  normalization. The following equality identifies every integer root-coroot evaluation
  with the corresponding rational evaluation. It covers all characters, hence in
  particular every root-coroot pair.
- `D.IsReduced` says proportional roots differ only by sign. D's coefficients are Z,
  so the root pairing is crystallographic. The two rational tensor-product span
  equalities express spanning of X_Q and Y_Q; they do not incorrectly require roots
  to span the full weight lattice over Z. `Finite (Subgroup.closure (Set.range
  D.reflection))` is finiteness of the reflection group.
- The final universal clause takes any rational vector space V (independent universe v),
  finite dimensional with the specified Lie action, and any finite basis `b :
  Module.Basis (Fin n) ℚ V`. Such bases exist for every finite-dimensional V, so this
  is a coordinate description of all representations, not a restriction to particular
  spaces. It supplies `r : GeneralLinearGroup.RationalHom G.X (Fin n)` and `IsMonHom r`.
  The equation `b.repr ⁅x,v⁆ = (r.differential (j x)).mulVec (b.repr v)` gives precisely
  the prescribed differential on the same V. The quantified s clause gives equality
  of every other algebraic representation with that differential, not only an isomorphism.
- `W : X → Submodule ℚ V` has finite nonzero support and `DirectSum.IsInternal W`.
  Every `W χ` equals the ordinary simultaneous H-eigenspace for the differentiated
  weight `d χ`. Its membership iff tests the actual r(A)-action against χ(t) for
  every commutative rational algebra A and t in T(A). Linear extension then gives
  the asserted scalar character action on A tensor W χ. The coordinates are those
  of b throughout; neither the vector space nor the integration action is replaced.

Dependency declarations read and used:

- def-wf-lie-algebra: Mathlib.Algebra.Lie.Basic (`LieRing`, `LieAlgebra`, `LieModule`),
  Mathlib.Algebra.Lie.Subalgebra (`LieSubalgebra`), Mathlib.Algebra.Lie.OfAssociative
  (`LieAlgebra.ad`, `LieModule.toEnd`), and Mathlib.Algebra.Lie.Weights.Basic
  (`LieModule.weightSpace`). The Basic docstrings and full class signatures and the
  adjoint/toEnd declarations were read. The bracket subspace uses `Submodule.span`.
- def-wf-semisimple-lie-algebra: Mathlib.Algebra.Lie.Semisimple.Defs
  (`LieAlgebra.HasTrivialRadical`), with the full equivalence
  `hasTrivialRadical_iff_no_solvable_ideals` in Semisimple.Basic read. This deliberately
  uses its recorded predicate, not Mathlib's differently defined `IsSemisimple`.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp (`CategoryTheory.GrpObj`,
  `CategoryTheory.Grp`); WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
  (`IsClosedSubgroupScheme`, `GrpObj.ker` and its inclusion, via the imported interfaces).
- def-wf-algebraic-representations: WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
  .Representation, `AlgebraicGeometry.GeneralLinearGroup.RationalHom.representation`;
  GeneralLinear.Lie, `RationalHom`, `.points`, `.differential`. The recorded
  `standardRepresentation` is the subgroup-of-GL specialization; the node also records
  the general RationalHom interface, which is exactly the one needed here. No repair
  or private copy is necessary.
- def-sfb-semisimple-group-scheme: Sheaf.AlgebraicGeometry.GroupScheme.Semisimple,
  `IsSemisimpleGroupScheme` and its `IsSolvableGroupScheme`/`GroupSchemeDerivedLength`.
- def-sfb-reductive-torus-centralizer-terminology:
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology,
  `ReductiveTorusCentralizer.IsMaximalTorus`.
- def-sfb-tori-multiplicative-type: Sheaf.AlgebraicGeometry.ToriMultiplicativeType,
  `MultiplicativeType.baseChange` and `.splitTorus`.
- def-sfb-torus-character-tangent-weights:
  Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights,
  `TorusCharacterTangent.weightSpace`. Its pointwise definition uses torus Q-points;
  Q-points of a Q-split torus are Zariski dense, so this is the actual algebraic
  character weight space in this setting as well.
- def-sfb-rho-section-module-data: Sheaf.AlgebraicGeometry.RhoSectionModuleData,
  `RhoSection.characterValue` (and its `evaluate`). This existing Laurent-coordinate
  evaluation is reused directly. The draft's duplicate helper was removed.
- def-sc-gm-ga: Sheaf.AlgebraicGeometry.StandardGroupSchemes,
  `StandardGroupSchemes.multiplicative` and `.affine`.
- Canonical tangent and differentials: WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
  .Differential (`GrpObj.differential`, `tangentPoint_differential`), with its
  Lie.Bracket (`lieEquivTangent`, commutator bracket) and Lie.InfPoints interfaces.
  `RootDatum`, `RootPairing.IsReduced`, and `RootPairing.reflection` are Mathlib's.

Proof imports include every currently recorded module of the proof dependencies:
SplitSemisimpleRootDecomposition, RationalHighestWeightModules, ReductiveBorelPairStructure,
MultiplicativeCharacterAntiduality, ReductiveRankOneReflections,
SemisimpleCentralIsogenyMultiplicative, CentralIsogenyBorelRootCompatibility,
BorelMaximalTorusConjugacy, plus Cartier, Lie.Derivation.Killing, LinearAlgebra.Trace,
and AlgebraicGeometry.Sites.Fpqc for the recorded Mathlib/upstream leaves. These remain
plain imports, so they do not expose their proof dependencies to consumers.
The other proof dependencies have no recorded module yet: reduced-rational-root-pairing-base,
neutral-tensor-envelope, split-lie-module-classification, faithful-semisimple-trace-form,
charzero-connected-differential-test, charzero-lie-semisimple-converse,
smooth-subgroup-tangent-generation, affine-group-lie-tangent-calculus,
relative-diagonalizable-character-duality, and diagonalizable-representation-weight-grading.
They are not needed to type this statement; no duplicate statement or proof is supplied.

Edge cases checked before writing and again against the file:

- g=0 implies H=0, R empty and P=0. Use the trivial group and rank-zero split torus;
  X,Y and the root datum have rank zero. All reflection clauses allow an empty index set.
- n=0 and V=0 are permitted: GL of the empty matrix space is the trivial group;
  W has empty nonzero support and the zero internal direct sum.
- A=0 and nonreduced A (in particular dual numbers) are included: there is no
  Nontrivial/field/reducedness hypothesis on a test algebra. Scheme-theoretic kernels
  and centrality are retained.
- The scalar field is exactly Q, so characteristic zero is not an extra assumption.
  g and V have independent explicit universes; finite bases allow spaces of either size.
  Schemes and test algebras use the existing size convention for the field Q.
- Coroot normalization is exactly 2 and the G_m tangent normalization is exactly
  the epsilon coefficient of t, preventing sign or scaling drift.
- Arbitrary finite bases are universally quantified; no faithful or nonzero action,
  simple module, dominant weight, or positive rank is imposed on the integration clause.

Searches for an existing statement/definition:

- msearch.py leansearch: "split semisimple Lie algebra algebraic group integration".
  Eight results, semisimple Lie predicates and their properties; none integrates a Lie algebra.
- msearch.py leanfinder: "A split semisimple rational Lie algebra integrates uniquely to a
  simply connected semisimple algebraic group with full weight lattice". Eight results,
  including trivial radical of the Geck Lie construction and semisimplicity predicates;
  none is a group-scheme integration statement.
- msearch.py loogle: "LieAlgebra.HasTrivialRadical, LieEquiv, RootPairing": zero hits.
- msearch.py grep: `integrat.*[Ll]ie|[Ll]ie.*integrat|[Ss]imply[Cc]onnected`
  in Algebra/Lie: zero hits.
- rg across WeilConjectures/ and Sheaf/ for the node id and integration names: no exact
  declaration. Broader searches for Integration, Semisimple, SplitTorus, Tangent,
  RootDatum, IsMaximalTorus, characterValue located the reusable definitions above.
  A final whole-source name search also found no declaration-name clash.
- Read Mathlib's complete RootPairing structure, RootDatum abbreviation and
  IsRootSystem fields: an integer root datum already packages the perfect pairing,
  normalization and simultaneous reflection formulas; no new root-datum definition.

Validation uses only the prescribed scompile.py wrapper, compiling the one delivered
module as an individual file against the published live library. Parser conflicts with
scoped mu/eta notation were repaired by renaming local binders. No local notation,
local instance, hidden assumption, auto-bound implicit, or data-valued sorry remains.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
