## Worker report

The module Sheaf.Paper.P1OrderedProjectionScalarSquare states
AlgebraicGeometry.Etale.p1_ordered_projection_scalar_square with a sorry proof.
It states the whole ordered square in the ordinary unbounded small-etale
constant-ring module derived category, on every Dctf input. No definition is
copied and no theorem is proved. The natural-language statement is unchanged.

Hypothesis and clause correspondence:

- The positive characteristic p, prime ell different from p, and field k are
  `(ell p n : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)` and
  `(k : Type u) [Field k] [CharP k p]`. A positive characteristic of a field
  is necessarily prime, so there is no additional assumption on p.
- The unital map of finite commutative rings is `(φ : A →+* B)` with
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`. The shared annihilator
  N=ell^n is expressed by hA and hB. Since ell is prime, ell^n is positive,
  including n=0; neither a nonzero ring nor n>0 is imposed.
- S is a scheme over Spec k. The Over, LocallyOfFiniteType, QuasiCompact and
  IsSeparated instances on its structure map express separated finite type
  over k. P is exactly `ProjectiveLine S` and q is its structure map
  `(ProjectiveLine S ↘ S)`. This construction already supplies the same
  separated finite-type k-structure on P and the geometric k-morphism q;
  no arbitrary P or q is substituted.
- `DerivedCategoryModule A S` and its B analogue are D(S_et,A/B).
  `scalarExtension φ T` is T_T, the actual derived extension adjoint to
  restriction of constant coefficients. It is everywhere defined, so no
  Tor-dimension or flatness assumption on B is present.
- The input `(K : DerivedCategoryModule A S)` has
  `_hK : ProEtale.AdjunctionTransfer.etaleProperty A S K`. The opened
  abbreviation is exactly isBoundedConstructible intersected with
  DerivedCategory.finiteTorAmplitude; it tests tensor against every
  degree-zero module sheaf, rather than merely stalkwise or bounded tests.
- `ordinaryFiniteLine A (ell^n) hA (ProjectiveLine S)` is the degree-zero
  realization of the actual finiteEtaleTateLine. Its shift by `(2 : ℤ)`
  is L_A. The same expression with B is L_B. The existing
  ordinaryFiniteP1Right is exactly q^* followed by tensoring on the right
  with this L, hence G_R; ordinaryFinitePushforward is F_R and its value
  at L_R is H_R.
- `ordinaryFiniteProjection R q L_R K` is precisely sigma, then the
  geometric counit-transpose rightDerivedLowerStarProjectionMap at L_R,K,
  then F_R(sigma), in Lean's left-to-right composition order. It is the
  ordered K-first pi in the node, with the actual geometric adjunction.
- `scalarMate φ q` is beta_q. Its source is F_A followed by T_S, and its
  target is T_P followed by F_B. Its definition uses mateEquiv applied to
  scalarPullbackIso and the two canonical geometric derived adjunctions.
  This is exactly the proper counit-transpose component of the dependency's
  etaleCoefficientMap; for proper q there is no nontrivial open extension.
- The existential e is the existing CoefficientLineComparison for the
  same annihilator N on both sides. It includes a roots map normalized by
  the inclusion into G_m, a sheaf isomorphism normalized on every scalar
  and root generator, and a derived isomorphism equal to the scalar counit
  followed by that sheaf map. With N=M>0 the roots map is the identity.
  Thus e expresses the canonical comparison stipulated by the node, with
  existence asserted rather than assumed as an extra hypothesis. On pure
  tensors its sheaf map is exactly (z tensor a) tensor b -> z tensor φ(a)b.
  The shifted lambda is scalarShiftIso followed by shiftFunctor.mapIso
  e.derivedIso, both in the formula for a_K and for b. The normalized
  components are unique by generators and the derived representative
  equation; the existential does not allow an arbitrary twist map.
- `ExceptionalCoefficients.tensorIso φ S` is exactly m_(K,H_A).
  The P-component at (q_A^*K,L_A), followed by mapIso of Iso.prod of
  scalarPullbackIso.symm and the shifted lambda, is a_K. The rhs tensor
  functor maps beta_q(L_A) followed by F_B(lambda), which is precisely
  1_(T_SK) tensor b. The final ordinaryFiniteProjection B is pi_(B,T_SK).
- Lean `≫` reverses the order of the node's circle notation: the lhs is
  T_S(pi_A) ≫ beta_q(G_AK) ≫ F_B(a_K); the rhs is
  m_(K,H_A) ≫ (1 tensor b) ≫ pi_(B,T_SK). The equality lives in D(S_et,B).
  The same e works for every K. Every component is a natural transformation
  or a functorial tensor operation, so this is the equality of the two
  natural families on the full Dctf subcategory; it has no K-dependent
  choice of a comparison.

Dependency declarations read and used:

- sk-def-sfb-dc-setting: WeilConjectures.SixFunctors.ProEtale.ModuleObject.
  Derived.BoundedConstructible, compactificationOverField and its standing
  Over/finite-type hypotheses. This item only uses the geometric setting;
  it does not use condensed coefficients or compactification choices.
- def-weil-pbc-derived-categories: WeilConjectures.AlgebraicGeometry.
  DerivedCategories and its public Derived.Coefficients import,
  AlgebraicGeometry.Etale.DerivedCategoryModule. These are ordinary
  module-valued etale sheaves, not a newly chosen SheafOfModules category.
- lem-pur-derived-change-of-rings: Sheaf.Algebra.Homology.
  DerivedChangeOfRingsCochainModel, SheafOfModules.
  nonempty_derivedChangeOfRingsCochainModel and its E/T/counit universal
  interface. The concrete existing scalarExtension is used in the square.
- det-sp-et-proet-adjunction-transfer: Sheaf.Paper.
  EtaleProEtaleAdjunctionTransfer,
  AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty.
- lem-asd-finite-etale-twist-line: Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine,
  AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line; its public
  FiniteEtaleTateTwist module supplies the actual root-based coefficient line.
- lem-sp-et-proet-coefficient-compatibility: Sheaf.Paper.
  EtaleProEtaleCoefficientCompatibility, etaleCoefficientMap, whose proper
  factor is AlgebraicGeometry.Etale.scalarMate. The actual beta, without
  requiring its invertibility, is the one used here. Its public
  PurEtaleScalarMateProjection dependency defines scalarPullbackIso by its
  unique K-flat representative normalization and scalarMate by mateEquiv.
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback: Sheaf.Paper.
  RingedTopoiCanonicalTensorPullbackOfUniverses,
  SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback; its full signature allows
  separate site object and morphism universes, and characterizes the tensor
  comparison on K-flat flat-term representatives. No universe is equated.
- def-kun-projection-formula-map: WeilConjectures.SixFunctors.Etale.
  Derived.LowerStarProjection, rightDerivedLowerStarProjectionMap,
  rightDerivedLowerStarProjectionMap_app_app and
  homEquiv_symm_rightDerivedLowerStarProjectionMap. The ordered wrapper
  below uses this very counit-transpose map.
- def-pur-exceptional-coefficient-normalizations: Sheaf.Paper.
  ExceptionalCoefficientMaps, ExceptionalCoefficients.tensorIso,
  siteTensorIso_existsUnique and TensorNormalizationAux, with the ordinary
  balanced scalar representative normalization retained.
- lem-sfb-ringed-derived-monoidal-comparisons: Sheaf.SixFunctors.
  RingedDerivedMonoidalComparisons, CategoryTheory.RingedDerivedComparisons.
  ringedDerivedMonoidalComparisons and its public System data; used for the
  symmetry and composition normalizations in the proof plan.
- Added existing statement dependency def-asd-ordinary-finite-p1-arrows:
  Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows, ordinaryFinitePullback,
  ordinaryFinitePushforward, ordinaryFiniteTensor, ordinaryFiniteProjection,
  ordinaryFiniteLine (public import), ordinaryFiniteP1Right. All are reused.
- Added existing statement dependency def-pur-finite-smooth-coefficient-arrows:
  Sheaf.Paper.FiniteSmoothCoefficientArrows, FiniteSmoothPurity.
  CoefficientLineComparison and scalarShiftIso. Their signatures and all
  normalization fields were read, not inferred from names.
- Proof-only imports include the recorded RingedToposMorphism definition,
  Sheaf.Paper.RingedExchangeTensorCoherence (ringedExchangeTensorCoherence),
  and Mathlib.CategoryTheory.Adjunction.Mates (mateEquiv, the dependency's
  mathlib_match rather than a missing lean record). All other proof
  dependency modules are already public statement imports. No import
  cycle is introduced and no recorded proof dependency is omitted.

Edge cases checked before writing: n=0 forces both rings to be zero rings,
which are allowed; K=0 gives the zero-morphism equality; the empty S gives
its zero sheaf category; A=B with the identity map gives the identical
projection square with canonical scalar identifications; the nonflat
quotient Z/ell^2 -> Z/ell is permitted (no Flat, projective-dimension,
bounded scalar resolution or invertibility of beta hypothesis). Derived
shifts and both symmetries retain their canonical signs. Positive p need
not be explicitly assumed prime since it is a field characteristic.

Searches for an existing exact statement:

- msearch.py leanfinder: 'Scalar extension commutes with the ordered
  projective line projection formula morphism and the balanced shifted
  Tate twist comparison'. Eight results: ModuleCat.extendScalars_assoc*,
  ModuleCat.homEquiv_extendScalarsComp, Proj.pullbackAwayιIso_hom_awayι,
  Abelian.Ext.smul_eq_comp_mk₀. These concern ordinary scalar associators,
  a Proj chart, or Ext, not this derived ordered coefficient/twist square.
- msearch.py loogle: 'rightDerivedLowerStarProjectionMap, scalarMate'.
  Zero hits, unknown identifier rightDerivedLowerStarProjectionMap in Mathlib.
- msearch.py grep: 'scalar.*[Pp]rojection|[Pp]rojection.*scalar' in
  Mathlib/CategoryTheory. Zero hits.
- rg in lean/WeilConjectures for scalar/projection names: pro-etale
  FiniteCoefficient/Derived/ScalarExtension has a related projection-square
  theorem, for internal condensed module objects on pro-etale sites. It
  is not this ordinary small-etale finite-root-line statement. The actual
  ordinary geometric projection is the LowerStarProjection declaration,
  which defines the arrow and not the coefficient/twist commutativity.
- grep -rn of the exact node id in lean/WeilConjectures: no match.
- rg in lean/Sheaf for orderedProjection, ordered_projection, ordered
  projection and scalar/projection names: OrdinaryFiniteP1Arrows defines
  pi but states no coefficient square; P1CounitScalar states the counit
  compatibility, whose proof needs this ordered projection square;
  EtaleCompactScalarCoherence gives an arbitrary compactification support
  square without this fixed projective-line shifted twist; the generic
  RingedExchangeTensorCoherence is unordered and untwisted. None is the
  full statement of this item, so no existing:true rebinding is made.

Sources opened locally: the node's complete proof, all ten original
statement-dependency records and their source declarations, both reused
arrow-node records, the current main-20261015 Charts proof paragraph,
and sites-cohomology.tex remark-compatible-with-diagram (Tag 0E48), which
requires a commutative ringed square and not a cartesian square.

Validation: scompile.py compiled the module in sandbox and library modes
in 4.5 s and 4.6 s respectively, without errors or warnings. All variables
and the universe u are explicitly bound; autoImplicit is false. There is
one postponed theorem, with its matching node and complete five-step
proof docstring. No hollow data definitions, new nodes, dependency repairs,
statement corrections or disputed mathematical clauses are needed.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
