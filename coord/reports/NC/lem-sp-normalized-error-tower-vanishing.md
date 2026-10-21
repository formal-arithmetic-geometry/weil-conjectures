## Worker report

The module `Sheaf.Paper.NormalizedErrorTowerVanishing` states
`AlgebraicGeometry.ProEtale.sp_normalized_error_tower_vanishing`. Its conclusion is
`SpNormalizedErrorDiagram ...`, a fully written existential proposition retaining the strict maps and
all the specified comparisons, rather than asserting an unspecified object isomorphism.
The named proposition is just the conjunction of the displayed clauses, under existential
binders for their witnesses. Every definition has real data; the only postponed proof is the main theorem.

Hypothesis-by-hypothesis correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  `(T : Scheme.{t})` is arbitrary, independently of `u`.
- `spCoefficientRing l E T n` is the recorded constant quotient at exponent `n+1`.
  `completedIntegralCoefficientSheafUnrestricted l E T` is the recorded completed R.
  `spCoefficientCommRings` retains the same quotient sheaves with their commutativity.
- `Q` is a family of unbounded integer cochain complexes over these quotient sheaves.
  `SpErrorTransitions` uses actual restriction of scalars along `spLevelReduction`,
  so the maps are semilinear chain maps, not arbitrary underlying functions.
  `hq_id` and `hq_comp` impose identities and all cocycle equations on every degree
  and every object of the site.
- `hflat` is precisely `CochainComplex.IsKFlatIndependentCoefficients (Q n)` for
  each level. There is no termwise flatness, boundedness or constructibility condition.
- `hnorm` supplies the reduction with `SpErrorReductionFormula` and `QuasiIso`.
  The formula is exactly `x tensor b ↦ b q(x)` on sheafified tensor generators.
  This formula uniquely determines the map by the tensor and sheafification universal
  properties. Existence of that canonical map is automatic from semilinearity; writing
  it as an existential jointly with quasi-isomorphy expresses the node's normalization
  hypothesis without an arbitrary comparison map. Restriction to R leaves the underlying
  abelian sheaf complex and its cohomology unchanged, hence tests the same quasi-isomorphism.
- `m : ℕ` stands for the positive exponent `m+1`. The tail index `j` stands for
  exponent `m+j+1`. In particular m=0 covers the paper's m=1.
- `RF`, `κ`, `hRF` choose any total right-derived inverse-limit functor with its
  comparison transformation, using the recorded `IsRightDerivedFunctor` interface.
  The two `HasDerivedCategory.{w}` binders choose the localization universe; they
  impose no finiteness or mathematical restriction on the coefficient complexes.

Clause-by-clause correspondence, through the named clauses in `SpNormalizedErrorDiagram`:

- `spErrorMiddle` is the actual total tensor of the restricted Q_n with the recorded
  `principalKoszul` K_m in degrees -1,0. `spErrorReduction` is the actual B_n-total
  tensor with B_m[0], followed by restriction to R.
- `spErrorCoefficientAugmentation` uses the augmentation supplied by
  `sp_ell_coefficient_fiber`. Its equation with the degree-zero cone inclusion
  uniquely specifies it: the target is concentrated in degree zero. Only that
  uniquely normalized arrow is extracted; no unspecified coefficient object is chosen.
  `spErrorCoefficientFiber` is its actual shifted mapping cone. `spErrorFiberTensor`
  is Q_n tensor_(B_n) that fiber, restricted to R.
- `s`, `t`, `s_formula`, `t_formula` give the usual strict S and M transitions.
  `Functor.ofOpSequence` supplies identities and all composite transitions.
- `a`, `a_left`, `a_right` specify the strict augmentation on the two free Koszul
  generators: zero in degree -1 and `x tensor 1 ↦ x tensor 1` in degree zero.
  R-linearity determines the augmentation for every coefficient, hence the actual
  coefficient augmentation, without a free choice of arrow.
- `assoc` and `assoc_formula` identify the explicit P_n,m tensor model with M_n.
  In both Koszul degrees the equation is `x tensor (b tensor 1) ↦ bx tensor 1`.
  The two free generators and balancedness determine `x tensor (b tensor k) ↦ bx tensor k`.
- `A`, `fiber`, `fiber_transition_formula`, `distinguished` give a strict left tower
  with exactly the actual coefficient-fiber tensor terms and their canonical transitions,
  and a distinguished triangle in D(strict R-towers). The right arrow is exactly Q(a).
  `SpErrorFiberTransitionFormula` fixes the transitions on every generator in the
  three cone coordinates: quotient reduction on the two B_n coordinates and identity
  on B_m, together with q on Q. `left` is existential, as in the node, which specifies
  the augmentation arrow and middle identification but does not normalize the left arrow.
- `η`, `η_quasiIso`, `η_levelwise` give a strict levelwise quasi-isomorphism from
  `spErrorPoweredShift` to the left tower. `powered_transitions` gives every gap,
  including the zero gap: ell^(j'-j) times the usual S transition shifted by 1.
- `ρ`, `reduction_formula`, `reduction_quasiIso` give the strict map to the
  constant tower on Q_m, with exactly the transition-induced component formulas.
- `limit_zero` says the total derived inverse limit of the left tower is zero.
- `diagonal` and `diagonal_formula` identify Q_m with the total derived limit of
  its constant tower by the identity cone. `spErrorDiagonal` is the ordinary
  constant/limit unit followed by the total-derived comparison, not an arbitrary iso.
- `composite_isIso` asserts invertibility of RF(Q(a)), followed by RF(Q(ρ)),
  followed by this specified diagonal's inverse. This is the exact composite in the node.

Dependency declarations read and used:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientRing`,
  `spCoefficientRings`, `spCoefficientReduction`, `sp_completed_coefficient_limit`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.EllCoefficientFiber`: `spCompletedEllProjection`, `spLevelReduction`,
  `spRelativeCoefficient`, `spRelativeKoszul`, `spRelativeFiber`,
  `SpRelativeFiberComparison`, `sp_ell_coefficient_fiber`, and
  `sp_completed_coefficients_regular` (the coefficient meaning and proof plan).
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  the total-summand inclusion; `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns`:
  `total`, `ι`, `Modules`, `tensor`, through the new definition node
  `def-sp-total-tensor-summand-interface`. The signs theorem remains proof-only.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients` (the full total right-derived
  functor, exactness and pro-zero interface).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its localization/shift/triangle structure.
- Added landed dependency `lem-coef-derived-tower-counit-projections`, for
  `strictTowerConstantAdditive` and
  `strictTowerLimitAdditive` in `Sheaf.CategoryTheory.DerivedTowerCounitProjections`;
  and `def-pur-principal-koszul-quotient-towers`, for `principalKoszul`,
  `koszulTowerComplex` and `koszulTowerComplexMap` in
  `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`.
- Proof-only inputs: `CochainComplex.IsKInjective`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`,
  `CategoryTheory.Pretriangulated`, `Triangle.coyoneda_exact₂`, and
  `CategoryTheory.Abelian.functorCategoryAbelian`, in the recorded dependency modules.

Edge cases read against the node and its source proof: m=1 (Lean m=0), n=m
(tail j=0), equal transition indices (power ell^0=1), a gap equal to m (Lean m+1,
which annihilates S), zero complexes, the empty scheme, Q_n=B_n, and unbounded
complexes. No case is excluded by the statement or its universe binders.

Searches actually run:

- msearch.py, LeanFinder: `A normalized tower of K-flat quotient coefficient complexes
  has a pro-zero tensor fiber tower and its derived limit recovers finite reduction`.
  Eight hits, on adic completion of ordinary modules and flatness criteria; no match.
- msearch.py, Loogle: `"IsDerivedLimitTriangle", "QuasiIso"`: zero hits.
- msearch.py, grep in Mathlib/Algebra/Homology:
  `[Nn]ormalized.*[Tt]ower|[Tt]ower.*[Kk][Ff]lat`: zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for normalized towers and the item id:
  existing adic-tower results concern constant ring coefficients, homotopy-limit cones,
  or bounded constructible effectivity; none states all these strict coefficient-fiber,
  normalization and total-derived-limit clauses for the actual completed ring sheaf.
- rg of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the proposed theorem/predicate/generator names: no collision.

The source read was the current main-20261015 `sk-lem-sp-tower.proof.md`, from the
coefficient tensor calculation through normalization, vanishing of the left term and
the reduction formula. No mathematical statement correction, disputed clause or dependency-interface
replacement is needed. The returned H2 repair below adds definition-node records
for existing interfaces, without new Lean definitions.

## Second reading by NC

Author's separate self-check for direct worker delivery; the maintainer supplies the
independent review. I reread the node beside the theorem and every existential binder and clause of the
conclusion. In particular, Q is K-flat over B_n, not over R; the normalization maps
are specified by pure tensors; the left shift is [1] and its gap exponent is n'-n;
the strict triangle is in the derived category of the tower category; and the last
arrow is the inverse of the identity-cone diagonal. The positive-index reindexing
keeps n=m and m=1. No extra bound, constructibility hypothesis, choice of arbitrary
comparison map, or statement correction was introduced. Compiler-driven repairs
are recorded in the final verification paragraph below.

Verification: scompile.py compiled the complete module in both sandbox and library
contexts without errors or warnings (22.8 s and 20.3 s). Explicit category arguments
at the derived localization maps resolve scalar-restriction presentation differences
without identifying the independent site and coefficient universes. The final delivery
dry run also recompiles the module after its direct principal-Koszul import.


## New nodes

`def-sp-commutative-coefficient-ring-tower` records, with `existing: true`,
`AlgebraicGeometry.ProEtale.spCoefficientCommRings` in
`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`. The definition uses precisely
constant commutative quotient ring sheaves at exponent n+1 and their quotient
reductions. Its source is the quotient-coefficient calculation of the current
`sk-lem-sp-tower` proof and the coefficient-tower definition. Reading its body
shows actual `constantSheaf`, `Ideal.Quotient.factorPowSucc` and
`Functor.ofOpSequence` data. No theorem or `.choose` is used for this tower.
LeanSearch and LeanFinder returned generic quotient reductions and ordinary
adic/module constructions; Mathlib grep found no coefficient-tower match.
Project grep found this exact definition in the existing module. DAG grep found
it only among theorem-node helper declarations, with no owning definition node.
`tools/blueprint_refs.py search 'commutative coefficient tower'` returned no
blueprint matches. The new node cites `sk-def-sp-coefficient-towers` and states
exactly this commutative-ring presentation of its tower.

`def-sp-total-tensor-summand-interface` records, with `existing: true`, the existing
`SheafOfModules.TotalTensorSigns.ι`, and its `Modules`, `tensor`, `total` aliases,
in `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns`. Its statement specifies
the category of module sheaves, sheafified balanced tensor, direct-sum total
with the usual sign, and the canonical direct-sum inclusion. The source is
Stacks' associated simple complex (012Z), applied to sheaf tensor as in 06YM,
and the current blueprint's tensor calculation. Its dependencies are the
existing category, sheaf tensor and total-complex definition nodes. LeanSearch
found generic tensor inclusions; Loogle found `CochainComplex.ιMapBifunctor`;
Mathlib grep found that inclusion and the total bifunctor. Reading the project
source confirms that `ι` is exactly its sheaf-tensor specialization and that the
other three declarations are transparent aliases. No theorem is extracted.
DAG grep found these declarations only under the signs theorem, with no owning
definition node for this concrete interface; the generic total tensor node
continues to be cited and reused. The blueprint search for 'total tensor summand'
returned no matches. No Lean module is added for either existing definition node.

## Returned H2 repair

The immutable returned head was `9b8687c4160d`. I retained its saved Lean module
and compared the saved node with the current read-only main node: the only
changed fields were `stmt_deps` and `lean`. The initial saved-packet dry run
passed mechanically as `2e7dc741d64`, but the return identified an ownership
error that those checks did not detect. This repair follows option (a) exactly:
remove `det-sp-coefficient-towers-abelian` and
`lem-weil-pbc-total-tensor-homotopy-cone-signs` from statement dependencies;
add the two definition nodes described above and cite those instead. The signs
theorem remains in `proof_deps`. The counit-projections dependency remains,
since its `strictTowerConstantAdditive` and `strictTowerLimitAdditive` are genuine
Prop-valued additive instances used in the statement. All Lean code, the item's
mathematical statement, its proof plan, and all other node fields are retained.

I reread both new nodes against the existing source declarations, including their
section variables and bodies. For the coefficient node, l is prime, E is finite
over Padic l and T has its independent site universe; n=0 denotes exponent one,
all reductions are actual quotient maps, and identities and composites are the
functor's. For the tensor node, site and coefficient universes remain independent,
complexes are unbounded, the sum is a direct sum, and the inclusion uses exactly
the equality p+q=n. The empty scheme, zero complex, negative cochain degrees,
and zero-gap transition introduce no extra restriction. This is the author's
repair self-check; independent review remains the maintainer's, as requested
for direct worker delivery. No agents were started.
