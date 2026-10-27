## Worker report

The module `Sheaf.CategoryTheory.ArithmeticSystemRightAdjoint` states
`SheafOfModules.arithmeticSystemRightAdjoint`. Its only theorem proof is `sorry`.
Three records bundle the componentwise normalized constructions asserted by this
same node; none chooses data from an unspecified existence assertion. In particular
there is no definition of a functor by choosing an arbitrary right adjoint.
The original delivery changed only `lean`; this repair also adds the two existing
declaration-owner nodes to `stmt_deps` as requested below. No new node, dependency repair,
statement correction, or disputed statement is needed.

The source read was the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower-equivalence.proof.md`,
including its adjunction, unit, counit and restriction paragraphs, and
`sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-bijection.proof.md`
with its normalization, bijections and purity paragraphs. Their current
text treats normalized reduction towers. The node's retained intermediate arithmetic
argument is given explicitly by the six proof steps in its JSON, which the theorem
docstring follows, with the general strict-system interface of Zheng Construction 4.1.

Hypotheses and clauses:

- The site is `C`, `Category C`, `J : GrothendieckTopology C`. Object universe `u`,
  morphism universe `v`, and coefficient universe `w` are independent.
  `EssentiallySmall.{w} C`, sheafification, locally bijective equivalences, and
  sheaf composition are the existing system dependency's small-site API. These are
  categorical infrastructure for the stated small site, not flatness or exact-products
  assumptions. A small site can be placed in any sufficiently large coefficient universe.
- `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat` is precisely the inverse sequence of ring sheaves.
  The strict category is the imported `StrictRingSystem B`, with its existing
  componentwise abelian structure, and `DerivedCategory` is its ordinary unbounded
  localization. Lean's natural level `n` means paper level `n+1` throughout.
- `e` and `_he : 1 ≤ e` express exactly the positive arithmetic step. The existential
  order embedding `r` is fixed by `r n = e * (n+1) - 1`; it is not a free subsequence.
  `selectedSystemRings B r` and `systemSubsequence B r` are the dependency's actual
  coefficient subsequence and restriction functor `U`.
- The existential `R` is the node's `J`. The witness `hf` supplies just the elementary
  inequality needed to type the existing restriction functor at the floor level.
  `ArithmeticSystemFloorData.level` gives restriction along the actual map
  `B_(e floor(k/e)) ← B_k`, using predecessor indices `(k+1)/e - 1`.
  `prefix_zero` makes every component below positive level `e` a zero object.
- `transition` describes all iterated transitions, not only successive ones: after the
  level identifications they are exactly the floor-index transitions of the original
  system. When floors agree its strict identity law makes these identities on sections.
  A transition into the zero prefix is uniquely zero. `map` specifies the restricted
  component of every morphism above the prefix; maps on the zero prefix are unique.
- `_hadd`, `_hlim`, `_hcolim` conclude additivity and exactness of `R`. Exactness of `U`
  is already supplied by `systemSubsequence_exact`; no extra assumption is imposed.
- `adjunction` is an actual natural adjunction `U ⊣ R`. `hom_selection` gives the
  selection `f_(en)` and `hom_extension` gives the inverse formula consisting of the
  original strict transition followed by restriction of `g_floor(k/e)`.
  `hom_prefix` states its zero components below `e` explicitly.
- `selected` identifies the selected component with `N.level n`. `counit` says the
  actual counit equals that identity identification. As a natural transformation,
  it also identifies selected transitions and morphisms: this is `UR = id` with the
  canonical harmless object-identification isomorphism. `unit_selected` gives the
  identity selected unit component, with that same identification.
- `quasiIso_restriction` and `quasiIso_extension` state preservation of quasi-isomorphisms
  by the termwise functors. `adjunction.mapExactDerivedCategory` is the dependency's
  specified derived adjunction, on precisely `U.mapDerivedCategory` and
  `R.mapDerivedCategory`. `derived_unit` and `derived_counit` give both localization
  equations through the standard `mapDerivedCategoryFactors` isomorphisms.
- The final quantified clause supplies every common coefficient sheaf `A` and compatible
  maps `α : const A ⟶ B`. `β` is fixed to `α` at selected indices. It uses any chosen
  total derived limit `RF` and comparison `η` from the recorded strict-tower theorem:
  `RF.IsRightDerivedFunctor η` and invertibility on K-injectives specify that choice,
  rather than any additional assertion about the tower. The target localization
  universe `z` remains independent and quantified with its chosen localizations.
- `ArithmeticSystemScalarForgetting` fixes the forgetting functors by the existing
  `restrictScalars` at every component, on every morphism, and on every transition.
  Its exactness fields are conclusions provided by the theorem, never input hypotheses.
- `ArithmeticSystemLimitData.selection` identifies arithmetic selection of `F_B R`
  with `F_r`. `selection_sections` fixes this isomorphism to the identity on underlying
  sections; `HEq` accounts for the propositionally equal selected indices and their
  dependent module types. It does not leave an arbitrary scalar or tower comparison.
- `comparison` is the asserted natural isomorphism `L_B R ≅ L_r`, writing
  `L_B R = D(R ⋙ F_B) ⋙ RF` and `L_r = D(F_r) ⋙ RF`. The canonical exact-composite
  factorization identifies this with `D(R) ⋙ D(F_B) ⋙ RF` as in the node.
  `normalization` specifies its canonical map on every complex by the actual
  `StrictTowerArithmetic.limitMap e`, followed by the termwise identity selection
  comparison. This fixes every selected limit projection: on K-injective tower
  representatives, `limit.pre` satisfies `limit.pre_π`, so the n-th target projection
  is exactly the original e(n+1)-th projection. Localization gives the same equation
  for derived projections. Neither exactness of countable products nor flatness is
  assumed at any point.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SystemLevelLeftExtension`:
  `SheafOfModules.systemLevelLeftExtensionTheory`, publicly reexporting
  `StrictRingSystem`, `systemLevel`, `systemRestriction`, `systemSubsequence`,
  `selectedSystemRings`, their exactness, abelian and derived-category instances from
  `SystemLevelLeftExtensionBasic`. Full strict-system and Hom signatures and the
  subsequence definition were read. No replacement category is introduced.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, through the dependency imports.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; its complete definition and additive instance were
  read. `systemRestriction` uses exactly this functor.
- `Sheaf.CategoryTheory.ExactDerivedAdjunction`:
  `CategoryTheory.Adjunction.mapExactDerivedCategory`, and its retained specialization
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`. The independent
  universe generalization is essential for source and target system categories.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`; the full
  declaration was read. Its `RF`, `η` and K-injective computation are the inputs
  quantified in the final clause, for all choices satisfying the universal property.
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`:
  `CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestriction`,
  `restriction`, `limitComplex`, `limitMap`. The main signature and actual arithmetic
  index and limit-map definitions were read; these fix the projection normalization.
- The proof import `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
  supplies `SheafOfModules.sheafRingDerivedCoefficientAdjunction` for scalar exactness.
- The Mathlib leaf `lem-weil-pbc-exact-functor-derived-factorization` is supplied by
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, already publicly imported;
  `mapDerivedCategory` and both factorization signatures were read.

Edge cases checked before and after writing:

- `e=1`: `r n=n`, empty zero prefix, floor index `k`; the right extension is the identity
  with the canonical identity scalar restriction. The normalization is identity restriction.
- `e=2`: positive level 1 is zero, levels 2 and 3 use the first selected component,
  and level 4 uses the second. The 3→2 map is identity on sections; 4→3 is the
  original selected transition, with scalar action restricted through B_4→B_3→B_2.
- Within any block repeated floor indices use strict identity transitions. Across a
  boundary, composition uses the original selected transition. All transitions into
  the prefix and all prefix map components are forced to be zero.
- Zero rings, zero systems, the empty site, and unbounded complexes are allowed.
  All tower indices remain present; no terminal coefficient, flatness, boundedness,
  normalization, or exact-products condition was added.

Searches actually run with `batch2/msearch.py` for this group and item:

- LeanFinder: "Exact right adjoint to arithmetic subsequence restriction of strict
  inverse systems of module sheaves using floor extension": eight results including
  condensed solidification, locally constant module adjunctions, local cohomology,
  and Nobeling successor exactness. None is this varying-ring floor extension.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Functor`: twelve general
  adjunction declarations/constructors, no specified system construction.
- Mathlib grep: `floor.*[Ss]ystem|[Aa]rithmetic.*[Aa]djoint|subsequence.*[Aa]djoint`:
  zero results.
- LeanSearch: "Arithmetic subsequence restriction of strict inverse systems of module
  sheaves admits an exact floor extension right adjoint": eight results concerning
  module restriction, scalar adjunctions, and sheaf limits, none states this node.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for arithmetic right adjoints,
  floor extensions and the proposed full names: only the constant-ring strict-tower
  arithmetic theorem and the compact-support Roos construction were related. Neither
  defines this varying-ring right extension. Searching the exact blueprint id in
  `WeilConjectures` produced no match. Existing `systemSubsequence` was reused.

Validation is through the prescribed `scompile.py` and `deliver2.py` wrappers only.
The initial syntax issue (reserved field name `prefix`) was fixed by naming it
`prefix_zero`. The selected-section formula initially tried equality between module
objects over propositionally equal indices; it now states the identity on underlying
sections using `HEq`, preserving the exact mathematical content.

The first complete elaboration exceeded 60 seconds while generating structure
auxiliaries and unfolding the derived constructions. Matching the dependency's
transparency settings and disabling unused generated size/injectivity auxiliaries
fixed this without splitting the file or increasing the timeout. A diagnostic
profiler run compiled in 14.9 seconds; the profiler was removed before delivery.

## Repair of return 0aa48100d19f

The maintainer's single H2 finding was that two definition owners used by the
Lean statement were absent from the statement-dependency graph. This repair adds
exactly these already landed nodes to the item's `stmt_deps`:

- `def-sp-strict-tower-arithmetic-restriction-data`, owning
  `CategoryTheory.StrictTowerArithmetic.restriction`, `limitComplex`, and `limitMap`
  in `Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs`. The declarations
  are already publicly reexported by the imported arithmetic-restriction module.
- `def-pur-system-level-left-extension-basic`, owning
  `SheafOfModules.StrictRingSystem`, `systemRestriction`, `selectedSystemRings`,
  and `systemSubsequence` in `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic`.
  They are already publicly reexported by the imported left-extension theorem module.

Both owner records and their actual source signatures were re-read. Their definitions
are precisely those used in the reviewed statement, including the positive-level
predecessor indexing and the actual `limit.pre` comparison. No replacement notion
is introduced. The source file is byte-for-byte the retained returned version, and
`lean.statement` still equals its theorem signature verbatim. No mathematical
statement, proof plan, or dependency record is changed. Against current main the
node differs only in the original `lean` binding and these `stmt_deps` additions;
the delivery wrapper builds the repaired packet on refreshed current main.

The one requested return point is therefore repaired by a real metadata change,
not an unchanged re-push. Compile and delivery preflight are repeated through the
prescribed wrappers.

## Second reading by Q100

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
