## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.TransposeComparisonUnit` states
`CategoryTheory.Adjunction.derivedTransposeComparisonUnit`, with exactly one
postponed theorem and no new definitions. Its three conjuncts are the homotopy
identity, the derived identity, and the displayed component identity. Only the
item's `lean` record changes; its statement and dependencies remain unchanged.

The node's source was read in the live read clone: `PlusAdjunction.lean`,
`derivedPlus_unit_app_fac` and the unit/naturality part (h₅, h₆) of
`derivedPlus_mateEquiv_app_fac`; and `HomotopyCategory/Adjunction.lean`,
`mapHomologicalComplex`, `mapHomotopyCategory`, `mapHomotopyCategoryPlus`, and
`mapHomotopyCategoryPlus_mateEquiv_app`. The latest blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` was also read:
this is a generic categorical subcalculation supporting that blueprint node,
not a separate blueprint unit statement.

Hypotheses and objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Four abelian categories in a chosen universe | Explicit `A`, `B`, `A'`, `B'` with `Category` and `Abelian` instances. All twelve universe variables are explicit; separate sizes allow a common bound without imposing accidental equalities. |
| Derived categories and bounded-below subcategories | Four `HasDerivedCategory` binders; Mathlib `DerivedCategory.Plus` through `DerivedCategory.Plus.Qh` and the derived functors. |
| Bounded-below homotopy complexes and localization q | `P : HomotopyCategory.Plus A`; `DerivedCategory.Plus.Qh`. |
| Exact additive L, L', G, H | The corresponding four `.Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits` instances are explicit theorem binders. Even the exactness instances not needed in the final expression are retained as the node requests. |
| E, E', T, S and canonical localization isomorphisms | These are the existing functors `.mapDerivedCategoryPlus`; the displayed formula only needs E' and its comparison `L'.mapDerivedCategoryPlusFactorsh.hom`. The other functors are determined by the binders, not extra input data. |
| Arbitrary transformation σ : L'G → HL | `σ : TwoSquare G L L' H`; by definition this packages exactly `σ.natTrans : G ⋙ L' ⟶ L ⋙ H`, with no commutation or invertibility hypothesis. |
| Enough injectives in A and A' | `[EnoughInjectives A] [EnoughInjectives A']`, exactly every object embedding in an injective object. No such assumption is made on B or B'. |
| Additive right adjoints and specified adjunctions | `R`, `R'`, their `.Additive` instances, and `adj : L ⊣ R`, `adj' : L' ⊣ R'`. |
| Termwise homotopy unit and counit | `adj'.mapHomotopyCategoryPlus.unit` and `adj.mapHomotopyCategoryPlus.counit`. |
| U, U' and α, α' | Existing `.rightDerivedFunctorPlus` and `.rightDerivedFunctorPlusUnit`. The equality only mentions U' and α'; no extra choices or replacement data are introduced. |
| Canonical normalized derived adjunctions | Existing `Adjunction.derivedPlus`, in particular `adj'.derivedPlus.unit`; its normalization is `derivedPlus_unit_app_fac` from the recorded dependency. |
| Ordinary mate b | `(mateEquiv adj adj' σ).natTrans`, using the recorded Mathlib mate equivalence. |
| N = K(R)P | `R.mapHomotopyCategoryPlus.obj P`, expanded everywhere. |
| M = K(G)N | `G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P)`. |
| W = K(H)P | `H.mapHomotopyCategoryPlus.obj P`. |
| Z = qM | `DerivedCategory.Plus.Qh.obj` of the expanded M. |
| d = K(H)(ε_P) ∘ σ_N | `(NatTrans.mapHomotopyCategoryPlus σ.natTrans).app (R.mapHomotopyCategoryPlus.obj P) ≫ H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P)`, expanded twice. |

Conclusions:

1. The first conjunct is `η'^K_M ≫ K(R').map d = K(b).app P`, exactly
   `K(R')(d) ∘ η'^K_M = K(b)_P` in the node. Lean's `≫` lists arrows in their
   traversal order, the reverse of mathematical composition notation.
2. The second conjunct is `η'^D_Z ≫ U'.map φ ≫ U'.map (q.map d) =
   q.map (K(b).app P) ≫ α'.app W`, exactly the displayed identity in D⁺(B').
   The comparison is applied at W, without any isomorphism hypothesis or inverse.
3. The last conjunct quantifies `∀ n : ℤ` and displays
   `η'_{G(R(Pⁿ))} ≫ R'(σ_{R(Pⁿ)}) ≫ R'H(ε_{Pⁿ}) = b_{Pⁿ}`,
   with `Pⁿ = P.obj.as.X n`. This explicitly records the component equality of
   the genuine termwise chain maps, rather than only equality after quotienting.
   Homotopy-category objects retain their complex representative as `.obj.as`.

There is no derived square, no derived mate, no hypothesis of injectivity on W,
no hypothesis that α'_W is invertible, and no assumption that σ is invertible.
The node's canonical choices are used directly; no arbitrary replacement maps
or hypotheses are used. The docstring contains all three proof steps with the
DAG dependencies, ready for stage 3. No statement correction or dispute.

Dependency declarations read and used:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`,
  `CategoryTheory.Abelian`.
- `def-weil-size-convention`: its recorded metatheoretic convention is rendered
  by the explicit category and derived morphism universe binders.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`.
- `def-weil-pbc-bounded-derived-subcategories`:
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, `DerivedCategory.Plus`;
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`, `DerivedCategory.Plus.Qh`.
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Functor.mapDerivedCategoryFactors`; its bounded-below restriction in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Functor.mapDerivedCategoryPlus` and `mapDerivedCategoryPlusFactorsh`.
- `def-sp-injective-resolutions`:
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `Injective` and
  `EnoughInjectives`; `InjectiveResolution` in the recorded `.Resolution`
  module was also read. This statement needs the enough-injectives predicate,
  not a separately supplied resolution.
- `lem-weil-pbc-termwise-adjunction-homotopy`:
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
  `Adjunction.mapHomotopyCategory`, its bounded-below restriction
  `Adjunction.mapHomotopyCategoryPlus`, and the chain-level construction
  `Adjunction.mapHomologicalComplex`.
- `lem-weil-pbc-right-derived-plus-injective`:
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `Functor.rightDerivedFunctorPlus`, `rightDerivedFunctorPlusUnit`.
- `lem-trf-bounded-below-derived-adjunction`:
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`,
  `Adjunction.derivedPlus`, `derivedPlus_unit_app_fac`,
  `derivedPlus_counit_app_fac`. The attachment lists these names without a
  module field; their actual source signatures and normalization were read.
- `def-weil-pbc-adjunction-mate`:
  `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`.

The primary public import supplies all the homological dependency declarations;
the second public import supplies the exact recorded mate definition. No
separate missing notion or unusable dependency interface was found.

Edge cases checked before writing: zero complex; σ = 0; identity adjunctions
and identity square; a complex concentrated in any integer degree; an arbitrary
bounded-below complex with noninjective terms, including noninjective W. For σ
zero both mate composites are zero by additivity; for identities both formulas
reduce to the canonical unit factorization. The argument uses naturality on all
of K⁺(A'), never an inverse of the comparison. No uniform lower bound, no
nonnegative-degree restriction, and no bounded-above restriction are introduced.
Different category object, morphism and derived morphism sizes remain available.

Searches (all through the prescribed msearch wrapper, 2026-10-24):

- LeanFinder query: "The derived adjunction transpose of a termwise mate equals
  the localized mate followed by the right derived comparison unit on arbitrary
  bounded below complexes". Eight hits, headed by `Adjunction.derivedε_fac_app`,
  `derivedη_fac_app`, their reassociated variants and derived-unit/counit
  definitions. They supply the general unit formula, not this combined statement.
- Loogle query: `CategoryTheory.Adjunction.derivedη_fac_app`. One exact hit in
  `Mathlib.CategoryTheory.Functor.Derived.Adjunction`; it is the unit identity
  input, not the mate identity.
- Mathlib grep query: `derived.*mate|mate.*derived|derivedη_fac_app`, restricted
  to `CategoryTheory`. Four files, including `Functor/Derived/Adjunction.lean`;
  no exact statement.
- LeanSearch query: "Termwise adjunction mate and bounded below derived unit
  comparison are compatible under localization". Eight hits, headed by
  `derived'_unit`, `derived_unit`, `localization_unit_app`, `derivedη.congr_simp`;
  none states the homotopy and derived mate identities together.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for derived transpose names,
  `derivedPlus_mateEquiv_app_fac`, and `mapHomotopyCategoryPlus_mateEquiv_app`:
  found the two source lemmas, their geometric applications and the parent
  `Sheaf.CategoryTheory.BoundedBelowDerivedMateModel`. The parent introduces a
  localized square and states a full derived mate formula, requiring additional
  data absent from this sublemma; it is not the same statement.
- `grep -rn` for the item's blueprint id in `lean/WeilConjectures`: no hits.
  `rg` of `dag/lean_names_upstream.json` for the item id and the proposed name:
  no hits. The proposed declaration name does not already exist in the project.

Validation: prescribed `scompile.py Q49 lem-trf-derived-transpose-comparison-unit`
compiled this file cleanly in both sandbox and library module modes (1.6 s and
1.7 s). `autoImplicit false` is explicit; every variable and universe is bound.
Every line is at most 100 characters. There is exactly one `sorry`, the named
main theorem. No definitions, helper axioms or additional postponed results.

## Second reading by Q49

A separate clause-by-clause reread by the same dispatched worker was performed
with the node and completed module open; no second agent was started, as the
assignment prohibits that. The maintainer's independent delivery review remains
independent of this author check.

Checked the direction of σ (`G ⋙ L' ⟶ L ⋙ H`), the direction of the ordinary
mate (`R ⋙ G ⟶ H ⋙ R'`), and the targets of all composites. The first composite
starts at M and ends at K(R')W. The second starts at Z = qM and ends at U'qW.
Its right side uses α' at W, not at P or at K(L')M. The exact comparison φ has
its hom direction, and is inside U'; there is no hidden inversion. The ordinary
component equality uses primed unit and unprimed counit at the correct objects.
All four exactness hypotheses and both enough-injectives hypotheses are explicit
binders even where the formula itself does not mention them. P is arbitrary in
K⁺(A); the degree quantifier ranges over all integers. No mismatch was found and
no change to the node's mathematical statement was needed.
