## Worker report

Module: `Sheaf.Paper.CompactSupportReductionAdjoint`.
Declaration: `AlgebraicGeometry.Scheme.coefCompactSupportReductionAdjoint`.
It states the node's equivalent unit equation and both invertibility assertions.
Its only theorem proof is `sorry`; there are no definitions, axioms, or proof additions.
The four-step natural-language proof is in its docstring.

Hypothesis and clause correspondence:

- The field k is `(k : Type u) [Field k]`. The prime and its invertibility are
  `(l : ℕ) [Fact l.Prime]` and `(_hl : IsUnit (l : k))`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The valuation ring, chosen uniformizer and quotient
  rings are the existing `Padic.coefficientExtensionRing`, with no new coefficient choice.
- All positive levels are represented as `m + 1`, `n + 1`, where `m n : ℕ` and
  `hmn : n ≤ m`. Every source pair of positive levels occurs uniquely this way;
  addition of one preserves their order. The first positive level is index zero.
  Positivity witnesses passed to constructibility are `Nat.le_add_left 1 m/n`.
- X and Y are `Scheme.{u}` with `Over (Spec (.of k))`. Each structure morphism has
  `LocallyOfFiniteType` and `QuasiCompact`, exactly finite type over k.
- The map is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` with `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact`. The fixed `(c : Compactification f)`
  supplies its actual open immersion, proper map and factorization equation.
- The small pro-etale derived module categories are `proEtaleDerivedCategory X A`:
  Mathlib's small site has object universe u+1 and morphism universe u; coefficients
  and module sheaves use the existing ULift into u+1. The library's standard derived
  localization is retained. No equality of site object and morphism universes is added.
- The actual quotient map is `compactSupportLevelQuotient l E m n hmn`, the quotient
  factor of the inclusion of uniformizer-ideal powers. Its constant sheaf map is
  `compactSupportLevelSheafQuotient l E T m n hmn`.
- `Res_T` is `pbcDerivedRestrict` of that sheaf map. `L_T` is `pbcDerivedExtend` of
  the same map, and `eta_T` is the unit of `pbcDerivedScalarAdjunction` of that map.
  These are the existing normalized ordinary derived scalar constructions, not
  completed scalar extension or arbitrarily selected adjunctions.
- `F_s` is `sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (s+1))`,
  the specified extension by zero followed by the specified total derived proper image.
- The canonical sigma is `(sfCompactSupportRestriction c quotient).hom.app ...`.
  This original declaration is publicly retained by the dependency's recorded
  `IntrinsicCompactSupportRestriction` module. Its original coordinates are exactly
  those of the recorded F_s and gamma used here. The later `intrinsicCompactSupportRestriction`
  also retained there uses the different `directImageConstantPush` coordinates, so it
  is not silently substituted for the sigma defining this gamma.
- V and W have exactly the upper/lower categories, and `_hV`, `_hW` state their
  `intrinsicFiniteTorsionConstructible` predicates individually. Beta has type
  `(pbcDerivedExtend sheafQuotientX).obj V ≅ W`; its actual morphism is `β.hom`.
- Gamma is the recorded `intrinsicCompactSupportCoefficientComparison quotient c V`.
  Its definition is the inverse of the normalized Hom bijection applied to compact
  support of eta_X followed by sigma at L_X V. Thus its unit-characterization is
  built into the chosen arrow, not added as a hypothesis.
- Rho is expanded literally as `eta_X.app V ≫ Res_X.map β.hom`. Tau is expanded as
  `F_m.map (eta_X.app V ≫ Res_X.map β.hom) ≫ sigma.hom.app W`.
- The first conjunct is `eta_Y.app (F_m.obj V) ≫ Res_Y.map (gamma ≫ F_n.map β.hom) = tau`.
  Lean's `≫` reads in execution order, reversing the usual written function-composition
  notation in the node. This is exactly the node's explicitly equivalent displayed
  equality and hence identifies the adjoint of this actual tau, not just some isomorphism.
- The second conjunct is `IsIso gamma`, the third is `IsIso (F_n.map β.hom)`.
  There is no flatness, finite Tor dimension or Tor-amplitude assumption.

Dependencies read and used (including their public implementations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported `CoefficientExtension`:
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, its category and imported
  `AlgebraicGeometry.Compactification`; finite-type/separated properties use Mathlib
  as instructed by the convention-only def-weil-scheme-morphism-properties node.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `ProEt.topology`; `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  abbreviation of Mathlib `SheafOfModules`; `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`; these are the categories inside
  `proEtaleDerivedCategory`, not duplicate constructions.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; its exact derived implementation is the published
  `pbcDerivedRestrict` in `Sheaf.Paper.BoundedConstructibleTower`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, the general normalized
  coefficient adjunction. The actual pro-etale normalized adjunction is the existing
  `pbcDerivedScalarAdjunction` in `Sheaf.Paper.BoundedConstructibleTower`, also with
  its K-flat tensor-unit normalization; no replacement adjunction is introduced.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`: the recorded
  `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction`, with public import
  of `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` and its
  `AlgebraicGeometry.Scheme.sfCompactSupportRestriction`, used in the original
  coordinates required by the tensor-comparison definition.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.CompactSupportIntrinsicTensorComparison`:
  `AlgebraicGeometry.ProEtale.intrinsicCompactSupportCoefficientComparison`.
- Proof import `Sheaf.Paper.FiniteCompactSupportScalarComparison`:
  `AlgebraicGeometry.Scheme.finiteCompactSupportScalarComparison`, for the
  invertibility step, with upper/lower variables swapped relative to that theorem's names.
- Added existing statement dependency `def-weil-compact-support-reduction-tower-data`:
  `Sheaf.Paper.CompactSupportReductionTowerData`,
  `WeilConjectures.compactSupportLevelFinite`, `compactSupportLevelQuotient` and
  `compactSupportLevelSheafQuotient`. These already define exactly the finite rings,
  direct quotient and sheaf quotient needed here, and supply positive-level finiteness.
  The addition reuses the landed coefficient definitions; no node is redefined.

Edge cases: m=n is allowed (`hmn` is non-strict), including m=n=0 indexing level 1.
The empty scheme, zero V or W, and arbitrary fixed compactifications are allowed.
For a zero object the same unit and naturality equations apply. A beta to zero
correctly imposes that the actual lower reduction be zero. Unbounded Tor behavior
of a quotient is not excluded: bounded constructibility of the actual reduction
follows from beta and W, exactly as in node proof step 1. The statement does not
assume it separately. Field characteristic only obeys invertibility of l, including
characteristic zero. A common universe for finite coefficients, fields and schemes
follows the recorded APIs; arbitrary sizes can be put in a common ambient universe.

Searches (2026-10-22, msearch.py with group Q121 and this item):

- LeanFinder query: "Compact support coefficient comparison is the scalar adjoint of
  the reduction transition and is invertible for bounded constructible complexes".
  Eight hits: Profinite Nobeling maps and complex support embeddings; no match.
- Loogle query: `CategoryTheory.Adjunction, "homEquiv"`. Twelve hits including
  `Adjunction.homEquiv`, `homEquiv_apply`, `homEquiv_symm_apply`, and natural
  adjunction constructors. These supply generic machinery, not this geometric theorem.
- Mathlib grep query: `compactSupport.*(tensor|adjoint)|coefficientComparison`,
  subdirectory `AlgebraicGeometry`: zero hits.
- LeanSearch query: "The scalar extension adjoint of compact support reduction is the
  compact support tensor comparison composed with the image of the reduction isomorphism".
  Eight hits: ordinary ModuleCat extension/restriction adjunctions and scalar-localization
  equivalences; no derived compact-support assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for compact-support tensor/adjoint,
  coefficient comparison and reduction adjoints found the recorded tensor comparison,
  finite invertibility theorem and related tower comparisons; none states this node's
  beta-dependent identity together with its invertibilities. The source-ID `grep -rn`
  in WeilConjectures has no hit. `rg` for the proposed declaration and source ID in
  both libraries and `dag/lean_names_upstream.json` found no existing declaration.
- All direct statement-dependency node records and signatures/docstrings were read.
  No maintenance repair note exists for this item. The example CompactObject module
  is withdrawn and empty; the current module header rules were followed instead.

Validation: scompile.py checked the module in sandbox and library mode against the
published server build, successfully (8.6 s / 6.0 s), with no errors or unexpected
warnings. Diagnostic #check commands were removed before the final compile.
No STATEMENT-DISPUTED finding and no statement correction or dependency repair.

## Second reading by Q121

I reread the finished node and module together in this worker session; no separate
agent was started, as the dispatcher explicitly prohibits that. The maintainer's
independent delivery review is still required. The reread checked the fields,
positive-level successor reindexing, all three finite-type hypotheses, the fixed
compactification, both constructibility assumptions, beta's orientation, and all
three conjuncts. In particular, `≫` expands rho and tau in the correct order and
the first conjunct is the node's equivalent unit equation, not the weaker assertion
that an unspecified adjoint exists. The imported tensor comparison uses the same
F_s and sigma as the theorem. No mismatch was found and no source statement was
changed. The only dependency addition is reuse of already landed quotient data.
