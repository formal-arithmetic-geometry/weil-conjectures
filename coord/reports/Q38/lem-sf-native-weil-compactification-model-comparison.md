## Worker report

Stage 2 attachment for lem-sf-native-weil-compactification-model-comparison.
The Q18 delivery reviewed PASS on 2026-10-22 was the stage-1 proof split; the live
node still had no lean field. This delivery preserves its statement and proof.
No re-splitting is performed. No repair note exists for this item.

Module: Sheaf.WeilSheaf.NativeCompactificationModelComparison.
Main declaration: AlgebraicGeometry.nativeWeilCompactificationModelComparison.
Its proof is sorry, the only sorry in the module. Its docstring preserves the
four-step proof plan and names every proof dependency. The auxiliary definition
AlgebraicGeometry.nativeWeilCompactificationRefinementComparisons is an explicit
Prop-valued packaging of the displayed chain. It belongs to this same notion,
uses real existing operations, and has no postponed proof or chosen data.

Hypothesis-by-hypothesis correspondence:

- The finite field k₀ is `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- The prime ℓ different from the characteristic is `(l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]`. The coefficient field is the framework's PadicAlgCl l;
  no second coefficient category or arbitrary realization is introduced.
- X and Y are `Scheme.{u}`, each with `Over (Spec (CommRingCat.of k₀))`.
  Each finite-type structure map has `LocallyOfFiniteType` and `QuasiCompact`.
- The target's quasi-compactness is the same `QuasiCompact` structure-map binder;
  quasi-separatedness is `QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))`.
  Since Spec k₀ is affine, these are exactly the qcqs condition on Y.
- The map is `(h : X ⟶ Y) [h.IsOver (Spec (CommRingCat.of k₀))]`, with
  `[IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]`, exactly separated
  finite type. There is no absolute-separatedness assumption on X or Y.
- A compactification is the recorded `Compactification h`, with proper leg g,
  open leg i, and comm : h = i ≫ g. Each quantification explicitly includes
  `[QuasiCompact c.i]`, because the upstream general structure omits this field.
- A refinement is the dependency's `Compactification.Refinement c₁ c₂`.
  Its `hom`, `i_hom`, and `hom_g` express respectively v, j₁ ≫ v = j₂ and
  v ≫ r₂ = r₁. Its existing `Refinement.isProper` instance proves exactly the
  required properness of a Y-map between these proper compactifications.
  Conversely any v in the node supplies this record by those two equations.

Clause-by-clause correspondence:

- The source restriction to WC^der(X) is `(WeilComplex.objectProperty k₀ l X).ι`.
  Its full subcategory is exactly the existing `WeilComplex k₀ l X`, using the
  ordinary derived category of all native equivariant pro-etale Weil sheaves.
- J_j is `(ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory`, the
  termwise exact native extension. Rr_* is
  `(ProEtaleWeilSheaf.lowerStar k₀ l r).rightDerivedFunctor`.
- F_c is exactly the existing `ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c`,
  whose defining expression is J_c.i ⋙ R_c.g. It is not a new functor definition.
- The first outer conjunct quantifies over both compactifications and every
  refinement. Its helper predicate has four conjuncts. The first is
  Nonempty (J_j₂ ≅ J_j₁ ⋙ Rv_*) after restriction to WC^der(X), translating
  J_j₂ ≅ Rv_* J_j₁ in Lean's left-to-right functor-composition convention.
  The second is Nonempty (F_c₂ ≅ J_j₁ ⋙ Rv_* ⋙ Rr₂_*), the first F comparison.
  The third is Nonempty (J_j₁ ⋙ Rv_* ⋙ Rr₂_* ≅ J_j₁ ⋙ R(v ≫ r₂)_*).
  The fourth is equality of that last functor with F_c₁, using v.hom_g.
  All four expressions include the bounded-constructible inclusion.
- The second outer conjunct quantifies over arbitrary compactifications without
  supplying a refinement, and asserts Nonempty (F_c₂ ≅ F_c₁) on that full source.
- The third outer conjunct states Nonempty (F_c ≅
  WeilComplex.derivedLowerShriek k₀ l h ⋙ (WeilComplex.objectProperty k₀ l Y).ι).
  This compares with the framework's actual chosen model in the ambient target,
  including the canonical full-subcategory inclusion on the chosen model side.
- Every `≅` is an isomorphism in a functor category, so it includes naturality,
  invertible components and inverse naturality. The target derived categories
  have native equivariant morphisms by definition. No faithful-forgetting
  hypothesis, arbitrary lift or action on fixed pairs in a derived category is used.
- Nonempty assertions record precisely existence. There is no independence from
  choices, no specified unique comparison and no cocycle requirement.

The helper's letI bindings occur only in its defining value, not in a theorem
signature. They install the canonical `Compactification.over` structures induced
by g and Y's structure map. The refinement's IsOver proof is an explicit
associativity rewrite of hom_g; it is not an additional assumption. This is
ordinary concrete proof data, not a theorem postponed with sorry. No file-local
notation, private declaration or local instance attribute is introduced.

Dependencies used (module and declaration):

- def-sf-native-weil-derived-framework: WeilConjectures.WeilSheaf.LowerShriek,
  AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek and
  AlgebraicGeometry.WeilComplex.derivedLowerShriek. Read their complete definitions
  and docstrings, including the selected HasCompactification.compactification.
  Its imported Category and OpenImmersion modules supply WeilComplex.objectProperty,
  ProEtaleWeilSheaf, and ProEtaleWeilSheaf.extensionByZero. The imported LowerStar
  module supplies ProEtaleWeilSheaf.lowerStar. All are the recorded native objects.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  AlgebraicGeometry.LocallyOfFiniteType, and Morphisms.QuasiCompact,
  AlgebraicGeometry.QuasiCompact (imported by FiniteType).
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  AlgebraicGeometry.IsProper and IsSeparated.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  AlgebraicGeometry.IsOpenImmersion.
- def-weil-compactifications-refinements:
  WeilConjectures.Compactification.RefinementCategory,
  AlgebraicGeometry.Compactification.Refinement and its isProper instance;
  Compactification from its imported Defs module. Read both structures in full.
- def-weil-quasi-separated-morphism:
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated,
  AlgebraicGeometry.QuasiSeparated (quasi-compact diagonal).
- Proof imports: Sheaf.WeilSheaf.NativeBasicComparisons,
  AlgebraicGeometry.nativeWeilBasicComparisons;
  Sheaf.WeilSheaf.NativeOpenProperInterchange,
  AlgebraicGeometry.WeilComplex.nonempty_extensionByZero_rightDerivedLowerStar_iso;
  Sheaf.AlgebraicGeometry.CompactificationCategory,
  AlgebraicGeometry.Compactification.compactificationCategory_properties.
  Read the declarations and their proof docstrings. The finite-type composition
  leaf uses Mathlib.locallyOfFiniteType_comp and quasiCompact_comp, and the
  quasi-compact open-leg leaf is AlgebraicGeometry.QuasiCompact.of_comp in the
  imported QuasiSeparated module. Thus every stated proof dependency is imported.

Source and edge cases:

Read literature/stacks-project/more-etale.tex, lemma-shriek-well-defined (0F7I),
and lemma-shriek-composition (0F7J). The displayed comparison is the same proper/open
calculation; the DAG explicitly adapts it to native coefficients. The result here
intentionally stops at existence, as the DAG does. It does not claim that the
Stacks torsion-coefficient result itself supplies the native assertion.

Checked the empty source (zero extension, including nonempty ambient schemes),
identity refinement (all functors compare to themselves), a proper extra component
away from X (extension by zero kills its contribution), identical compactifications,
and non-separated finite-type Y over k₀ with separated h. None is excluded by a
new hypothesis. No positivity condition on a cohomological degree is introduced;
WC^der retains its full bounded interval in arbitrary integral degrees. The single
universe u follows the actual scheme/finite-field framework; the ambient sheaf
and derived-category universes are inherited without imposing a new equality.
No STATEMENT-DISPUTED issue and no source-based statement correction were needed.

Searches (msearch.py, plus direct rg of both project roots):

- LeanFinder query: "Two compactifications give naturally isomorphic derived
  proper pushforward after extension by zero for native Weil sheaves".
  Eight hits: SheafOfModules.pushforwardNatIso, its hom version, pushforwardCongr
  and its hom/inv component formulas, TopCat.Sheaf.pushforwardForgetIso,
  Functor.sheafPushforwardContinuousIso_hom, and Condensed.lanSheafProfinite.
  None is the native derived compactification comparison.
- Loogle query: "rightDerivedNatIso". Zero hits (unknown identifier), recorded as
  returned. The generic derived natural-isomorphism construction would in any case
  require the native comparison, rather than supply it.
- Mathlib grep query:
  compactification.*(Iso|iso|Comparison)|refinement.*(Iso|iso).
  Eleven hits: affine-open-cover refinement formulas, a morphism-property use,
  Schur's comment, one-point topological compactification, and paracompact
  refinements. None concerns these native compactification models.
- LeanSearch query: "Independence of compactification for derived compact support
  direct image of sheaves". Eight hits in HasCompactSupport, condensed objects,
  continuous maps with compact support, and Scheme.Hom.support_ker. No match.
- Direct rg searches for the item id, nativeWeilCompactification,
  compactification/refinement with Iso/iso, over lean/WeilConjectures and lean/Sheaf.
  No exact statement found. Read WeilSheaf/LowerShriekFunctoriality: its proper
  compact-support comparison is only the proper case, and its open-immersion
  sheaf comparison is another specialization; neither is this statement.
  NativeAdicCompactSupportSums works with a different underlying AdicSheaf target,
  so it is not substituted for the native fixed-pair category. Read its definition.

Validation: scompile.py compiled the delivered module as sandbox and library,
with no error or warning. All variables and universes are explicitly bound;
autoImplicit is disabled in the delivered module. The only postponed declaration
is the main theorem, matching this DAG node.

## New nodes

None. The helper predicate packages clauses of this item's own statement.

## Dependency modules

None. The recorded dependency interfaces suffice without repairs.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
