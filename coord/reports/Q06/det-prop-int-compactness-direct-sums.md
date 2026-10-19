## Worker report

The module `Sheaf.Paper.IntegralProperDirectSums` states
`AlgebraicGeometry.ProEtale.integralProperDirectSums`, with proof `sorry`.
Its helper `IntegralProperDirectImageAssertions` expands precisely the three
conclusions; it has real Prop-valued data and is part of this node's statement.
No new DAG nodes, dependency repairs, or statement corrections are needed.
The theorem docstring contains the eleven-step proof plan of the DAG, including
the termwise-product/strict-tower bridge inserted by the stage-1 reviewer.

### Hypotheses and objects

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite extension E of Q_ell: `E : PadicAlgCl.FiniteIntermediateField ℓ`, the
  finite-subextension presentation used in the standing setting and integral
  compactness dependency. Every finite extension embeds in a chosen algebraic
  closure; this is the existing coefficient presentation, rather than an extra
  restriction on the extension. Its actual valuation ring is the ring underlying
  `Profinite.padicIntegersRingObj ℓ E`, with continuous-function sections. A chosen
  uniformizer does not occur in any conclusion, so no artificial uniformizer
  condition is imposed; the coefficient-extension module reexports its construction.
- Field of positive characteristic different from ell:
  `(k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)`.
- Separated finite-type k-schemes X and Y: `Scheme.{u}` with `Over (Spec (.of k))`,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` for each structural map.
- Proper k-morphism: `(p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]`.
- Nonnegative dimension bound: `(d : ℕ)`. The `hd` hypothesis takes the Krull
  dimension of the pullback over an algebraic closure of each residue field.
  This is the geometric fibre, using precisely the pullback construction of
  `Scheme.Hom.fiber`, with the residue-field point composed with its algebraic
  closure point. One algebraic closure suffices since extension of an
  algebraically closed residue field does not change the finite-type dimension.
  The comparison uses `(d : WithBot ℕ∞)`, retaining the empty-fibre value bottom.
- Coefficients are the existing condensed ring of integers, its existing
  `condensedRingObj` pullback, and Mathlib's internal `Mod` category.
- F is exactly `(CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E) p).
  rightDerivedFunctor`. This is the full module-object pushforward, including
  restriction of scalars, derived on the ordinary unbounded category. It is
  neither a completed functor nor a functor on only bounded complexes.
- Cons is `IsConstantModelConstructible` and Dbc is
  `constantModelBoundedConstructible` from the recorded constructibility node.
  IndCons is Mathlib `ObjectProperty.ind.{u+1}`, whose `ColimitPresentation`
  includes ambient colimit maps and their universal property. Dic means that
  every `DerivedCategory.homologyFunctor` object satisfies that property.
- Loc(Dbc) is the recorded `CategoryTheory.localizingClosure` applied to Dbc
  itself, with no finite-Tor-amplitude restriction. All small indices are
  `Type (u+1)` after specializing the generic assertion bundle at `v = u+1`.

### Conclusions, clause by clause

1. The first conjunct says that every `N : A` with `H₁ N` has image of its
   `DerivedCategory.singleFunctor A 0` object in `C₂`, with `.IsGE 0` and
   `.IsLE (2 * (d : ℤ) + 1)`. Thus it is bounded constructible and has precisely
   the required support bound. The second conjunct quantifies over every
   `H₁.ind N`, gives `H₂.ind` of every image cohomology object, and gives the same
   two support bounds. It includes every integer degree, including negative ones.
2. The third conjunct quantifies over all K with ind-constructible cohomology
   and every integer q. It applies `F.map`, then `homologyFunctor B q`, to
   `truncLEι q` at K and `truncGEπ (q - 2*d - 1)` at `truncLE q K`, and asserts
   `IsIso` of both maps. Their directions are exactly K <- tau_le K -> window.
   The fourth conjunct quantifies over arbitrary small families in Dic and
   supplies a colimit cofan whose image under F is a colimit. The mapped legs
   are the actual `F.map` of the source injections, so the canonical coproduct
   comparison is invertible, rather than merely an abstract endpoint isomorphism.
3. The fifth conjunct is pointwise preservation of `localizingClosure C₁` into
   `localizingClosure C₂`. The sixth supplies coproduct cofans preserved by F
   for every small family in that localizing closure. Minimality and ambient
   repleteness are those of the recorded closure definition.

### Dependency declarations read and used

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; its standing
  hypotheses are expanded as explicit binders, not replaced by a new predicate.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public imports:
  `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`. The statement needs only the ring of integers;
  the actual condensed constructor is `Profinite.padicIntegersRingObj` in upstream
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `Scheme.fromSpecResidueField`, instantiated with geometric residue-field extension.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, transparently
  the ring objects instantiated by the existing ring-of-integers constructor.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module action.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  generic unbounded derived-category convention; the specialized construction is
  upstream `CategoryTheory.Functor.rightDerivedFunctor`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `CondensedRing.derivedUpperStarLowerStarAdjunction` and the exact functor
  `(CondensedRing.lowerStar Λ p).rightDerivedFunctor` described in its docstring.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`.
- `Sheaf.Paper.IntegralConstructibleCompactness`:
  `IntegralConstructibleCompactnessAssertions`, `integralConstructibleCompactness`;
  reuse its Mathlib `ObjectProperty.ind` and cohomological expression for Dic.
- `Sheaf.Paper.LocalizingClosureExistence`: `localizingClosure_exists`, with the
  publicly imported `CategoryTheory.localizingClosure` intersection definition.
- `def-weil-size-convention` is a convention node: explicit universes and small
  filtered diagrams/cofans express it; there is no object to import or duplicate.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: the public-imported
  `DerivedCategory.TStructure.t`, its `truncLE`, `truncGE`, `truncLEι`, `truncGEπ`.
  Its primary new telescope predicate is not the truncation notion, and is not
  incorrectly used for a finite-window assertion.

Compatible available recorded proof-dependency modules are imported without `public`
(unless also used for statement data). The currently unstated integral-heart,
integral proper-base-change, and integral adic-criterion proof nodes have no
module to import. Mathlib proof leaves are imported by their recorded source
modules. The rational window and rational coproduct modules found in searches
are not proof inputs: the DAG specifies an integral proof route.

### Edge cases checked before writing

Empty indexing sets are included: a cofan on the empty family is the zero
coproduct, and its image is required to be a colimit. The same holds for the
zero object and all-zero families. No nonempty index or common boundedness
condition appears. Empty X and empty fibres retain Krull dimension bottom and
are allowed. The case d = 0 yields support [0,1] and window [q-1,q], exactly
as the node says. Negative q, q = 0, arbitrarily negative tails, unbounded
positive tails and summands without a shared lower bound are all quantified.
No finite-Tor or derived-completeness condition is placed on arbitrary K.

### Searches

- `msearch.py leanfinder`: "Proper direct image of integral pro-etale module sheaves
  preserves arbitrary direct sums of complexes with ind-constructible cohomology".
  Eight results concern light condensed modules and unrelated tensor structures;
  none states the item.
- `msearch.py loogle`: "PreservesColimit, IsIso, DerivedCategory".
  Returned zero hits, unknown identifier `PreservesColimit`.
- `msearch.py grep`: `direct.sums|PreservesCoproducts|IndCons` in CategoryTheory.
  Nine hits concern tensor distribution and additive/biproduct functors, not this item.
- `rg` over the named upstream WeilConjectures source and `lean/Sheaf`:
  `integral.*(Direct|direct|Sum)|IndCons|int-compactness-direct-sums`.
  Found rational `ProperHeartBound`, `ProperUnboundedWindow`,
  `ProperUnboundedCoproducts`; read their complete declarations. They specialize
  to E or Qbar coefficients, not the integral ring, and none bundles all three
  assertions of this node. The only literal blueprint-id reference is in the
  generic class-relative upper-bound proof dependency.
- Read the exact 51-module framework under shared `lean/WeilConjectures`, as
  required by `coord/pefw-upstream-framework.md`; the older source checkout
  does not contain all of these modules.

No STATEMENT-DISPUTED issue was found. No statement has been corrected.

### Validation

The required `scompile.py Q06 det-prop-int-compactness-direct-sums` single-file
compile passed for both the sandbox check (19.3 s) and the module-path check
(10.5 s), with no warnings or errors. `autoImplicit` is explicitly false.
Source inspection confirms one `sorry`, exactly the item theorem; the helper is
fully defined. Every line is at most 100 characters. The JSON signature is
verbatim, and the only changed node field is `lean`. The required `deliver2.py --no-push` dry run passed server preflight and compilation
(checked packet 34d5e12dfe).

The first compile diagnosed an inherited duplicate between the old pro-etale
`Derived.Comparison` and the newer `FiniteCoefficient.Derived.Comparison`.
The sole old-framework importer was the proof-only
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`; its direct import is omitted
to use the newer comparison framework already needed by
`BoundedBelowProEtaleComparison`, following the launcher's explicit duplicate-import
repair instruction. Its mathematical input remains in the proof plan;
its existing recorded declaration is not redefined.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
