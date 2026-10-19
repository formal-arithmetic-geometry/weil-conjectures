## Worker report

The module Sheaf.Paper.IndHeartIIVanishing states
AlgebraicGeometry.ProEtale.indHeartII_vanishing, with one sorry and no new definitions.
It states both continuity for every chosen filtered constructible presentation and
uniform vanishing for every ind-constructible target. The node's statement is unchanged.
The already landed sk-def-sfb-constructible is added to stmt_deps so the finite
constant-model constructibility predicate is cited explicitly.

Hypothesis and clause correspondence:

- X is a Noetherian scheme: `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`.
  No finite-type, base-field, separatedness or characteristic restriction is imposed.
- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. Its chosen algebraic closure is
  `PadicAlgCl ℓ`; `E : PadicAlgCl.FiniteIntermediateField ℓ` is exactly a finite
  intermediate extension of the p-adic field inside that closure.
- Lambda is E or Qbar: R is a RingCat-valued sheaf on the coherent profinite site,
  and `_hR` is precisely equality with `padicSubfieldCondensedRing ℓ E` or
  `padicAlgClCondensedRing ℓ`. The latter has finite-subextension-valued sections,
  not all continuous maps into the algebraic closure. The explicit commutativity
  instance records their ring-object structure, already supplied for both cases.
- Lambda_X is `condensedRingObj (coefficientHeartRingObj R) X`, the underlying
  ring object of `coefficientRing X (Mon.mk (coefficientHeartRingObj R))`.
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ...` is the category of internal
  modules over exactly this pulled-back coefficient ring.
- The source C is a `ConstantModelConstructible ... X`. This uses the existing
  finite constant scalar-model predicate; its `.obj` is its ambient module sheaf.
  On a Noetherian scheme the finite-stratification and affine-local descriptions
  agree; no arbitrary locally finitely presented coefficient matrices replace
  the constant scalar matrices.
- The bound is `(d : ℤ) (_hd : 0 ≤ d)`. `_hbound` ranges over every constructible
  target N and every integer r strictly above d, asserting `Subsingleton` of
  `((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
    ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦r⟧)`.
  This is the exact supplied uniform bound, rather than a stronger bound on
  arbitrary sheaves or an assertion that such a bound exists for all Noetherian X.
- The first conjunct quantifies over every `I : Type (u + 1)` with `SmallCategory I`
  and `IsFiltered I`, every ambient module diagram D, and its pointwise
  constructibility condition. This is the coefficient universe used by the
  continuity dependency and by all sibling ind-constructible statements.
- `c : Cocone D` with `IsColimit c` supplies B = c.pt and the chosen colimit arrows
  in the module category. Every such presentation is allowed, not just one choice.
- Every `q : ℤ` is included. Applying degree-zero embedding, shift q, and the
  additive coyoneda functor of C[0] gives the Ext diagram as an AddCommGrpCat-valued
  functor. `colimit.desc _ (...mapCocone c)` is the canonical additive comparison:
  on each stage it sends f to f followed by the shifted degree-zero image of c.ι.
  `IsIso` states precisely that this natural map is an isomorphism of abelian groups.
- The second conjunct ranges independently over every ambient B satisfying
  `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible ... X) B`.
  Mathlib defines this as existence of a small filtered ColimitPresentation with
  constructible stages in the ambient category. For every integer q with d < q,
  it asserts `Subsingleton` of the same derived Hom. Because these Hom types are
  additive groups, Subsingleton means that the group is zero. This includes all
  ind-constructible B, independently of a presentation chosen in the first conjunct.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian;
  Mathlib.Topology.Defs.Filter: CompactSpace.
- Sheaf.Topology.ProfiniteCondensedRing reexports the continuous/adically defined
  coefficients. WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic:
  Profinite.padicSubfieldCondensedRing, Profinite.padicAlgClCondensedRing;
  WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension:
  PadicAlgCl.FiniteIntermediateField.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  AlgebraicGeometry.ProEtale.coefficientRing and condensedRingObj.
  Sheaf.Paper.CoefficientHeartCommonStratification: coefficientHeartRingObj.
- Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod and its action-compatible
  morphisms. Mathlib.Algebra.Homology.DerivedCategory.Basic:
  DerivedCategory and DerivedCategory.singleFunctor; the latter is the localization
  of a degree-zero complex.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  Scheme.FiniteLocallyClosedStratification, and the existing constructible refinement
  Scheme.Stratification used by IsFiniteConstantStratified.
- Sheaf.Paper.CondensedConstantConstructibility: HasFiniteConstantLocalModel,
  IsFiniteConstantStratified, IsConstantModelConstructible, ConstantModelConstructible.
  Sheaf.AlgebraicGeometry.FiniteConstantLocalModel:
  finiteConstantLocalModel_iff_exists_cover gives exactly the scalar-extension
  description of the same existing local-model predicate.
- Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic: Abelian.Ext and
  Abelian.Ext.homAddEquiv identify the nonnegative convention with the displayed
  derived Hom. Integer degrees are written directly using this Hom, as the item
  explicitly requires; no natural-number-only Ext convention drops negative q.
- Sheaf.Paper.UniformConstructibleExt: uniformConstructibleExt records the intended
  bound property. Its existence theorem has the standing finite-field setting;
  this item assumes the bound, so those hypotheses are not imported into its type.
- Sheaf.Paper.ConstructibleExtContinuity: constructible_sheaf_ext_continuity states
  exactly the canonical comparison used by the first conjunct, with all module
  targets. Its proof is the sole non-elementary proof dependency of this item.
- Mathlib.CategoryTheory.ObjectProperty.Ind: ObjectProperty.ind, the existing
  generic ambient filtered-colimit property. No second IndCons definition is needed.

Edge cases checked before writing: the empty scheme, zero source or target,
zero constructible diagram and d = 0 cause no excluded cases. Filtered categories
are nonempty by their definition, so an empty indexing category is correctly
excluded. Constant one-object presentations cover constructible targets. Negative
q and q = 0 occur in the continuity conjunct; the vanishing clause is strictly
q > d, so it makes no false degree-zero claim. Every allowed presentation is
quantified, including non-poset categories and all their morphisms. The scheme
universe remains arbitrary; site objects and morphisms retain their separate
sizes. No equality of those universes is added. The finite extension may be the
base p-adic field itself, and both coefficient disjuncts remain present.

Searches made, 2026-10-18:

- msearch.py leanfinder, query "Ext from constructible sheaves commutes with filtered
  colimits and vanishes above a uniform bound for ind constructible targets": eight
  hits, including Condensed.instAB5CondensedMod, Grothendieck HasExt and injective
  dimension vanishing; none is this constructible-source statement.
- msearch.py loogle, query `"Ext", "colimit"`: twelve substring matches such as
  IsColimit.extendIso and colimit.hom_ext, no derived Ext continuity theorem.
- msearch.py grep, query `Ext.*filtered.*colimit|filtered.*colimit.*Ext`: two unrelated
  LocallyPresentable structure matches, no theorem for these coefficients.
- msearch.py leansearch, query "Ext out of a constructible sheaf commutes with filtered
  colimits and vanishes uniformly on ind constructible targets": eight hits for
  filtered-colimit, sheaf and condensed-category infrastructure, none this result.
- rg over WeilConjectures and lean/Sheaf for IndConstructible, ind_constructible,
  indHeart vanishing and the item id: sibling closure, sums, triangulatedness and
  continuity statements found; no statement with this comparison and supplied bound.
  A further search for indHeartII, ind_heart_ii, constructible_ext_continuity and
  Ext vanishing also checked dag/lean_names_upstream.json. The sibling
  det_ind_heart_ii_sums concerns sums, not filtered targets or this uniform bound.

No disputed statement or dependency repair is needed. Every imported project
notion uses its existing declaration. All proof steps remain in the theorem's
docstring and the sole proof is sorry. Compilation uses only scompile.py.

The first compile identified a private-import visibility error for coefficientHeartRingObj;
publicly importing its existing CoefficientHeartCommonStratification module fixes that
without changing the theorem type or adding a conversion definition.

Validation: scompile.py passed the sandbox check in 8.9 seconds and the module-path
check in 29.1 seconds, without errors or warnings. No global build was run.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
