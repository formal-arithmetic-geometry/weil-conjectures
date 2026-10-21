## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFieldProEtaleDirectImage` states
`AlgebraicGeometry.Scheme.finiteField_proEtale_directImage_bounded_constructible`.
Its only declaration is the item's theorem, with proof `sorry`. No new definition,
dependency module, or statement correction is needed. The node copy changes only `lean`.

I read the item, all nine statement dependencies and their recorded declarations and
docstrings, the stage-2 brief and stage document, delivery-errors H, the framework note,
and the compact-object example (its old Sheaf module is withdrawn; the current upstream
module was read instead). The mathematical source is the locally available
Bhatt--Scholze PDF, Lemmas 5.4.3 and 6.7.2 and Theorem 6.7.1, read with `pdftotext`.
The seven-step node proof is included in the theorem docstring. In particular the
arbitrary-field, non-separated etale finiteness input is the existing
`thm-dg-finite-type-constructibility`; the pro-etale comparison is used only on bounded
below input, where Lemma 5.4.3 applies.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Prime ell | `(ell : ℕ)` and `hell : ell.Prime`. |
| Field k of characteristic p > 0 | `(k : Type u) [Field k] [CharP k p]` and `hp : 0 < p`. The field condition already forces a positive characteristic to be prime. |
| p different from ell | `hne : p ≠ ell`. |
| A finite field of characteristic ell | `(A : Type u) [Field A] [Finite A] [CharP A ell]`. No chosen cardinality or prime-field restriction. |
| T and V finite-type k-schemes | `T V : Scheme.{u}`, structure morphisms `aT`, `aV` to `Spec (.of k)`, with `LocallyOfFiniteType` and `QuasiCompact` instances for each. |
| f a finite-type k-morphism | `f : T ⟶ V`, `hf : f ≫ aV = aT`, and `[LocallyOfFiniteType f] [QuasiCompact f]`. These are exactly the recorded finite-type convention. |
| Ordinary uncompleted derived category | `K : proEtaleDerivedCategory T A`, transparently the standard localization `DerivedCategory` of all sheaves of modules over the constant ring. No completion, condensed coefficients, Tor-amplitude, or etale-origin condition is imposed. |
| Input cohomology vanishes outside a finite interval | `hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (...)`. Cohomology is `DerivedCategory.homologyFunctor`. |
| Input constructible cohomology | `hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf T A (...)`. This recorded intrinsic predicate uses an actual finite constructible locally closed stratification, canonical module inverse image to each stratum, local constancy and finite geometric module stalks. Over the finite field A, these are exactly finite-dimensional stalks and local constant models. |
| Ordinary total right derived module direct image | `(proEtaleConstantModuleDirectImage f A).rightDerivedFunctorOfQuasiIsoResolutions (...)`. The supplied proof term only forgets the monomorphism from the already available `Abelian.HasKInjectiveResolutions.exists_isKInjective`; it adds no resolution assumption. The functor and unit are the recorded universal construction. Its `rightDerivedFunctorOfQuasiIsoResolutionsObjIso` computes the value as direct image of a K-injective resolution. |
| Output belongs to B_A(V) | The conclusion applies a displayed lambda predicate to precisely that derived value: an existential finite cohomology interval, conjoined with `∀ q, IsConstructibleProEtaleModuleSheaf V A (...)`. The lambda beta-reduces directly; there is no hidden `let`, copied category, or private bounded-constructibility definition. |
| No finiteness, perfection, or separable closedness assumption on k | The complete list of field assumptions is `[Field k] [CharP k p]` and positive p different from ell. No separatedness assumption is imposed on f or the structure morphisms either. |

Recorded dependency declarations used:

- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, through `proEtaleConstantRing` in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. The coefficients are the canonical
  constant ring sheaf of `ULift A` in the module universe.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, used by the existing `proEtaleRingModules`.
  This is Mathlib `SheafOfModules`, with its inherited abelian structure.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory.standard`; the existing `proEtaleDerivedCategory` uses them.
- `def-weil-proetale-constructible-sheaf`: `Sheaf.Paper.ProEtaleConstructibleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and `QuasiCompact` from its recorded
  quasi-compactness dependency.
- `def-weil-proetale-module-direct-image`:
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage`. This is intrinsic
  sectionwise direct image with restriction of scalars along the canonical constant-section
  ring map, for arbitrary commutative rings. Its additive instance is imported from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`. The exact recorded
  declaration is applied in the conclusion, rather than replacing it by a different
  chosen derived functor. The required K-injective instance comes from the existing
  `proEtaleRingModules_hasKInjectiveResolutions` in `Sheaf.AlgebraicGeometry.ProEtaleOperations`.

Every recorded proof-dependency module is imported without `public` (the generic
right-derived-functor module, which is also a statement dependency, is public).
Mathlib proof leaves are included through Noetherian, QuasiSeparated,
GrothendieckCategory.EnoughInjectives and DerivabilityStructureInjectives.
The original small pro-etale sites retain object universe u+1 and morphism universe u;
module values have universe u+1. No equality of site object and morphism universes
is introduced.

Edge cases checked before writing:

- The empty scheme is allowed: the recorded stratification definition permits empty
  stratum domains, so the positive number of strata does not impose nonemptiness.
- The zero complex is allowed; it satisfies the boundedness formulation with [0,0].
- Bounds are arbitrary integers, including negative degrees, and may coincide. An empty
  cohomological support is allowed. No uniform bound independent of K is asserted.
- Arbitrarily large finite extensions of the prime coefficient field are allowed.
  ell = p is excluded exactly as required; ell = 2 is allowed; k is arbitrary in the
  specified positive characteristic, including imperfect and non-separably-closed fields.
- The identity, empty-source maps and non-separated finite-type morphisms are included.
- The output has both clauses. Finite cohomological support alone would not state this item.

Searches made (all for this item, 2026-10-21):

- `msearch.py ... leanfinder "Pro etale derived direct image preserves bounded constructible finite field coefficient complexes for finite type morphisms over an arbitrary field"`:
  eight hits on etale morphisms and constructible subsets, no matching theorem.
- `msearch.py ... loogle '"constructible", "rightDerived"'`: zero hits.
- `msearch.py ... grep '(pro[Ee]tale|proetale|[Cc]onstructible).*([Dd]erived|[Dd]irect[Ii]mage)'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Derived direct image preserves bounded constructible finite field coefficient sheaves on pro etale sites"`:
  eight sheaf-pullback/sheafification exactness hits, no finiteness theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id, intrinsic
  constructibility, `proEtaleConstantModuleDirectImage`, and finite-type constructible
  direct-image names, together with `grep -rn` of the item id in `lean/WeilConjectures`:
  no existing statement of this item. The ordinary etale theorem is in
  `FiniteTypeDirectImageConstructibility`; existing pro-etale functor and constructibility
  definitions are reused. Integral/reduction and separated-setting theorems found by the
  search do not state this arbitrary-field finite-coefficient result.
- Exact declaration-name `rg` over Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`:
  no clash for `finiteField_proEtale_directImage_bounded_constructible`.

No statement dispute or node fault was found. The first compiler run identified one
extra closing parenthesis in the resolution witness; it was removed. The final
`scompile.py Q21 lem-sfb-finite-field-proetale-direct-image <module>` passed in both
sandbox and library-name modes, in 3.9 s and 4.1 s, without errors or warnings.

## Second reading by Q21

Author self-check, under the dispatcher's direct-delivery instructions; the maintainer
performs the independent review. I reopened the node and the completed module and checked
every row above against the signature. Both characteristic instances and positive p
are present; the coefficient is a finite field rather than an arbitrary finite ring;
both structure maps and f have the required finite-type conditions; hf says f is over k.
The input has bounded and intrinsically constructible cohomology, and the displayed
conclusion asserts these same two properties on V for the recorded universal derived
functor applied to the recorded sectionwise module direct image. The nested existential
elimination only discards `Mono s`, retaining `I.IsKInjective` and `QuasiIso s`, so it is
not a new assumption or an arbitrary map. The explicit lambda is beta-reducible and
introduces no different B_A. All the node's seven proof steps, including the uniqueness
of module inverse images and the D-plus/full-derived comparison, appear in the docstring.
The parenthesis defect found by compilation is corrected. No mathematical mismatch,
missing notion or dependency-interface repair was found.
