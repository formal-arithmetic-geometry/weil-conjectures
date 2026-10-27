## Worker report

The module `Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison` states
`CategoryTheory.injective_finite_total_derived_comparison`, with one `sorry` and no other
postponed proofs. Its auxiliary structure packages precisely the node's comparison clauses;
the four triple-total helpers and the unit helper are real constructions belonging to this
comparison, not independent missing notions. The item changes only in `lean`.

I read the complete item and its ten proof steps, every statement dependency and its recorded
Lean/Mathlib signatures, Stacks `derived.tex` labels `lemma-two-ss-complex-functor` (015J),
`lemma-bounded-below-injectives-K-injective` (070J), and `lemma-injective-acyclic` (05TH).
I also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). The source's equality Tot(F(I)) = F(Tot(I)) is expressed as a chain
isomorphism normalized on every finite-diagonal inclusion. The ten proof steps, including
all three generic tool uses, are transcribed in the theorem docstring.

Hypotheses and clauses, in node order:

| Node text | Lean rendering |
| --- | --- |
| Grothendieck abelian A, B | Explicit independent object/morphism universes, `[Abelian C]`, `[Abelian D]`, `[IsGrothendieckAbelian.{v} C]`, `[IsGrothendieckAbelian.{v'} D]`. |
| F left exact and additive | `(F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]`. |
| Ordinary unbounded derived categories, Q, K-injective RF | Independent `[HasDerivedCategory.{w} C]`, `[HasDerivedCategory.{w'} D]`; `nonnegativeComplexLocalization`; recorded `F.rightDerivedFunctorOfQuasiIsoResolutions`. The theorem supplies its resolution-existence proof from `kInjectiveResolutionFunctor`, `toKInjectiveResolution`, and `monoQuasiIso_toKInjectiveResolution_app`. No resolution hypothesis is added to the theorem. |
| Delta, all its ordered objects and order-preserving arrows | `SimplexCategory`; `CosimplicialObject` is the strict functor category, and its morphisms are natural transformations for every simplex arrow. |
| Strict nonnegative cosimplicial complexes | `CosimplicialObject (CochainComplex C ℕ)`. Extension by `ComplexShape.embeddingUpNat` includes all zero terms in negative integer degrees. |
| T(C)^r finite sum n+q=r; delta+(-1)^n d | Existing `nonnegativeCosimplicialTotal`, the composite of `alternatingCofaceMapComplex` and `HomologicalComplex₂.totalFunctor`. The published up-N tensor sign is `(-1)^n`. |
| Natural chain isomorphism beta for every J | `InjectiveFiniteTotalDerivedComparison.beta`, quantified over every strict J before any injectivity hypothesis. |
| beta F(iota)=iota', characterized by this | `beta_summand`, using the actual `HomologicalComplex₂.ιTotal`; `beta_unique` states uniqueness among chain isomorphisms with this equation. |
| T(Fg) beta = beta F(Tg) | `beta_natural` is the same equation in Lean composition order, with `Functor.whiskerRight` for Fg. |
| Every J_n^q injective | The explicit condition `∀ (n : SimplexCategory) (q : ℕ), Injective ((J.obj n).X q)` precedes each affected conclusion. |
| u strict and columnwise quasi-isomorphism | `(u : K ⟶ J)` and `∀ n : SimplexCategory, QuasiIso (u.app n)`. No assumption that F(u) is a quasi-isomorphism. |
| T(u) quasi-isomorphism | `total_quasiIso` under the stated column and injectivity assumptions. |
| All terms of T(J) injective | `total_injective`, for every integer r after extension by zero, including negative r. |
| T(J) and each J_n K-injective | `total_kInjective`, `column_kInjective`, using the recorded `CochainComplex.IsKInjective`. |
| rho inverse derived unit on bounded below injectives | `injectiveFiniteTotalUnit` is the recorded unit with the canonical quotient/Q and extension/F transports. `unit_isIso` states its invertibility. Its inverse is exactly rho. |
| Whole derived isomorphism chi = Q(beta) rho RF(QT(u)) | `derived` supplies an actual `Iso` whose hom satisfies `chi.hom ≫ Q(beta.inv) ≫ eta = RF(QT(u))`. Invertibility of eta and beta makes this exactly the displayed formula, in Lean order `RF(QT(u)) ≫ rho ≫ Q(beta)`. It is not a cohomology-only statement. |
| Column c = rho RF(Qu_n), commuting with all operators | The same `derived` field supplies the natural isomorphism `c : K ⋙ Q ⋙ RF ≅ J ⋙ F_N ⋙ Q`, normalized at every simplex n by `c.hom.app n ≫ eta_(J_n) = RF(Qu_n)`. Its naturality is for every arrow of Delta, including all cofaces and codegeneracies. |
| Normalization uniquely specifies chi | The `∀ e, ... → e = chi` conjunct of `derived` states precisely uniqueness under that normalization equation. |
| J_n first-quadrant q,s total, all operators bidegree-preserving and commuting | `X : CosimplicialObject (HomologicalComplex₂ C (.up ℕ) (.up ℕ))`: each arrow is a double chain map, and its inner total is the J_n in the clause. No extra injectivity is required for this algebraic reassociation. |
| Finite triples n+q+s=r; common differential delta+(-1)^n d_q+(-1)^(n+q) d_s | `finiteTripleTotalRight` first totals q,s and then n; `finiteTripleTotalLeft` first totals n,q in the category of s-complexes and then with s. All indices are natural. Each component index is at most r, so only finitely many triples occur. Both signs follow from the existing total-complex construction; negative-degree totals are the zero extension. |
| Canonical reassociation | `reassociation` provides aC and aD and fixes each on every triple inclusion by `finiteTripleInclusionRight ≫ a = finiteTripleInclusionLeft`. Thus the rearrangement is identity on original summands, without any arbitrary chain identification. |
| beta respects reassociation | `reassociation` also supplies the natural inner finite-biproduct comparison b and the other-grouping comparison bL, each fixed on original summands, and states the commuting square `F(aC) ≫ bL = beta ≫ T(b) ≫ aD`. |

Dependency declarations actually used:

- `def-sp-double-complex-total`: `WeilConjectures.CategoryTheory.DoubleComplexTotal`, with
  `HomologicalComplex₂`, `total`, `totalFunctor`, `ιTotal`; finite natural-indexed totals
  and their sign instances from `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`
  and `ComplexShapeSigns`. These are used directly, not copied.
- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` (the theorem concerns injective
  terms; no separate injective-resolution object is needed).
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`; `PreservesFiniteLimits`,
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`. The ordinary object-level
  `Functor.rightDerived` is not substituted for the whole derived functor.
- `sk-def-sfb-derived-categories` and `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `rightDerivedFunctorOfQuasiIsoResolutions` and its `Unit`; Mathlib `DerivedCategory.Q`,
  `quotientCompQhIso` and `CochainComplex.IsKInjective`. The existing Grothendieck
  K-injective construction supplies the prerequisite automatically.
- Already defined convenience constructions `CategoryTheory.nonnegativeCosimplicialTotal`
  and `nonnegativeComplexLocalization` are reused from
  `Sheaf.CategoryTheory.NonnegativeDerivedTotalization`. Its derived comparison theorem
  and comparison structure are not used. These merely name the alternating-coface,
  finite-total and extension/localization constructions already in the statement dependencies.
- Proof imports are the recorded `WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison`,
  `Sheaf.CategoryTheory.KInjectiveComputes`, and
  `Sheaf.CategoryTheory.AdditiveDerivedPlusUnitNormalization`. Grothendieck enough-injectives
  and the other proof-dependency definitions are publicly available through the statement
  imports. The maintainer should omit the reverse proof import from
  `NonnegativeDerivedTotalization` to this file, per stages/2-statements.md section 3 rule 7:
  it would create an import cycle. This file uses only that module's concrete construction
  definitions and does not depend mathematically on the parent theorem.

Edge cases checked before and during writing: the zero diagram; F the identity; u the identity;
negative integer total degrees (empty sums, zero extension); degrees 0, 1 and 2; and triple
indices with n=0, q=0 or s=0. At r=0 the only triple is (0,0,0), every sign is +1,
and both reassociation maps are fixed by the sole summand. At r=1 the three summands
match with identity maps and the same signs. No empty simplex object is introduced: Delta
has precisely the finite nonempty ordered sets as intended. No exactness, injective
preservation, or F(u) quasi-isomorphism is assumed. Universes for the two categories and
their localizations are explicitly independent.

Searches actually run (through the prescribed msearch wrapper where indicated):

- LeanFinder: `An additive functor commutes with finite diagonal totalization of cosimplicial nonnegative complexes naturally and the total of injectives computes its right derived image`.
  Eight hits concerned object-level injective resolutions, derived single functors, and
  Dold-Kan. None states the normalized finite-total derived comparison and reassociation.
- Loogle: `"total", "mapHomologicalComplex"`: zero hits.
- Mathlib grep: `cosimplicial|mapTotal|total.*[Kk]Injective|[Kk]Injective.*total`,
  subdirectory `Algebra/Homology`: zero hits.
- LeanSearch: `Additive functor commutes with total complex finite biproducts and comparison natural in cosimplicial complexes`.
  Eight hits, including `preservesFiniteBiproductsOfAdditive`, finite-(co)product
  preservation, `map_homogical_complex_additive`, `Mat_.additiveObjIsoBiproduct`,
  `map₂CochainComplex`, and `HomologicalComplex₂.totalFunctor`. These supply ingredients,
  not the theorem.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for cosimplicial totalization,
  finite-total and reassociation terms found the existing construction wrappers in
  `NonnegativeDerivedTotalization` and the narrower double-cosimplicial shuffle module.
  The former is reused; the latter concerns shuffle equivalences rather than this theorem.
- Direct rg of both libraries and `dag/lean_names_upstream.json` for every proposed new
  declaration name found no collision; rg of upstream for this blueprint id found none.

No statement correction or disputed mathematical assertion is needed. No dependency node
or new definition node is delivered. Compilation and delivery validation are recorded below.

## Second reading by Q130

I reread the item and the complete file in a separate pass. The dispatcher explicitly forbids
starting another agent, so this is a self-review, not a claim of an independent agent review;
the maintainer's independent review remains necessary.

The pass matched both category hypotheses, left exactness and additivity, the strict Delta
category, all finite-total and beta clauses, the injective/columnwise-quasi-isomorphism
hypotheses, both K-injectivity conclusions, the whole-object chi isomorphism, its unique
unit normalization, naturality of c for all simplex arrows, and the triple reassociation
square. I added an explicit `beta_unique` field so that "characterized" is asserted rather
than only informally explained. I restricted the total-quasi-isomorphism field to the
node's injective J setting. I removed the auxiliary existence proof h as a theorem
hypothesis: the theorem now instantiates it from the existing Grothendieck K-injective
resolution functor. The auxiliary structure remains parameterized by h solely to name
the recorded derived pair. Both triple inclusions use full `HomologicalComplex₂.ιTotal`
names, and K-injectivity uses `CochainComplex.IsKInjective`, resolving the first compiler's
alias namespace lookup errors. I checked the directions of the normalization equations:
chi has source RF(QT(K)), and composing with Q(beta)^(-1) then eta gives RF(QT(u));
the column equation has precisely the analogous type. The last square has source
F(T_n(T_qs(X))) and target T_nq,s(FX) on both sides. Neither map is arbitrary because
all its original summand components are specified. No source/DAG field was changed.

Validation: prescribed `scompile.py` passed for the final file in both sandbox-module
and actual library-module modes with no warnings or errors. The `deliver2.py --no-push`
dry run passed server preflight and compilation, reporting `OK (dry run)` at
`581782f93e0`. A final sandbox-only consistency check confirmed the recorded theorem
signature is verbatim, every Lean line is at most 100 characters, and exactly one `sorry`
remains, in the item's named theorem.
