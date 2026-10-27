## Worker report

The module `Sheaf.Algebra.Homology.BoundedInjectiveRHomAmplitude` states
`CategoryTheory.boundedInjective_rhom_amplitude`. Its only proof is `sorry`;
there are no new definitions or auxiliary postponed theorems. The declaration's
docstring gives all five steps of the DAG proof. The mathematical statement is
unchanged. The only additional statement dependency is the already landed
`def-sc-module-total-hom-complex`, the ordinary-module Hom complex needed to
retain the coefficient action and the exact differential of def-pur-hom-complex.

Hypothesis and clause correspondence:

- A commutative ring: `(R : Type u) [CommRing R]`. All module objects, complexes,
  derived objects, Hom complexes, and cohomology retain this same ring and the
  chosen module universe. No Noetherianity, finite generation, or nonzero-ring
  hypothesis appears.
- Fixed integers a <= b: `(a b : ℤ) (hab : a ≤ b)`. These precede the universal
  quantifiers over K and c, so neither bound depends on either input.
- A cochain complex J of injective R-modules: `J : CochainComplex
  (ModuleCat.{u} R) ℤ` and `hinj : ∀ i : ℤ, Injective (J.X i)`.
- Vanishing below a and above b: `hlo : ∀ i, i < a → IsZero (J.X i)` and
  `hhi : ∀ i, b < i → IsZero (J.X i)`. Zero means categorical zero of a
  module object, not equality with a particular chosen zero module.
- L and its given representative: `L : DerivedCategory (ModuleCat.{u} R)` and
  `eJ : DerivedCategory.Q.obj J ≅ L`.
- Every K and every integer c: the conclusion begins `∀ (K : DerivedCategory
  (ModuleCat.{u} R)) (c : ℤ)`. Its two implications are joined by `∧`.
- First hypothesis: `∀ i, c < i → IsZero ((DerivedCategory.homologyFunctor
  (ModuleCat.{u} R) i).obj K)` is precisely vanishing of H^i(K) for i > c.
- First representative: `∃ P : CochainComplex (ModuleCat.{u} R) ℤ`, with
  `∀ p, c < p → IsZero (P.X p)` and
  `Nonempty (DerivedCategory.Q.obj P ≅ K)`. This is strict term support and
  an isomorphism in D(R), not just cohomological support.
- First comparison: `Nonempty (DerivedCategory.Q.obj
  (CochainComplex.moduleHomComplex P J) ≅
  (ordinaryModuleDerivedInternalHom R).obj (op K, L))`. Both endpoints are
  derived R-module objects. The node asks for existence of an isomorphism,
  with no additional naturality condition.
- First termwise bound: `∀ n, n < a - c → IsZero
  ((CochainComplex.moduleHomComplex P J).X n)`.
- First cohomological bound: `∀ n, n < a - c → IsZero
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
  ((ordinaryModuleDerivedInternalHom R).obj (op K, L)))`. It is conjoined
  outside the representative existential, under the same implication.
- Second hypothesis: `∀ i, i < c → IsZero ((DerivedCategory.homologyFunctor
  (ModuleCat.{u} R) i).obj K)` is vanishing below c.
- Second representative: `∃ Q : CochainComplex (ModuleCat.{u} R) ℤ`, with
  `∀ p, p < c → IsZero (Q.X p)` and `Nonempty (DerivedCategory.Q.obj Q ≅ K)`.
- Second comparison: the same derived-module isomorphism with Q replacing P.
- Second termwise bound: `∀ n, b - c < n → IsZero
  ((CochainComplex.moduleHomComplex Q J).X n)`.
- Second cohomological bound: the same homology-functor expression with
  the strict inequality `b - c < n`.

Declarations reused, with full signatures/docstrings read in their sources:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  The additional resolution declaration in its node record was also read in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; it is unnecessary
  to the signature because J itself is supplied.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`. This recorded interface
  for def-pur-derived-internal-hom already exposes the ordinary-module
  presentation of the K-injective-derived internal Hom; it publicly retains
  the generic ringed-site definitions. It is the existing derived closed
  internal Hom, not an arbitrary selected bifunctor.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  the recorded sheaf Hom complex, publicly imported; its ordinary-module
  counterpart is the existing `CochainComplex.moduleHomComplex` in
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`, recorded by
  def-sc-module-total-hom-complex. Its terms are Mathlib HomComplex.Cochain
  and its differential is HomComplex.δ_hom, with the required sign
  d_J f - (-1)^n f d_P. The different differential of the upstream
  CochainComplex.internalHomObj is not silently substituted.

Already stated proof dependencies are imported without `public`:
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
(`CochainComplex.isKInjective_of_injective`, `CochainComplex.IsKInjective`),
`Mathlib.Algebra.Homology.Embedding.CochainComplex`
(`CochainComplex.quasiIsoAt_ιTruncLE`, `truncLE`, `truncGE`),
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
(the recorded module of def-kun-truncations), and
`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
(`CategoryTheory.quasiIso_homComplex_map`). The derived-Hom and Hom-complex
proof dependencies are already public statement imports.

Edge cases checked before writing: the zero ring, J = 0, K = 0, a = b,
and arbitrary positive/zero/negative c are included. No terms are required
nonzero at either endpoint. The strict inequalities deliberately leave
n = a-c and n = b-c unrestricted; for a source concentrated at c and a target
concentrated at a or b, these endpoints may indeed be nonzero. If both source
hypotheses hold, the conjunction supplies each model separately, as the node
requires. The product calculation works without boundedness of K or any
finiteness of its terms. The ordinary module universe follows the existing
recorded RHom interface; no equality between site universes was introduced.

Searches for an existing statement and notions:

- msearch.py leanfinder: "Derived Hom into a bounded injective target has lower
  bound a minus c for source bounded above c and upper bound b minus c for
  source bounded below c" returned eight unrelated analytic bounds (including
  GromovHausdorff.HD_below_aux1/2); no match.
- msearch.py loogle: "CochainComplex.isKInjective_of_injective" returned that
  exact K-injectivity criterion, not the amplitude theorem.
- msearch.py grep: "internalHom|HomComplex" under Algebra/Homology/Monoidal
  returned no hits. Broader grep "isKInjective_of_injective|exists_iso_Q_obj_of_isLE|
  exists_iso_Q_obj_of_isGE|HomComplex" under Algebra/Homology returned 25 hits,
  including HomComplex, KInjective and their component APIs; no exact statement.
- msearch.py leansearch: "Derived internal Hom of complexes of modules into a
  bounded injective complex has bounded cohomology" returned eight hits:
  rightDerivedToHomotopyCategory, injective-resolution/cohomology declarations,
  hasExt_of_enoughInjectives, single-injective vanishing, and bounded strict
  representatives. None combines both requested bounds and both Hom models.
- rg searches in WeilConjectures and lean/Sheaf for the item id and
  boundedInjective_rhom_amplitude found no existing theorem. Searches for
  HomComplex/moduleHomComplex/ordinaryModuleDerivedInternalHom found the
  existing module Hom and ordinary derived Hom interfaces above. The DAG
  search for moduleHomComplex found def-sc-module-total-hom-complex; it is
  reused by adding its id to stmt_deps, as permitted for landed nodes.
- Read Stacks more-algebra.tex definition-injective-dimension and dualizing.tex
  lemma-dualizing. The former explicitly defines the bounded injective support;
  the latter supplies the boundedness motivation. The elementary degree
  argument of this node needs neither the Noetherianity nor coherence of the
  stronger dualizing-complex theorem.

No statement dispute or correction. No new nodes or dependency repairs.
Server validation: scompile.py compiled the sandbox and its library-module form
cleanly, in 1.7 seconds each, within the prescribed 60-second limit.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
